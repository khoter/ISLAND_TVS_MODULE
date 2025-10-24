#include <Arduino.h>
#include <TM1637Display.h>
#include <Bounce2.h>

/* ===== Подключения =====
   TM1637 U (верхний):  CLK=18, DIO=17
   TM1637 L (нижний):   CLK=16, DIO=15
   Потенциометры: I->8, U->9, P->10  (ESP32-S3 ADC 12-bit)
   Кнопки (к GND, INPUT_PULLUP): OUT->11, UI->12, DEW->13, DEP->14, RU->21
   LED: OUT->1, UI->2, DEW->3, DEP->4, RU->36
   RGB (общий катод): R->5 (150Ω), G->6 (100Ω), B->7 (100Ω), общий -> GND
*/

// --------- TM1637 ----------
#define TMU_CLK 18
#define TMU_DIO 17
TM1637Display dispU(TMU_CLK, TMU_DIO);

#define TML_CLK 16
#define TML_DIO 15
TM1637Display dispL(TML_CLK, TML_DIO);

// --------- ADC ----------
#define POT_I 8
#define POT_U 9
#define POT_P 10

// --------- Кнопки ----------
#define BTN_OUT 11
#define BTN_UI  12
#define BTN_DEW 13
#define BTN_DEP 14
#define BTN_RU  21
Bounce bOUT, bUI, bDEW, bDEP, bRU;

// --------- LED ----------
#define LED_OUT 1
#define LED_UI  2
#define LED_DEW 3
#define LED_DEP 4
#define LED_RU  36

// --------- LED_POT ----------
#define LED_U 41
#define LED_P 42

// ===== Параметры =====
const uint32_t SELFTEST_MS  = 600;
const float    ALPHA        = 0.05f;      // EMA сглаживание АЦП
const float    MAX_I_A      = 9.99f;
const float    MAX_U_V      = 40.0f;
const float    MAX_P_W      = 800.0f;

// гистерезис индикации
const float UI_EPS_V = 0.05f;
const float II_EPS_A = 0.02f;
const int   PP_EPS_W = 2;

// RGB фазы
const uint32_t WARMUP_MS    = 10000;      // время разогрева 
const float    WHITE_AT_A   = 6.0f;       // макс управляющий ток к «белому»

// ===== TM1637 helpers =====
const uint8_t SEG_BLK = 0x00;

//      A
//     ---
//  F |   | B
//     -G-
//  E |   | C
//     ---
//      D
const uint8_t SEG_ERR1[] = {
  (uint8_t)(SEG_A | SEG_D | SEG_E | SEG_F | SEG_G), // E
  (uint8_t)(SEG_E | SEG_G),                         // r
  (uint8_t)(SEG_E | SEG_G),                         // r
  (uint8_t)(SEG_B | SEG_C)                          // 1
};

// ===== Состояния =====
enum State { ST_INIT=0, ST_READY, ST_SETUP_I, ST_SETUP_P, ST_ARMED, ST_RUN, ST_ERR1 };
State state = ST_INIT;

// Фильтры/уставки
float filtI=0, filtU=0, filtP=0;
float setI_amp=0.0f, setU_volt=0.0f, setP_watt=0.0f;

// Отображённые (для гистерезиса)
float shownU=0.0f, shownI=0.0f;
int   shownP=0;

// Тайминги
uint32_t tStart=0, depTime=0;

// Флаги перерисовки
bool forceRedraw_IU=false;

// Настройки ошибки ERR1
const float DI_DT_LIMIT_A_PER_S = 0.5f;
float    rate_lastI  = 0.0f;
uint32_t rate_lastMs = 0;
bool     errActive   = false;

// ===== Утилиты =====
static inline void setLed(uint8_t pin,bool on){ pinMode(pin,OUTPUT); digitalWrite(pin, on?HIGH:LOW); }
static inline float readADCnorm(int pin){ return analogRead(pin)/4095.0f; }
static inline float mapU(float x){ return x*MAX_U_V; }
static inline float mapP(float x){ return x*MAX_P_W; }
static inline float mapI_full(float x){ return x*MAX_I_A; }
static inline float smooth01(float t){ t = constrain(t,0.0f,1.0f); return t*t*(3.0f-2.0f*t); }
static inline uint8_t u8(int v){ if(v<0)v=0; if(v>255)v=255; return (uint8_t)v; }

// ===== RGB =====
#define RGB_R 5
#define RGB_G 6
#define RGB_B 7
#define RGB_COMMON_ANODE 0
#define RGB_GAMMA 2.2f
#define RGB_SCALE_R 1.00f
#define RGB_SCALE_G 0.60f
#define RGB_SCALE_B 0.90f

static void rgbWriteRaw(uint8_t r,uint8_t g,uint8_t b){
  auto gfix=[&](uint8_t v)->uint8_t{ float x=v/255.0f; x=powf(x,1.0f/RGB_GAMMA); return u8(lroundf(x*255.0f)); };
  uint8_t R=gfix(r), G=gfix((uint8_t)lroundf(g*RGB_SCALE_G)), B=gfix(b);
#if RGB_COMMON_ANODE
  R=255-R; G=255-G; B=255-B;
#endif
  ledcWrite(0,R); ledcWrite(1,G); ledcWrite(2,B);
}

static inline void mixRGB(uint8_t r1,uint8_t g1,uint8_t b1,
                          uint8_t r2,uint8_t g2,uint8_t b2,
                          float t, uint8_t& r,uint8_t& g,uint8_t& b){
  t = constrain(t,0.0f,1.0f);
  r = u8(lroundf(r1 + (r2 - r1)*t));
  g = u8(lroundf(g1 + (g2 - g1)*t));
  b = u8(lroundf(b1 + (b2 - b1)*t));
}

// Фаза 2: base=Ywarm → белый по току 0..6A (smoothstep + EMA).
static float ti_ema = 0.0f;
const  float TI_ALPHA = 0.12f;

static void rgbRun(uint32_t ms_since_dep, float i_amp){
  const uint8_t Rr=200, Rg=0,   Rb=0;
  const uint8_t Wr=250, Wg=100, Wb=5;

  float ti = constrain(i_amp / WHITE_AT_A, 0.1f, 1.0f);
  ti = smooth01(ti);
  ti_ema = (1.0f - TI_ALPHA)*ti_ema + TI_ALPHA*ti;

  uint8_t r,g,b; mixRGB(Rr,Rg,Rb, Wr,Wg,Wb, ti_ema, r,g,b);
  rgbWriteRaw(r,g,b);
}

// ===== Отрисовка TM1637 =====
static inline void showZerosU(){ uint8_t z[4]={dispU.encodeDigit(0),dispU.encodeDigit(0),dispU.encodeDigit(0),dispU.encodeDigit(0)}; dispU.setSegments(z); }
static inline void show3ZerosU(){ uint8_t s[4]={ SEG_BLK, dispU.encodeDigit(0), dispU.encodeDigit(0), dispU.encodeDigit(0) }; dispU.setSegments(s); }
static inline void showZerosL(){ uint8_t z[4]={dispL.encodeDigit(0),dispL.encodeDigit(0),dispL.encodeDigit(0),dispL.encodeDigit(0)}; dispL.setSegments(z); }

static inline void showERR1Both(bool on){
  if(on){ dispU.setSegments(SEG_ERR1); dispL.setSegments(SEG_ERR1); }
  else  { uint8_t z[4]={SEG_BLK,SEG_BLK,SEG_BLK,SEG_BLK}; dispU.setSegments(z); dispL.setSegments(z); }
}

// U: XX.X
static void showU(float volts){
  if(volts<0) volts=0;
  if(volts>=100.0f){
    uint8_t s[4]={SEG_BLK, dispU.encodeDigit(1),
                  (uint8_t)(dispU.encodeDigit(0) | 0x80),
                  dispU.encodeDigit(0)};
    dispU.setSegments(s); return;
  }
  int d=(int)lroundf(volts*10.0f);
  int d0=d%10; d/=10; int d1=d%10; d/=10; int d2=d%10;
  uint8_t s[4];
  s[0]=SEG_BLK;
  s[1]=dispU.encodeDigit(d2);
  s[2]=(uint8_t)(dispU.encodeDigit(d1) | 0x80);
  s[3]=dispU.encodeDigit(d0);
  dispU.setSegments(s);
}

// U: X.XX как функция I: от 0.10 до 0.40 при 0..9.99 A
static void showU_I(float amps){
  if(amps<0) amps=0; if(amps>MAX_I_A) amps=MAX_I_A;
  float minV = 0.10f, maxV = 0.40f;
  float v_f = (amps>0) ? (minV + (amps / MAX_I_A) * (maxV - minV)) : 0.0f;
  int v = (int)lroundf(v_f * 100.0f);  // 0.37 -> 37
  int d0=v%10; v/=10; int d1=v%10; v/=10; int d2=v%10;
  uint8_t s[4];
  s[0]=SEG_BLK;
  s[1]=(uint8_t)(dispU.encodeDigit(d2) | 0x80);  // целые U + точка
  s[2]=dispU.encodeDigit(d1);
  s[3]=dispU.encodeDigit(d0);
  dispU.setSegments(s);
}

// I: X.XX
static void showI(float amps){
  if(amps<0) amps=0; if(amps>MAX_I_A) amps=MAX_I_A;
  int c=(int)lroundf(amps*100.0f);  // 3.73A -> 373
  int d0=c%10; c/=10; int d1=c%10; c/=10; int d2=c%10;
  uint8_t s[4];
  s[0]=SEG_BLK;
  s[1]=(uint8_t)(dispL.encodeDigit(d2) | 0x80);  // целые А + точка
  s[2]=dispL.encodeDigit(d1);
  s[3]=dispL.encodeDigit(d0);
  dispL.setSegments(s);
}

// P: XXX
static void showP(float watts){
  int w=(int)lroundf(watts); if(w<0)w=0; if(w>999)w=999;
  int d0=w%10; w/=10; int d1=w%10; w/=10; int d2=w%10;
  uint8_t s[4];
  s[0]=SEG_BLK;
  s[1]=dispL.encodeDigit(d2);
  s[2]=dispL.encodeDigit(d1);
  s[3]=dispL.encodeDigit(d0);
  dispL.setSegments(s);
}

// ===== Кнопки =====
static inline uint8_t readButtonsMask(){
  uint8_t m=0;
  if(digitalRead(BTN_OUT)==LOW) m|=1<<0;
  if(digitalRead(BTN_UI )==LOW) m|=1<<1;
  if(digitalRead(BTN_DEW)==LOW) m|=1<<2;
  if(digitalRead(BTN_DEP)==LOW) m|=1<<3;
  if(digitalRead(BTN_RU )==LOW) m|=1<<4;
  return m;
}

// ===== SETUP =====
void setup(){
  Serial.begin(115200);

  pinMode(BTN_OUT,INPUT_PULLUP); bOUT.attach(BTN_OUT); bOUT.interval(10);
  pinMode(BTN_UI ,INPUT_PULLUP); bUI.attach(BTN_UI ); bUI.interval(10);
  pinMode(BTN_DEW,INPUT_PULLUP); bDEW.attach(BTN_DEW); bDEW.interval(10);
  pinMode(BTN_DEP,INPUT_PULLUP); bDEP.attach(BTN_DEP); bDEP.interval(10);
  pinMode(BTN_RU ,INPUT_PULLUP); bRU.attach(BTN_RU ); bRU.interval(10);

  setLed(LED_OUT,1); setLed(LED_UI,1); setLed(LED_DEW,1); setLed(LED_DEP,1); setLed(LED_RU,1);
  setLed(LED_U,1);   setLed(LED_P,1);

  ledcSetup(0,5000,8); ledcAttachPin(RGB_R,0);
  ledcSetup(1,5000,8); ledcAttachPin(RGB_G,1);
  ledcSetup(2,5000,8); ledcAttachPin(RGB_B,2);
  rgbWriteRaw(0,0,0);

  analogReadResolution(12);
  analogSetPinAttenuation(POT_I, ADC_11db);
  analogSetPinAttenuation(POT_U, ADC_11db);
  analogSetPinAttenuation(POT_P, ADC_11db);
  pinMode(POT_P, INPUT_PULLDOWN);
  pinMode(POT_I, INPUT);
  pinMode(POT_U, INPUT);

  dispU.setBrightness(7,true);
  dispL.setBrightness(7,true);

  uint8_t all8U[4]={dispU.encodeDigit(8),dispU.encodeDigit(8),dispU.encodeDigit(8),dispU.encodeDigit(8)};
  uint8_t all8L[4]={dispL.encodeDigit(8),dispL.encodeDigit(8),dispL.encodeDigit(8),dispL.encodeDigit(8)};
  dispU.setSegments(all8U); dispL.setSegments(all8L);
  delay(120);
  showZerosU(); showZerosL();

  tStart=millis();
  state = ST_READY;
}

// ===== LOOP =====
void loop(){
  bOUT.update(); bUI.update(); bDEW.update(); bDEP.update(); bRU.update();
  uint32_t now=millis();

  if(state==ST_INIT){
    if(now - tStart >= SELFTEST_MS) state=ST_READY; else return;
  }

  // фильтрация АЦП
  filtI=filtI*(1-ALPHA)+readADCnorm(POT_I)*ALPHA;
  filtU=filtU*(1-ALPHA)+readADCnorm(POT_U)*ALPHA;
  filtP=filtP*(1-ALPHA)+readADCnorm(POT_P)*ALPHA;

  // быстрые входы блокируем в RUN и в ERR1
  if(state!=ST_RUN && state!=ST_ERR1){
    if(digitalRead(BTN_OUT)==LOW && state!=ST_SETUP_I){
      setLed(LED_OUT,0);
      state=ST_SETUP_I;
      forceRedraw_IU=true; shownU=-1e9f; shownI=-1e9f;
    }
    if(digitalRead(BTN_UI)==LOW && state!=ST_SETUP_P){
      setLed(LED_UI,0);
      state=ST_SETUP_P;
      shownP=-10000;
    }
  }

  switch(state){
    case ST_READY:
      showZerosU(); showZerosL();
      break;

    case ST_SETUP_I: {
      setI_amp = constrain(roundf(mapI_full(filtI)*100.0f)/100.0f, 0.0f, MAX_I_A);
      setU_volt= constrain(mapU(filtU), 0.0f, MAX_U_V);

      if (forceRedraw_IU){
        showU(setU_volt); shownU=setU_volt;
        showI(setI_amp);  shownI=setI_amp;
        forceRedraw_IU=false;
      } else {
        if (fabsf(setU_volt - shownU) > UI_EPS_V) { shownU = setU_volt; showU(shownU); }
        if (fabsf(setI_amp - shownI) > II_EPS_A)  { shownI = setI_amp; showI(shownI); }
      }

      if (bUI.fell()){
        setLed(LED_UI,0);
        show3ZerosU(); showZerosL();        // в UI три нуля сверху
        state=ST_SETUP_P; shownP=-10000;
      }
    } break;

    case ST_SETUP_P: {
      setP_watt = constrain(mapP(filtP), 0.0f, MAX_P_W);
      show3ZerosU();                        // в UI три нуля
      int pInt = (int)lroundf(setP_watt);
      if (abs(pInt - shownP) > PP_EPS_W) { shownP = pInt; showP(shownP); }

      if(digitalRead(BTN_OUT)==HIGH && digitalRead(BTN_UI)==HIGH){
        setLed(LED_OUT,1); setLed(LED_UI,1);
        shownU=-1e9f; shownI=-1e9f;
        showU(setU_volt); showI(setI_amp);
        state=ST_ARMED;
      }
    } break;

    case ST_ARMED: {
      if (fabsf(setU_volt - shownU) > UI_EPS_V) { shownU = setU_volt; showU(shownU); }
      if (fabsf(setI_amp - shownI) > II_EPS_A)  { shownI = setI_amp; showI(shownI); }

      if(bDEP.fell()){
        setLed(LED_DEP,0); setLed(LED_U,0); setLed(LED_P,0);
        depTime=now;
        showU_I(setI_amp);                   // верхний: U от I (начало DEP)
        showI(setI_amp);                     // низ — выставленный ток
        ti_ema = 0.0f;
        rgbRun(0, setI_amp);                
        state=ST_RUN;

        // открыть трекер скорости
        rate_lastI = setI_amp;
        rate_lastMs = now;
        errActive = false;
      }
    } break;

    case ST_RUN: {
      if (digitalRead(BTN_DEP)==HIGH || bDEP.rose()){
        setLed(LED_DEP,1); setLed(LED_U,1); setLed(LED_P,1);
        rgbWriteRaw(0,0,0);
        state=ST_ARMED;
        break;
      }

      float iFull=constrain(mapI_full(filtI),0.0f,MAX_I_A);
      float iView=roundf(iFull*100.0f)/100.0f;
      if (fabsf(iView - shownI) > II_EPS_A) { shownI = iView; showI(iView); }
      showU_I(iView);                        // верхний — U от I
      rgbRun(now - depTime, iFull);

      // контроль скорости нарастания тока
      uint32_t dt_ms = now - rate_lastMs;
      if (dt_ms > 0){
        float di = fabsf(iFull - rate_lastI);
        float rate = di / (dt_ms * 0.001f);  // A/с
        if (rate > DI_DT_LIMIT_A_PER_S){
          errActive = true;
          rgbWriteRaw(0,0,0);
          setLed(LED_U,1); setLed(LED_P,1); setLed(LED_DEP,1);
          state = ST_ERR1;
          break;
        }
      }
      rate_lastI = iFull;
      rate_lastMs = now;
    } break;

    case ST_ERR1: {
      bool blinkOn = ((now / 500) % 2) == 0; // 1 Гц (500 мс вкл/выкл)
      showERR1Both(blinkOn);
      // Выход только физическим RST (перезагрузка МК)
    } break;

    default: break;
  }

  // Нули только в режиме готовности и когда отпущены все кнопки
  if (state == ST_READY && readButtonsMask() == 0) {
    showZerosU();
    showZerosL();
  }

  // Управление LED (не трогаем в аварии)
  if (state != ST_ERR1){
    setLed(LED_OUT, digitalRead(BTN_OUT)==LOW ? 0:1);
    setLed(LED_UI,  digitalRead(BTN_UI )==LOW ? 0:1);
    setLed(LED_DEW, digitalRead(BTN_DEW)==LOW ? 0:1);
    setLed(LED_DEP, digitalRead(BTN_DEP )==LOW ? 0:1);
    setLed(LED_RU,  digitalRead(BTN_RU )==LOW ? 0:1);
    setLed(LED_U,   digitalRead(BTN_DEP )==LOW ? 0:1);
    setLed(LED_P,   digitalRead(BTN_DEP )==LOW ? 0:1);
  }
}
