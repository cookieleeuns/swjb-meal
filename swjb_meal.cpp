// SwjbMeal - 수원정보과학고 급식 데스크톱 위젯 (Win32 / C++17)
#ifndef UNICODE
#define UNICODE
#endif
#ifndef _UNICODE
#define _UNICODE
#endif
#define WIN32_LEAN_AND_MEAN
#include <windows.h>
#include <windowsx.h>
#include <winhttp.h>
#include <shellapi.h>
#include <shlobj.h>
#include <objidl.h>
#include <gdiplus.h>
#include <string>
#include <vector>
#include <ctime>
#include <cstdio>
#include <cmath>

// ======================= 설정 =======================
#define HOST_W      L"swjb-h.goesw.kr"
#define PATH_W      L"/swjb-h/ad/fm/foodmenu/selectFoodMenuView.do"
#define HTTP_PORT   80
static const int  CRAWL_INTERVAL_DAYS = 3;       // 주기 크롤링(일). 시작 시엔 항상 1회 크롤링.
static int  WIN_W      = 320;                    // 창 가로폭(프리셋에 따라 변동)
static int  HEADER_H   = 36;                     // 헤더 높이(최소 모드=0)
static const int  NAV_H      = 38;               // 하단 네비 높이
static int  g_size     = 1;                       // 0=최소, 1=기본, 2=크게
static void applySizePreset(){ if(g_size==0){WIN_W=250;HEADER_H=0;} else if(g_size==2){WIN_W=430;HEADER_H=44;} else {WIN_W=320;HEADER_H=36;} }
static const int  ICON_DRAW  = 18;               // 헤더 아이콘 이미지 표시 크기(px). 원본은 36~48 권장.
static const wchar_t* FONT_DEFAULT = L"Malgun Gothic"; // 기본 폰트(config.ini FONT= 로 변경 가능)

// ======================= 색상(테마) =======================
static const BYTE WIN_ALPHA=244, TIP_ALPHA=250;
static const COLORREF C_ACCENT = RGB(0,190,255);   // #00BEFF 강조(테마 공통)
// 다크: 흑백 4단계 + 완전 화이트
static const COLORREF D_BG1=RGB(23,23,23),D_BG2=RGB(33,33,33),D_BG3=RGB(51,51,51),D_GRAY=RGB(138,138,138),D_TEXT=RGB(255,255,255);
// 라이트: 백색 4단계 + 블랙
static const COLORREF W_BG1=RGB(255,255,255),W_BG2=RGB(242,242,242),W_BG3=RGB(214,214,214),W_GRAY=RGB(110,110,110),W_TEXT=RGB(20,20,20);
// 역할별(테마에 따라 applyTheme 에서 채움)
static COLORREF COL_BG,COL_HEADER,COL_NAV,COL_NAV_LINE,COL_TITLE,COL_DATE,COL_ACCENT,COL_SUB,
                COL_ITEM,COL_ICON,COL_NAVARROW,COL_SCROLL,COL_TODAY_BG,COL_TODAY_TX,COL_TIP_BG,COL_TIP_TX,COL_WARN;
static bool g_light=false;
static void applyTheme(){ COLORREF bg1,bg2,bg3,gr,tx,white=RGB(255,255,255);
    if(g_light){bg1=W_BG1;bg2=W_BG2;bg3=W_BG3;gr=W_GRAY;tx=W_TEXT;} else {bg1=D_BG1;bg2=D_BG2;bg3=D_BG3;gr=D_GRAY;tx=D_TEXT;}
    COL_BG=bg1; COL_HEADER=bg2; COL_NAV=bg2; COL_NAV_LINE=bg3; COL_TITLE=tx; COL_DATE=tx;
    COL_ACCENT=C_ACCENT; COL_SUB=gr; COL_ITEM=tx; COL_ICON=gr; COL_NAVARROW=gr; COL_SCROLL=bg3;
    COL_TODAY_BG=C_ACCENT; COL_TODAY_TX=white; COL_TIP_BG=bg3; COL_TIP_TX=tx;
    COL_WARN = g_light?RGB(211,47,47):RGB(255,92,92); }  // 알레르기 메뉴(빨강)
// ==========================================================

static const UINT WM_APP_FETCH_DONE = WM_APP + 1;
static const UINT TRAY_MSG = WM_APP + 2;
static const UINT TIMER_ID = 1, TRAY_UID = 101;
enum { CMD_RESTORE = 2001, CMD_REFRESH, CMD_EXIT, CMD_THEME_DARK, CMD_THEME_LIGHT, CMD_STARTUP };
static const int CMD_ALG_BASE = 2100; // +1..19
static const int CMD_SIZE_BASE = 2200; // +0..2 (최소/기본/크게)

static const char* ALLERGEN[20] = {
    "", "난류","우유","메밀","땅콩","대두","밀","고등어","게","새우","돼지고기",
    "복숭아","토마토","아황산류","호두","닭고기","쇠고기","오징어","조개류(굴,전복,홍합)","잣"
};

struct Item { std::string text, allergens; unsigned mask=0; }; // mask: 알레르기 코드 비트(1<<n)
struct Meal { std::string name, kcal; std::vector<Item> items; };
struct DayMenu { std::string date, dow; std::vector<Meal> meals; };

static HWND   g_hwnd=nullptr, g_tip=nullptr;
static HFONT  g_fTitle=0,g_fSmall=0,g_fDate=0,g_fItem=0,g_fTag=0,g_fNav=0;
static bool   g_collapsed=false,g_fetching=false,g_lastOk=true,g_drag=false,g_tracking=false;
static time_t g_lastFetch=0;
static int    g_scrollY=0,g_contentH=0,g_winH=260,g_hoverIdx=-1;
static POINT  g_dragOff{};
static std::vector<DayMenu> g_week;
static std::string g_viewDate,g_fetchDate;
static std::wstring g_tipText,g_fontName;
static ULONG_PTR g_gdipTok=0;
static Gdiplus::Image *g_imgRefresh=nullptr,*g_imgMin=nullptr,*g_imgClose=nullptr;
static std::vector<BYTE> g_fontBuf; static HANDLE g_fontMem=nullptr;

static RECT g_rcRefresh{},g_rcMin{},g_rcClose{},g_rcPrev{},g_rcNext{},g_rcToday{};
struct Hit { RECT rc; std::wstring tip; };
static std::vector<Hit> g_itemHits;
static bool g_alg[20]={false}; static unsigned g_algMask=0;   // 사용자가 체크한 알레르기
static void recalcMask(){ g_algMask=0; for(int i=1;i<=19;i++) if(g_alg[i]) g_algMask|=(1u<<i); }

// ---- 유틸 ----
static std::wstring U8toW(const std::string& s){ if(s.empty())return L"";
    int n=MultiByteToWideChar(CP_UTF8,0,s.c_str(),(int)s.size(),nullptr,0);
    std::wstring w(n,0); MultiByteToWideChar(CP_UTF8,0,s.c_str(),(int)s.size(),&w[0],n); return w; }
static std::string WtoU8(const std::wstring& w){ if(w.empty())return "";
    int n=WideCharToMultiByte(CP_UTF8,0,w.c_str(),(int)w.size(),nullptr,0,0,0);
    std::string s(n,0); WideCharToMultiByte(CP_UTF8,0,w.c_str(),(int)w.size(),&s[0],n,0,0); return s; }
static std::string trim(const std::string& s){ size_t a=s.find_first_not_of(" \t\r\n"); if(a==std::string::npos)return"";
    size_t b=s.find_last_not_of(" \t\r\n"); return s.substr(a,b-a+1); }
static void replaceAll(std::string& s,const std::string& a,const std::string& b){ if(a.empty())return;
    size_t p=0; while((p=s.find(a,p))!=std::string::npos){s.replace(p,a.size(),b);p+=b.size();} }
static std::string brToNl(std::string s){ size_t p=0; while((p=s.find("<br",p))!=std::string::npos){
    size_t e=s.find('>',p); if(e==std::string::npos)break; s.replace(p,e-p+1,"\n"); p+=1;} return s; }
static std::string stripTags(const std::string& s){ std::string o; bool in=false;
    for(char c:s){ if(c=='<')in=true; else if(c=='>')in=false; else if(!in)o+=c;} return o; }
static std::string decodeEntities(std::string s){ replaceAll(s,"&lt;","<");replaceAll(s,"&gt;",">");
    replaceAll(s,"&quot;","\"");replaceAll(s,"&#39;","'");replaceAll(s,"&nbsp;"," ");replaceAll(s,"&amp;","&"); return s; }
static std::vector<std::string> split(const std::string& s,const std::string& sep){ std::vector<std::string> v;
    size_t p=0,q; while((q=s.find(sep,p))!=std::string::npos){v.push_back(s.substr(p,q-p));p=q+sep.size();} v.push_back(s.substr(p)); return v; }

static void splitAllergy(const std::string& line,std::string& text,std::string& allergens,unsigned& mask){
    std::string o; std::vector<int> codes; mask=0;
    for(size_t i=0;i<line.size();){
        if(line[i]=='('){ size_t j=line.find(')',i);
            if(j!=std::string::npos){ bool code=(j>i+1);
                for(size_t k=i+1;k<j;++k){char c=line[k]; if(!(isdigit((unsigned char)c)||c=='.'||c==' ')){code=false;break;}}
                if(code){ for(auto& t:split(line.substr(i+1,j-i-1),".")){ std::string n=trim(t);
                        if(!n.empty()){int v=atoi(n.c_str()); if(v>=1&&v<=19){codes.push_back(v); mask|=(1u<<v);}} }
                    while(!o.empty()&&o.back()==' ')o.pop_back(); i=j+1; continue; } } }
        o+=line[i++];
    }
    text=trim(o); std::string a; for(size_t k=0;k<codes.size();++k){ if(k)a+=", "; a+=ALLERGEN[codes[k]]; } allergens=a;
}

// ---- 파서 ----
static std::vector<std::pair<std::string,std::string>> headerDates(const std::string& html){
    std::vector<std::pair<std::string,std::string>> out;
    size_t ts=html.find("<thead"),te=html.find("</thead>",ts==std::string::npos?0:ts);
    std::string region=(ts!=std::string::npos&&te!=std::string::npos)?html.substr(ts,te-ts):html;
    const std::string KEY="<th scope=\"col\">"; size_t p=0;
    while((p=region.find(KEY,p))!=std::string::npos){
        size_t s=p+KEY.size(),e=region.find("</th>",s); if(e==std::string::npos)break;
        std::string inner=region.substr(s,e-s); p=e+5;
        size_t br=inner.find("<br"); if(br==std::string::npos)continue; size_t gt=inner.find('>',br);
        std::string dow=trim(stripTags(inner.substr(0,br))),date=trim(stripTags(inner.substr(gt+1)));
        if(date.find('-')!=std::string::npos) out.push_back({date,dow});
    }
    return out;
}
static std::vector<std::string> rowCells(const std::string& html,const std::string& meal){
    std::vector<std::string> cells; std::string key=">"+meal+"</th>"; size_t p=html.find(key);
    if(p==std::string::npos)return cells; size_t start=p+key.size(),rowEnd=html.find("</tr>",start);
    if(rowEnd==std::string::npos)rowEnd=html.size(); std::string region=html.substr(start,rowEnd-start); size_t q=0;
    while((q=region.find("<td",q))!=std::string::npos){ size_t gt=region.find('>',q); if(gt==std::string::npos)break;
        size_t ce=region.find("</td>",gt); if(ce==std::string::npos)break; cells.push_back(region.substr(gt+1,ce-gt-1)); q=ce+5; }
    return cells;
}
static void parseCell(const std::string& cell,std::string& kcal,std::vector<Item>& items){
    kcal.clear(); items.clear();
    size_t k=cell.find("fm_tit_p");
    if(k!=std::string::npos){ size_t gt=cell.find('>',k),e=cell.find("</p>",gt);
        if(gt!=std::string::npos&&e!=std::string::npos){ std::string t=trim(stripTags(decodeEntities(cell.substr(gt+1,e-gt-1))));
            size_t kp=t.find("Kcal"); if(kp==std::string::npos)kp=t.find("kcal"); if(kp!=std::string::npos)t=trim(t.substr(0,kp)); kcal=t; } }
    size_t m=cell.find("<p class=\"\">");
    if(m!=std::string::npos){ size_t gt=cell.find('>',m),e=cell.find("</p>",gt);
        if(gt!=std::string::npos&&e!=std::string::npos){ std::string body=decodeEntities(stripTags(brToNl(cell.substr(gt+1,e-gt-1))));
            size_t pos=0,nl; do{ nl=body.find('\n',pos);
                std::string line=trim(body.substr(pos,nl==std::string::npos?std::string::npos:nl-pos));
                if(!line.empty()){ Item it; splitAllergy(line,it.text,it.allergens,it.mask); if(!it.text.empty())items.push_back(it); }
                pos=(nl==std::string::npos)?nl:nl+1; }while(nl!=std::string::npos); } }
}
static std::vector<DayMenu> parseWeek(const std::string& html){
    std::vector<DayMenu> week; auto dates=headerDates(html); week.resize(dates.size());
    for(size_t i=0;i<dates.size();++i){week[i].date=dates[i].first;week[i].dow=dates[i].second;}
    const char* meals[3]={"\xEC\xA1\xB0\xEC\x8B\x9D","\xEC\xA4\x91\xEC\x8B\x9D","\xEC\x84\x9D\xEC\x8B\x9D"};
    for(int mi=0;mi<3;++mi){ auto cells=rowCells(html,meals[mi]);
        for(size_t i=0;i<cells.size()&&i<week.size();++i){ std::string kc; std::vector<Item> its; parseCell(cells[i],kc,its);
            if(!its.empty())week[i].meals.push_back({meals[mi],kc,its}); } }
    return week;
}

// ---- 날짜 ----
static std::string todayStr(){ time_t t=time(nullptr); struct tm lt; localtime_s(&lt,&t);
    char b[16]; sprintf(b,"%04d-%02d-%02d",lt.tm_year+1900,lt.tm_mon+1,lt.tm_mday); return b; }
static std::string addDays(const std::string& d,int delta){ int y=0,m=0,dd=0; sscanf(d.c_str(),"%d-%d-%d",&y,&m,&dd);
    struct tm t{}; t.tm_year=y-1900;t.tm_mon=m-1;t.tm_mday=dd;t.tm_hour=12;t.tm_isdst=-1;
    time_t tt=mktime(&t); tt+=(time_t)delta*86400; struct tm o; localtime_s(&o,&tt);
    char b[16]; sprintf(b,"%04d-%02d-%02d",o.tm_year+1900,o.tm_mon+1,o.tm_mday); return b; }
static std::string dowOf(const std::string& d){ static const char* W[7]={"일","월","화","수","목","금","토"};
    int y=0,m=0,dd=0; sscanf(d.c_str(),"%d-%d-%d",&y,&m,&dd);
    struct tm t{}; t.tm_year=y-1900;t.tm_mon=m-1;t.tm_mday=dd;t.tm_hour=12;t.tm_isdst=-1; mktime(&t); return W[t.tm_wday]; }
static const DayMenu* findDay(const std::string& d){ for(auto& x:g_week) if(x.date==d)return &x; return nullptr; }

// ---- 네트워크 ----
static bool httpReq(bool secure,const wchar_t* host,INTERNET_PORT port,const wchar_t* verb,const wchar_t* path,
                    const std::string& body,const wchar_t* headers,std::string& out){ out.clear(); bool ok=false;
    HINTERNET hS=WinHttpOpen(L"Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36",
                             WINHTTP_ACCESS_TYPE_DEFAULT_PROXY,WINHTTP_NO_PROXY_NAME,WINHTTP_NO_PROXY_BYPASS,0);
    if(!hS)return false; WinHttpSetTimeouts(hS,8000,8000,12000,12000);
    HINTERNET hC=WinHttpConnect(hS,host,port,0);
    if(hC){ DWORD flags=secure?WINHTTP_FLAG_SECURE:0;
        HINTERNET hR=WinHttpOpenRequest(hC,verb,path,nullptr,WINHTTP_NO_REFERER,WINHTTP_DEFAULT_ACCEPT_TYPES,flags);
        if(hR){ LPCWSTR hdr=headers?headers:WINHTTP_NO_ADDITIONAL_HEADERS; DWORD hlen=headers?(DWORD)-1:0; BOOL sent;
            if(!body.empty()) sent=WinHttpSendRequest(hR,hdr,hlen,(LPVOID)body.data(),(DWORD)body.size(),(DWORD)body.size(),0);
            else sent=WinHttpSendRequest(hR,hdr,hlen,WINHTTP_NO_REQUEST_DATA,0,0,0);
            if(sent&&WinHttpReceiveResponse(hR,nullptr)){ DWORD a=0; do{ a=0; if(!WinHttpQueryDataAvailable(hR,&a)||a==0)break;
                    std::string buf(a,0); DWORD rd=0; if(WinHttpReadData(hR,&buf[0],a,&rd)&&rd)out.append(buf.data(),rd);
                }while(a>0); ok=!out.empty(); }
            WinHttpCloseHandle(hR); }
        WinHttpCloseHandle(hC); }
    WinHttpCloseHandle(hS); return ok; }
static bool httpFetch(const std::string& schDt,std::string& out){
    return httpReq(false,HOST_W,HTTP_PORT,L"POST",PATH_W,
        "mi=&sysId=swjb-h&restSeq=&schDt="+schDt+"&schSysId=",
        L"Content-Type: application/x-www-form-urlencoded",out); }


// ---- 설정/캐시 ----
static std::wstring dataDir(){ wchar_t p[MAX_PATH];
    if(SUCCEEDED(SHGetFolderPathW(nullptr,CSIDL_APPDATA,nullptr,0,p))){ std::wstring d=std::wstring(p)+L"\\SwjbMeal"; CreateDirectoryW(d.c_str(),nullptr); return d; } return L"."; }
static std::wstring exeDir(){ wchar_t p[MAX_PATH]; GetModuleFileNameW(nullptr,p,MAX_PATH); std::wstring s=p; size_t q=s.find_last_of(L"\\/"); return q==std::wstring::npos?L".":s.substr(0,q); }
static std::wstring cfgPath(){return dataDir()+L"\\config.ini";}
static std::wstring cachePath(){return dataDir()+L"\\cache.txt";}
static void saveConfig(int x,int y){ FILE* f=_wfopen(cfgPath().c_str(),L"wb"); if(!f)return;
    std::string fn=WtoU8(g_fontName),al; for(int i=1;i<=19;i++) if(g_alg[i]){ if(!al.empty())al+=","; al+=std::to_string(i); }
    fprintf(f,"X=%d\nY=%d\nCOLLAPSED=%d\nFONT=%s\nTHEME=%d\nSIZE=%d\nALLERGY=%s\n",x,y,g_collapsed?1:0,fn.c_str(),g_light?1:0,g_size,al.c_str()); fclose(f); }
static bool loadConfig(int& x,int& y){ FILE* f=_wfopen(cfgPath().c_str(),L"rb"); if(!f)return false;
    char l[256]; bool got=false; int v;
    while(fgets(l,sizeof(l),f)){ std::string s=l; while(!s.empty()&&(s.back()=='\n'||s.back()=='\r'))s.pop_back();
        if(sscanf(l,"X=%d",&v)==1){x=v;got=true;} else if(sscanf(l,"Y=%d",&v)==1)y=v;
        else if(sscanf(l,"COLLAPSED=%d",&v)==1)g_collapsed=(v!=0);
        else if(sscanf(l,"THEME=%d",&v)==1)g_light=(v!=0);
        else if(sscanf(l,"SIZE=%d",&v)==1){ if(v>=0&&v<=2)g_size=v; }
        else if(s.rfind("FONT=",0)==0){ std::string fn=trim(s.substr(5)); if(!fn.empty())g_fontName=U8toW(fn); }
        else if(s.rfind("ALLERGY=",0)==0){ for(auto& t:split(trim(s.substr(8)),",")){ int n=atoi(trim(t).c_str()); if(n>=1&&n<=19)g_alg[n]=true; } } }
    fclose(f); return got; }
static void saveCache(){ FILE* f=_wfopen(cachePath().c_str(),L"wb"); if(!f)return; fprintf(f,"%lld\n",(long long)g_lastFetch);
    for(auto& d:g_week){ std::string line=d.date+"|"+d.dow+"|";
        for(size_t mi=0;mi<d.meals.size();++mi){ if(mi)line+="\x1d"; line+=d.meals[mi].name+"\x1c"+d.meals[mi].kcal;
            for(auto& it:d.meals[mi].items)line+="\x1e"+it.text+"\x1f"+it.allergens+"\x1f"+std::to_string(it.mask); }
        line+="\n"; fwrite(line.data(),1,line.size(),f); } fclose(f); }
static void loadCache(){ FILE* f=_wfopen(cachePath().c_str(),L"rb"); if(!f)return;
    std::string all; char b[4096]; size_t n; while((n=fread(b,1,sizeof(b),f))>0)all.append(b,n); fclose(f);
    auto lines=split(all,"\n"); if(lines.empty())return; g_lastFetch=(time_t)atoll(lines[0].c_str()); g_week.clear();
    for(size_t i=1;i<lines.size();++i){ if(trim(lines[i]).empty())continue; auto p=split(lines[i],"|"); if(p.size()<3)continue;
        DayMenu d; d.date=p[0]; d.dow=p[1];
        if(!p[2].empty())for(auto& ms:split(p[2],"\x1d")){ auto nk=split(ms,"\x1c"); if(nk.size()<2)continue;
            Meal m; m.name=nk[0]; m.kcal=nk[1]; size_t pos=ms.find("\x1e");
            if(pos!=std::string::npos)for(auto& is:split(ms.substr(pos+1),"\x1e")){ auto tf=split(is,"\x1f"); Item it; it.text=tf[0]; if(tf.size()>1)it.allergens=tf[1]; if(tf.size()>2)it.mask=(unsigned)strtoul(tf[2].c_str(),nullptr,10); if(!it.text.empty())m.items.push_back(it);}
            d.meals.push_back(m); }
        g_week.push_back(d); } }

static bool fetchDue(){ if(g_week.empty())return true; if(!findDay(g_viewDate))return true;
    return (time(nullptr)-g_lastFetch)>=(time_t)CRAWL_INTERVAL_DAYS*86400; }

static DWORD WINAPI fetchThread(LPVOID){ std::string html; bool ok=httpFetch(g_fetchDate,html);
    auto* wk=new std::vector<DayMenu>(); if(ok)*wk=parseWeek(html);
    PostMessageW(g_hwnd,WM_APP_FETCH_DONE,(WPARAM)(ok?1:0),(LPARAM)wk); return 0; }
static void startFetch(const std::string& date){ if(g_fetching)return; g_fetching=true; g_fetchDate=date;
    HANDLE h=CreateThread(nullptr,0,fetchThread,nullptr,0,nullptr); if(h)CloseHandle(h); else g_fetching=false; }

// ---- 에셋 로드 (파일을 메모리로 1회 읽고 즉시 닫음 → 실행 중 파일 미점유) ----
static std::vector<BYTE> readAll(const std::wstring& path){ std::vector<BYTE> v;
    HANDLE h=CreateFileW(path.c_str(),GENERIC_READ,FILE_SHARE_READ|FILE_SHARE_WRITE,nullptr,OPEN_EXISTING,FILE_ATTRIBUTE_NORMAL,nullptr);
    if(h==INVALID_HANDLE_VALUE)return v; LARGE_INTEGER sz; if(GetFileSizeEx(h,&sz)&&sz.QuadPart>0){ v.resize((size_t)sz.QuadPart);
        DWORD rd=0; ReadFile(h,v.data(),(DWORD)v.size(),&rd,nullptr); v.resize(rd); } CloseHandle(h); return v; }
// 메모리 바이트를 디코드해 소유 비트맵으로 복제 → 스트림/원본 비점유
static Gdiplus::Bitmap* decodeOwned(const BYTE* data,size_t n){ if(!data||!n)return nullptr;
    HGLOBAL hg=GlobalAlloc(GMEM_MOVEABLE,n); if(!hg)return nullptr;
    void* p=GlobalLock(hg); memcpy(p,data,n); GlobalUnlock(hg);
    IStream* st=nullptr; if(CreateStreamOnHGlobal(hg,TRUE,&st)!=S_OK){ GlobalFree(hg); return nullptr; }
    Gdiplus::Bitmap* tmp=Gdiplus::Bitmap::FromStream(st); Gdiplus::Bitmap* out=nullptr;
    if(tmp&&tmp->GetLastStatus()==Gdiplus::Ok){ int w=tmp->GetWidth(),h=tmp->GetHeight();
        out=new Gdiplus::Bitmap(w,h,PixelFormat32bppARGB); Gdiplus::Graphics g(out);
        g.Clear(Gdiplus::Color(0,0,0,0)); g.SetInterpolationMode(Gdiplus::InterpolationModeHighQualityBicubic);
        g.DrawImage(tmp,0,0,w,h); }
    if(tmp)delete tmp; st->Release(); return out; }
static Gdiplus::Image* loadOwned(const std::wstring& path){ auto b=readAll(path); return decodeOwned(b.data(),b.size()); }
static Gdiplus::Image* findIcon(const wchar_t* base){ const wchar_t* ext[3]={L".png",L".ico",L".bmp"};
    std::wstring dirs[3]={exeDir()+L"\\assets",exeDir(),dataDir()};
    for(auto& dir:dirs)for(auto e:ext){ std::wstring path=dir+L"\\"+base+e;
        if(GetFileAttributesW(path.c_str())!=INVALID_FILE_ATTRIBUTES){ auto* img=loadOwned(path); if(img)return img; } }
    return nullptr; }
static void loadIcons(){ g_imgRefresh=findIcon(L"refresh"); g_imgMin=findIcon(L"minimize"); g_imgClose=findIcon(L"close"); }
// assets/font.ttf 를 메모리 폰트로 등록(파일 미점유)하고 패밀리명을 g_fontName 으로
static void loadFontAsset(){ std::wstring p=exeDir()+L"\\assets\\font.ttf";
    auto bytes=readAll(p); if(bytes.empty())return; g_fontBuf=std::move(bytes);
    DWORD n=0; g_fontMem=AddFontMemResourceEx(g_fontBuf.data(),(DWORD)g_fontBuf.size(),nullptr,&n); if(!g_fontMem)return;
    Gdiplus::PrivateFontCollection pfc;
    if(pfc.AddMemoryFont(g_fontBuf.data(),(INT)g_fontBuf.size())==Gdiplus::Ok&&pfc.GetFamilyCount()>0){
        int got=0; Gdiplus::FontFamily fam; pfc.GetFamilies(1,&fam,&got);
        if(got>0){ WCHAR nm[LF_FACESIZE]={0}; if(fam.GetFamilyName(nm)==Gdiplus::Ok&&nm[0])g_fontName=nm; } } }

static void drawImg(HDC hdc,Gdiplus::Image* img,RECT box){ Gdiplus::Graphics g(hdc);
    g.SetInterpolationMode(Gdiplus::InterpolationModeHighQualityBicubic);
    g.SetPixelOffsetMode(Gdiplus::PixelOffsetModeHalf); g.SetSmoothingMode(Gdiplus::SmoothingModeAntiAlias);
    int cx=(box.left+box.right)/2,cy=(box.top+box.bottom)/2;
    g.DrawImage(img,Gdiplus::Rect(cx-ICON_DRAW/2,cy-ICON_DRAW/2,ICON_DRAW,ICON_DRAW)); }

// ---- 본문 ----
static int DrawBody(HDC hdc,int startY,bool measure){
    const int padX=16; SetBkMode(hdc,TRANSPARENT); int y=startY+4;
    if(!measure)g_itemHits.clear();
    std::string today=todayStr(); bool isToday=(g_viewDate==today);
    auto line=[&](const std::wstring& ws,HFONT font,COLORREF col,int indent,const std::wstring* tip){
        HFONT old=(HFONT)SelectObject(hdc,font); RECT calc{padX+indent,y,WIN_W-padX,y+2000};
        DrawTextW(hdc,ws.c_str(),-1,&calc,DT_WORDBREAK|DT_NOPREFIX|DT_CALCRECT); int h=calc.bottom-calc.top; if(h<18)h=18;
        if(!measure){ SetTextColor(hdc,col); RECT dr{padX+indent,y,WIN_W-padX,y+h}; DrawTextW(hdc,ws.c_str(),-1,&dr,DT_WORDBREAK|DT_NOPREFIX);
            if(tip){ Hit hit; hit.rc={padX+indent,y,WIN_W-padX,y+h}; hit.tip=*tip; g_itemHits.push_back(hit);} }
        SelectObject(hdc,old); y+=h; };

    int y0=0,m0=0,d0=0; sscanf(g_viewDate.c_str(),"%d-%d-%d",&y0,&m0,&d0);
    std::wstring ds=U8toW(std::to_string(m0)+"월 "+std::to_string(d0)+"일 ("+dowOf(g_viewDate)+")");
    if(!measure){ HFONT old=(HFONT)SelectObject(hdc,g_fDate); SetTextColor(hdc,isToday?COL_ACCENT:COL_DATE);
        RECT hr{padX,y,WIN_W-padX,y+26}; DrawTextW(hdc,ds.c_str(),-1,&hr,DT_SINGLELINE|DT_VCENTER);
        if(isToday){ SelectObject(hdc,g_fTag); SetTextColor(hdc,COL_ACCENT); RECT tr{padX,y,WIN_W-padX,y+26};
            DrawTextW(hdc,L"오늘",-1,&tr,DT_SINGLELINE|DT_VCENTER|DT_RIGHT); } SelectObject(hdc,old); }
    y+=28;

    const DayMenu* day=findDay(g_viewDate);
    if(!day){ line(g_fetching?L"불러오는 중…":L"급식 정보가 없습니다",g_fItem,COL_SUB,4,nullptr); y+=12; return y; }
    if(day->meals.empty()){ line(L"급식이 없습니다",g_fItem,COL_SUB,4,nullptr); y+=12; return y; }
    bool multi=day->meals.size()>1;
    for(auto& m:day->meals){ std::string pre=multi?"["+m.name+"] ":"";
        if(!m.kcal.empty())line(U8toW(pre+m.kcal+" kcal"),g_fSmall,COL_SUB,4,nullptr);
        else if(multi)line(U8toW(pre),g_fSmall,COL_SUB,4,nullptr);
        for(auto& it:m.items){ bool warn=(it.mask&g_algMask)!=0;
            std::wstring base=it.allergens.empty()?L"알레르기 정보 없음":L"알레르기: "+U8toW(it.allergens);
            std::wstring tip=warn?(L"주의! 내 알레르기 포함\n"+base):base;
            std::wstring label=(warn?L"● ":L"· ")+U8toW(it.text);
            line(label,g_fItem,warn?COL_WARN:COL_ITEM,6,&tip); } }
    y+=12; return y;
}

static void computeHeight(){ HDC hdc=GetDC(g_hwnd); g_contentH=DrawBody(hdc,0,true); ReleaseDC(g_hwnd,hdc);
    RECT wa{}; SystemParametersInfo(SPI_GETWORKAREA,0,&wa,0); int maxH=(int)((wa.bottom-wa.top)*0.88);
    int want=HEADER_H+g_contentH+NAV_H; g_winH=g_collapsed?HEADER_H:(want>maxH?maxH:want);
    int vis=g_winH-HEADER_H-NAV_H,ms=g_contentH-vis; if(ms<0)ms=0; if(g_scrollY>ms)g_scrollY=ms; if(g_scrollY<0)g_scrollY=0; }
static void applySize(){ SetWindowPos(g_hwnd,nullptr,0,0,WIN_W,g_winH,SWP_NOMOVE|SWP_NOZORDER|SWP_NOACTIVATE);
    SetWindowRgn(g_hwnd,CreateRoundRectRgn(0,0,WIN_W+1,g_winH+1,18,18),TRUE); InvalidateRect(g_hwnd,nullptr,FALSE); }
static void relayout(){ computeHeight(); applySize(); }

static void drawRefresh(HDC hdc,RECT r,COLORREF c){ int cx=(r.left+r.right)/2,cy=(r.top+r.bottom)/2,R=6;
    HPEN pen=CreatePen(PS_SOLID,2,c); HPEN op=(HPEN)SelectObject(hdc,pen); POINT p[24]; int n=0;
    for(int a=70;a<=340;a+=18){ double rad=a*3.14159265/180.0; p[n].x=cx+(int)lround(R*cos(rad)); p[n].y=cy-(int)lround(R*sin(rad)); n++; }
    Polyline(hdc,p,n); SelectObject(hdc,op); DeleteObject(pen);
    double rad=70*3.14159265/180.0; int ax=cx+(int)lround(R*cos(rad)),ay=cy-(int)lround(R*sin(rad));
    POINT tri[3]={{ax+1,ay+1},{ax+6,ay},{ax+1,ay-5}}; HBRUSH b=CreateSolidBrush(c); HBRUSH ob=(HBRUSH)SelectObject(hdc,b);
    HGDIOBJ np=SelectObject(hdc,GetStockObject(NULL_PEN)); Polygon(hdc,tri,3); SelectObject(hdc,np); SelectObject(hdc,ob); DeleteObject(b); }
static void drawTri(HDC hdc,int cx,int cy,bool left,COLORREF c){ POINT t[3];
    if(left){t[0]={cx+4,cy-6};t[1]={cx+4,cy+6};t[2]={cx-4,cy};} else {t[0]={cx-4,cy-6};t[1]={cx-4,cy+6};t[2]={cx+4,cy};}
    HBRUSH b=CreateSolidBrush(c); HBRUSH ob=(HBRUSH)SelectObject(hdc,b); HGDIOBJ np=SelectObject(hdc,GetStockObject(NULL_PEN));
    Polygon(hdc,t,3); SelectObject(hdc,np); SelectObject(hdc,ob); DeleteObject(b); }

static void paint(HDC hdc){ RECT rc; GetClientRect(g_hwnd,&rc); int W=rc.right,H=rc.bottom;
    HDC mem=CreateCompatibleDC(hdc); HBITMAP bmp=CreateCompatibleBitmap(hdc,W,H); HBITMAP ob=(HBITMAP)SelectObject(mem,bmp);
    HBRUSH bg=CreateSolidBrush(COL_BG); RECT full{0,0,W,H}; FillRect(mem,&full,bg); DeleteObject(bg);

    if(!g_collapsed){ SaveDC(mem); IntersectClipRect(mem,0,HEADER_H,W,H-NAV_H); DrawBody(mem,HEADER_H+2-g_scrollY,false); RestoreDC(mem,-1); }

    if(HEADER_H>0){
        HBRUSH hb=CreateSolidBrush(COL_HEADER); RECT hr{0,0,W,HEADER_H}; FillRect(mem,&hr,hb); DeleteObject(hb);
        SetBkMode(mem,TRANSPARENT); HFONT old=(HFONT)SelectObject(mem,g_fTitle); SetTextColor(mem,COL_TITLE);
        RECT tr{14,0,W-96,HEADER_H}; DrawTextW(mem,L"급식표",-1,&tr,DT_SINGLELINE|DT_VCENTER|DT_NOPREFIX); SelectObject(mem,old);
        int by=HEADER_H/2;
        g_rcRefresh={W-84,by-11,W-62,by+11}; g_rcMin={W-58,by-11,W-36,by+11}; g_rcClose={W-32,by-11,W-10,by+11};
        if(g_imgRefresh)drawImg(mem,g_imgRefresh,g_rcRefresh); else drawRefresh(mem,g_rcRefresh,g_fetching?COL_ACCENT:COL_ICON);
        if(g_imgMin)drawImg(mem,g_imgMin,g_rcMin);
        else { HPEN pen=CreatePen(PS_SOLID,2,COL_ICON); HPEN opn=(HPEN)SelectObject(mem,pen);
            MoveToEx(mem,g_rcMin.left+3,by+(g_collapsed?4:0),nullptr); LineTo(mem,g_rcMin.right-3,by+(g_collapsed?4:0));
            SelectObject(mem,opn); DeleteObject(pen); }
        if(g_imgClose)drawImg(mem,g_imgClose,g_rcClose);
        else { HPEN pen=CreatePen(PS_SOLID,2,COL_ICON); HPEN opn=(HPEN)SelectObject(mem,pen);
            MoveToEx(mem,g_rcClose.left+3,by-7,nullptr); LineTo(mem,g_rcClose.right-3,by+7);
            MoveToEx(mem,g_rcClose.right-3,by-7,nullptr); LineTo(mem,g_rcClose.left+3,by+7);
            SelectObject(mem,opn); DeleteObject(pen); }
    } else { g_rcRefresh=g_rcMin=g_rcClose=RECT{0,0,0,0}; }

    if(!g_collapsed){ int vis=H-HEADER_H-NAV_H;
        if(g_contentH>vis){ int bar=vis*vis/g_contentH; if(bar<24)bar=24; int ms=g_contentH-vis; int pos=ms>0?(vis-bar)*g_scrollY/ms:0;
            HBRUSH sb=CreateSolidBrush(COL_SCROLL); RECT br{W-4,HEADER_H+pos,W-1,HEADER_H+pos+bar}; FillRect(mem,&br,sb); DeleteObject(sb); } }

    if(!g_collapsed){ int ny=H-NAV_H; HBRUSH nb=CreateSolidBrush(COL_NAV); RECT nr{0,ny,W,H}; FillRect(mem,&nr,nb); DeleteObject(nb);
        HPEN ln=CreatePen(PS_SOLID,1,COL_NAV_LINE); HPEN olp=(HPEN)SelectObject(mem,ln); MoveToEx(mem,0,ny,nullptr); LineTo(mem,W,ny); SelectObject(mem,olp); DeleteObject(ln);
        int cy=ny+NAV_H/2; g_rcPrev={10,ny+4,56,H-4}; g_rcNext={W-56,ny+4,W-10,H-4};
        drawTri(mem,30,cy,true,COL_NAVARROW); drawTri(mem,W-30,cy,false,COL_NAVARROW);
        if(g_viewDate!=todayStr()){ g_rcToday={W/2-34,ny+6,W/2+34,H-6}; HBRUSH tb=CreateSolidBrush(COL_TODAY_BG); FillRect(mem,&g_rcToday,tb); DeleteObject(tb);
            HFONT of=(HFONT)SelectObject(mem,g_fNav); SetTextColor(mem,COL_TODAY_TX); DrawTextW(mem,L"오늘",-1,&g_rcToday,DT_SINGLELINE|DT_VCENTER|DT_CENTER); SelectObject(mem,of); }
        else g_rcToday={0,0,0,0}; }

    BitBlt(hdc,0,0,W,H,mem,0,0,SRCCOPY); SelectObject(mem,ob); DeleteObject(bmp); DeleteDC(mem); }

// ---- 툴팁 ----
static LRESULT CALLBACK TipProc(HWND h,UINT msg,WPARAM wp,LPARAM lp){
    if(msg==WM_PAINT){ PAINTSTRUCT ps; HDC hdc=BeginPaint(h,&ps); RECT rc; GetClientRect(h,&rc);
        HBRUSH b=CreateSolidBrush(COL_TIP_BG); FillRect(hdc,&rc,b); DeleteObject(b);
        SetBkMode(hdc,TRANSPARENT); SetTextColor(hdc,COL_TIP_TX); HFONT of=(HFONT)SelectObject(hdc,g_fItem);
        RECT t{8,6,rc.right-8,rc.bottom-6}; DrawTextW(hdc,g_tipText.c_str(),-1,&t,DT_WORDBREAK|DT_NOPREFIX); SelectObject(hdc,of);
        EndPaint(h,&ps); return 0; }
    return DefWindowProcW(h,msg,wp,lp); }
static void TipHide(){ if(g_tip)ShowWindow(g_tip,SW_HIDE); }
static void TipShow(POINT sp,const std::wstring& txt){ if(!g_tip)return; g_tipText=txt;
    HDC hdc=GetDC(g_tip); HFONT of=(HFONT)SelectObject(hdc,g_fItem); RECT m{0,0,240,2000};
    DrawTextW(hdc,txt.c_str(),-1,&m,DT_WORDBREAK|DT_NOPREFIX|DT_CALCRECT); SelectObject(hdc,of); ReleaseDC(g_tip,hdc);
    int w=(m.right-m.left)+16, hh=(m.bottom-m.top)+12;
    RECT wa{}; SystemParametersInfo(SPI_GETWORKAREA,0,&wa,0);
    int x=sp.x,y=sp.y; if(x+w>wa.right)x=wa.right-w; if(y+hh>wa.bottom)y=sp.y-hh-24; if(y<0)y=0;
    SetWindowPos(g_tip,HWND_TOPMOST,x,y,w,hh,SWP_NOACTIVATE|SWP_SHOWWINDOW); InvalidateRect(g_tip,nullptr,TRUE); }

// ---- 트레이 ----
static void trayAdd(){ NOTIFYICONDATAW n{}; n.cbSize=sizeof(n); n.hWnd=g_hwnd; n.uID=TRAY_UID; n.uFlags=NIF_ICON|NIF_MESSAGE|NIF_TIP;
    n.uCallbackMessage=TRAY_MSG; n.hIcon=LoadIcon(nullptr,IDI_APPLICATION); wcscpy(n.szTip,L"수원정보과학고 급식"); Shell_NotifyIconW(NIM_ADD,&n); }
static void trayRemove(){ NOTIFYICONDATAW n{}; n.cbSize=sizeof(n); n.hWnd=g_hwnd; n.uID=TRAY_UID; Shell_NotifyIconW(NIM_DELETE,&n); }
static bool startupOn(){ HKEY k; bool on=false;
    if(RegOpenKeyExW(HKEY_CURRENT_USER,L"Software\\Microsoft\\Windows\\CurrentVersion\\Run",0,KEY_READ,&k)==ERROR_SUCCESS){
        if(RegQueryValueExW(k,L"SwjbMeal",nullptr,nullptr,nullptr,nullptr)==ERROR_SUCCESS)on=true; RegCloseKey(k); } return on; }
static void setStartup(bool on){ HKEY k;
    if(RegOpenKeyExW(HKEY_CURRENT_USER,L"Software\\Microsoft\\Windows\\CurrentVersion\\Run",0,KEY_SET_VALUE,&k)==ERROR_SUCCESS){
        if(on){ wchar_t p[MAX_PATH]; GetModuleFileNameW(nullptr,p,MAX_PATH); std::wstring q=L"\""+std::wstring(p)+L"\"";
            RegSetValueExW(k,L"SwjbMeal",0,REG_SZ,(const BYTE*)q.c_str(),(DWORD)((q.size()+1)*sizeof(wchar_t))); }
        else RegDeleteValueW(k,L"SwjbMeal"); RegCloseKey(k); } }
static void trayMenu(){ POINT pt; GetCursorPos(&pt); HMENU m=CreatePopupMenu();
    if(g_size!=0) AppendMenuW(m,MF_STRING,CMD_RESTORE,g_collapsed?L"펼치기":L"접기");
    AppendMenuW(m,MF_STRING,CMD_REFRESH,L"새로고침");
    AppendMenuW(m,MF_SEPARATOR,0,nullptr);
    HMENU sz=CreatePopupMenu();
    const wchar_t* sn[3]={L"최소",L"기본",L"크게"};
    for(int i=0;i<3;i++) AppendMenuW(sz,MF_STRING|(g_size==i?MF_CHECKED:0),CMD_SIZE_BASE+i,sn[i]);
    AppendMenuW(m,MF_POPUP,(UINT_PTR)sz,L"창 크기");
    HMENU th=CreatePopupMenu();
    AppendMenuW(th,MF_STRING|(!g_light?MF_CHECKED:0),CMD_THEME_DARK,L"블랙");
    AppendMenuW(th,MF_STRING|( g_light?MF_CHECKED:0),CMD_THEME_LIGHT,L"화이트");
    AppendMenuW(m,MF_POPUP,(UINT_PTR)th,L"테마");
    HMENU al=CreatePopupMenu();
    for(int i=1;i<=19;i++){ std::wstring nm=U8toW(std::to_string(i)+". "+ALLERGEN[i]);
        AppendMenuW(al,MF_STRING|(g_alg[i]?MF_CHECKED:0),CMD_ALG_BASE+i,nm.c_str()); }
    AppendMenuW(m,MF_POPUP,(UINT_PTR)al,L"알레르기 표시 설정");
    AppendMenuW(m,MF_STRING|(startupOn()?MF_CHECKED:0),CMD_STARTUP,L"Windows 시작 시 실행");
    AppendMenuW(m,MF_SEPARATOR,0,nullptr);
    AppendMenuW(m,MF_STRING,CMD_EXIT,L"종료");
    SetForegroundWindow(g_hwnd); TrackPopupMenu(m,TPM_RIGHTBUTTON,pt.x,pt.y,0,g_hwnd,nullptr); DestroyMenu(m); }

static void createFonts(){ HFONT old[6]={g_fTitle,g_fSmall,g_fDate,g_fItem,g_fTag,g_fNav};
    double s=g_size==0?0.92:(g_size==2?1.30:1.0);
    auto mk=[&](int h,int w){ return CreateFontW(-(int)lround(h*s),0,0,0,w,FALSE,FALSE,FALSE,HANGEUL_CHARSET,OUT_TT_PRECIS,CLIP_DEFAULT_PRECIS,CLEARTYPE_QUALITY,FF_DONTCARE,g_fontName.c_str()); };
    g_fTitle=mk(15,FW_SEMIBOLD); g_fSmall=mk(12,FW_NORMAL); g_fDate=mk(16,FW_BOLD);
    g_fItem=mk(14,FW_NORMAL); g_fTag=mk(12,FW_BOLD); g_fNav=mk(12,FW_SEMIBOLD);
    for(HFONT f:old) if(f)DeleteObject(f); }
static void toggleCollapse(){ if(g_size==0)return;  // 최소 모드엔 헤더가 없어 접기 불가
    g_collapsed=!g_collapsed; g_scrollY=0; TipHide(); g_hoverIdx=-1; relayout();
    RECT wr; GetWindowRect(g_hwnd,&wr); saveConfig(wr.left,wr.top); }
static void setSize(int s){ g_size=s; if(g_size==0)g_collapsed=false; applySizePreset(); createFonts();
    g_scrollY=0; TipHide(); g_hoverIdx=-1; relayout();
    RECT wr; GetWindowRect(g_hwnd,&wr); saveConfig(wr.left,wr.top); }
static void gotoDate(const std::string& d){ g_viewDate=d; g_scrollY=0; TipHide(); g_hoverIdx=-1; if(!findDay(d))startFetch(d); relayout(); }

static LRESULT CALLBACK WndProc(HWND hwnd,UINT msg,WPARAM wp,LPARAM lp){
    switch(msg){
    case WM_ACTIVATE:
        if(LOWORD(wp)==WA_INACTIVE){ TipHide(); SetWindowPos(hwnd,HWND_BOTTOM,0,0,0,0,SWP_NOMOVE|SWP_NOSIZE|SWP_NOACTIVATE); }
        else SetWindowPos(hwnd,HWND_TOP,0,0,0,0,SWP_NOMOVE|SWP_NOSIZE|SWP_NOACTIVATE);
        return 0;
    case WM_PAINT:{ PAINTSTRUCT ps; HDC hdc=BeginPaint(hwnd,&ps); paint(hdc); EndPaint(hwnd,&ps); return 0; }
    case WM_LBUTTONDOWN:{ POINT pt{GET_X_LPARAM(lp),GET_Y_LPARAM(lp)};
        if(PtInRect(&g_rcClose,pt)){DestroyWindow(hwnd);return 0;}
        if(PtInRect(&g_rcMin,pt)){toggleCollapse();return 0;}
        if(PtInRect(&g_rcRefresh,pt)){startFetch(g_viewDate);InvalidateRect(hwnd,nullptr,FALSE);return 0;}
        if(!g_collapsed){ if(PtInRect(&g_rcPrev,pt)){gotoDate(addDays(g_viewDate,-1));return 0;}
            if(PtInRect(&g_rcNext,pt)){gotoDate(addDays(g_viewDate,+1));return 0;}
            if(g_rcToday.right>g_rcToday.left&&PtInRect(&g_rcToday,pt)){gotoDate(todayStr());return 0;} }
        // 드래그: 헤더(기본/크게) 또는 본문 영역(최소 모드, 네비 제외)
        if(pt.y<HEADER_H || (g_size==0 && pt.y<g_winH-NAV_H)){ g_drag=true; RECT wr; GetWindowRect(hwnd,&wr); POINT sp=pt; ClientToScreen(hwnd,&sp);
            g_dragOff.x=sp.x-wr.left; g_dragOff.y=sp.y-wr.top; SetCapture(hwnd); }
        return 0; }
    case WM_RBUTTONUP: trayMenu(); return 0;   // 창 우클릭 → 메뉴
    case WM_MOUSEMOVE:{
        if(g_drag){ POINT sp; GetCursorPos(&sp); SetWindowPos(hwnd,nullptr,sp.x-g_dragOff.x,sp.y-g_dragOff.y,0,0,SWP_NOSIZE|SWP_NOZORDER|SWP_NOACTIVATE); return 0; }
        if(!g_tracking){ TRACKMOUSEEVENT t{sizeof(t),TME_LEAVE,hwnd,0}; TrackMouseEvent(&t); g_tracking=true; }
        if(!g_collapsed){ POINT pt{GET_X_LPARAM(lp),GET_Y_LPARAM(lp)}; int hit=-1;
            if(pt.y>=HEADER_H&&pt.y<g_winH-NAV_H)for(size_t i=0;i<g_itemHits.size();++i)if(PtInRect(&g_itemHits[i].rc,pt)){hit=(int)i;break;}
            if(hit!=g_hoverIdx){ g_hoverIdx=hit;
                if(hit>=0){ POINT sp; GetCursorPos(&sp); TipShow({sp.x+14,sp.y+18},g_itemHits[hit].tip); }
                else TipHide(); } }
        return 0; }
    case WM_MOUSELEAVE: g_tracking=false; g_hoverIdx=-1; TipHide(); return 0;
    case WM_LBUTTONUP: if(g_drag){ g_drag=false; ReleaseCapture(); RECT wr; GetWindowRect(hwnd,&wr); saveConfig(wr.left,wr.top); } return 0;
    case WM_MOUSEWHEEL: if(!g_collapsed){ int d=GET_WHEEL_DELTA_WPARAM(wp); int vis=g_winH-HEADER_H-NAV_H,ms=g_contentH-vis; if(ms<0)ms=0;
            g_scrollY-=(d/WHEEL_DELTA)*36; if(g_scrollY<0)g_scrollY=0; if(g_scrollY>ms)g_scrollY=ms; TipHide(); g_hoverIdx=-1; InvalidateRect(hwnd,nullptr,FALSE); } return 0;
    case TRAY_MSG: if(lp==WM_LBUTTONDBLCLK){ if(g_collapsed)toggleCollapse(); SetForegroundWindow(hwnd); } else if(lp==WM_RBUTTONUP)trayMenu(); return 0;
    case WM_COMMAND:{ int id=LOWORD(wp);
        if(id>CMD_ALG_BASE&&id<=CMD_ALG_BASE+19){ int n=id-CMD_ALG_BASE; g_alg[n]=!g_alg[n]; recalcMask();
            RECT wr; GetWindowRect(hwnd,&wr); saveConfig(wr.left,wr.top); InvalidateRect(hwnd,nullptr,FALSE); return 0; }
        if(id>=CMD_SIZE_BASE&&id<=CMD_SIZE_BASE+2){ if(g_size!=id-CMD_SIZE_BASE) setSize(id-CMD_SIZE_BASE); return 0; }
        switch(id){
            case CMD_RESTORE: toggleCollapse(); break;
            case CMD_REFRESH: startFetch(g_viewDate); InvalidateRect(hwnd,nullptr,FALSE); break;
            case CMD_THEME_DARK: if(g_light){ g_light=false; applyTheme(); RECT wr; GetWindowRect(hwnd,&wr); saveConfig(wr.left,wr.top); InvalidateRect(hwnd,nullptr,FALSE);} break;
            case CMD_THEME_LIGHT: if(!g_light){ g_light=true; applyTheme(); RECT wr; GetWindowRect(hwnd,&wr); saveConfig(wr.left,wr.top); InvalidateRect(hwnd,nullptr,FALSE);} break;
            case CMD_STARTUP: setStartup(!startupOn()); break;
            case CMD_EXIT: DestroyWindow(hwnd); break;
        } return 0; }
    case WM_TIMER: if(wp==TIMER_ID&&fetchDue())startFetch(g_viewDate); return 0;
    case WM_APP_FETCH_DONE:{ g_fetching=false; bool ok=(wp==1); auto* wk=(std::vector<DayMenu>*)lp; g_lastOk=ok;
        if(ok&&wk&&!wk->empty()){ g_week=*wk; g_lastFetch=time(nullptr); saveCache(); relayout(); } else InvalidateRect(hwnd,nullptr,FALSE);
        delete wk; return 0; }
    case WM_DESTROY: trayRemove(); KillTimer(hwnd,TIMER_ID); PostQuitMessage(0); return 0;
    }
    return DefWindowProcW(hwnd,msg,wp,lp); }

int WINAPI WinMain(HINSTANCE hInst,HINSTANCE,LPSTR,int){
    SetProcessDPIAware();
    Gdiplus::GdiplusStartupInput gsi; Gdiplus::GdiplusStartup(&g_gdipTok,&gsi,nullptr);

    g_fontName=FONT_DEFAULT;
    loadCache();
    int x=-1,y=-1; bool haveCfg=loadConfig(x,y);   // FONT/위치/접힘/테마/알레르기 반영
    recalcMask(); applyTheme(); applySizePreset();
    loadFontAsset();                               // assets/font.ttf 있으면 최우선 사용
    g_viewDate=todayStr();
    createFonts();

    WNDCLASSW wc{}; wc.lpfnWndProc=WndProc; wc.hInstance=hInst; wc.hCursor=LoadCursor(nullptr,IDC_ARROW); wc.lpszClassName=L"SwjbMealWidget"; RegisterClassW(&wc);
    WNDCLASSW tc{}; tc.lpfnWndProc=TipProc; tc.hInstance=hInst; tc.lpszClassName=L"SwjbMealTip"; RegisterClassW(&tc);

    loadIcons();

    g_hwnd=CreateWindowExW(WS_EX_TOOLWINDOW|WS_EX_LAYERED,L"SwjbMealWidget",L"급식",WS_POPUP,0,0,WIN_W,260,nullptr,nullptr,hInst,nullptr);
    if(!g_hwnd)return 0; SetLayeredWindowAttributes(g_hwnd,0,WIN_ALPHA,LWA_ALPHA);
    g_tip=CreateWindowExW(WS_EX_TOOLWINDOW|WS_EX_TOPMOST|WS_EX_NOACTIVATE|WS_EX_LAYERED,L"SwjbMealTip",L"",WS_POPUP,0,0,10,10,nullptr,nullptr,hInst,nullptr);
    SetLayeredWindowAttributes(g_tip,0,TIP_ALPHA,LWA_ALPHA);

    relayout();
    if(!haveCfg){ RECT wa{}; SystemParametersInfo(SPI_GETWORKAREA,0,&wa,0); x=wa.right-WIN_W-24; y=wa.top+24; } // 기본: 우상단
    SetWindowPos(g_hwnd,HWND_BOTTOM,x,y,WIN_W,g_winH,SWP_NOACTIVATE);
    trayAdd(); ShowWindow(g_hwnd,SW_SHOWNOACTIVATE);
    SetWindowPos(g_hwnd,HWND_BOTTOM,0,0,0,0,SWP_NOMOVE|SWP_NOSIZE|SWP_NOACTIVATE);

    SetTimer(g_hwnd,TIMER_ID,30*60*1000,nullptr);
    startFetch(g_viewDate);   // 시작 시 항상 1회 크롤링

    MSG msg; while(GetMessageW(&msg,nullptr,0,0)>0){ TranslateMessage(&msg); DispatchMessageW(&msg); }
    DeleteObject(g_fTitle);DeleteObject(g_fSmall);DeleteObject(g_fDate);DeleteObject(g_fItem);DeleteObject(g_fTag);DeleteObject(g_fNav);
    delete g_imgRefresh; delete g_imgMin; delete g_imgClose;
    if(g_fontMem)RemoveFontMemResourceEx(g_fontMem); Gdiplus::GdiplusShutdown(g_gdipTok);
    return 0;
}
