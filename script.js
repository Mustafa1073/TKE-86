/* weak-device detector: adds class "lite" to <html> when frames are consistently slow */
(function(){var H=document.documentElement,K='tke-lite6',Q=location.search;
function put(v){try{localStorage.setItem(K,v?String(Date.now()):'0')}catch(e){}}
function on(s){H.classList.add('lite');if(s)put(1)}
if(/[?&]lite=1(&|$)/.test(Q)){on(1);return}
if(/[?&]lite=0(&|$)/.test(Q)){put(0);return}
try{var v=localStorage.getItem(K);if(v==='0')return;if(v&&Date.now()-(+v)<6048e5){on(0);return}}catch(e){}
if((navigator.deviceMemory||8)<=2||(navigator.hardwareConcurrency||8)<=2){on(1);return}
var d=[],last=0,w0=0,bad=0,t00=0;
function f(t){if(H.classList.contains('lite'))return;
 if(!t00)t00=t;
 if(last){var x=t-last;if(x<250)d.push(x);else{d=[];w0=0}}last=t;
 if(!w0)w0=t;
 if(t-w0>=1200){if(d.length>=4){d.sort(function(a,b){return a-b});if(d[d.length>>1]>34){if(++bad>=2){on(1);return}}else bad=0}d=[];w0=t}
 if(t-t00<60000)requestAnimationFrame(f)}
addEventListener('load',function(){setTimeout(function(){requestAnimationFrame(f)},2500)})})();
;
document.getElementById("tke-splash").onclick=function(){this.style.display="none"};

const $=i=>document.getElementById(i),hx=(n,l)=>(n>>>0).toString(16).toUpperCase().padStart(l,'0');
const M=new Uint8Array(1<<20),r=new Uint16Array(8),s=new Uint16Array(4);
let ip=0x2000,F=2,ov,rp,md,rg,rm,ea,sg,op,q,led=0,run=0,ex='',vw=0,st='i',cmd='',buf='',adr=0x2000,ri=0,lm=-1,lf=0,wc=0,wk=[],note='';
const wr=a=>{a=(a&1048575)>>4;const j=wk.indexOf(a);if(j>=0)wk.splice(j,1);wk.push(a);wk.length>256&&wk.shift()};
const io=new Uint8Array(65536);let bp=-1,bpk=0,wi=0,wv=[],tm='',pt=0,ci=0,mm=0,pq=0;
const rdp=p=>{p&=65535;return p==0||p==128?led:io[p]},wrp=(p,v)=>{p&=65535;v&=255;io[p]=v;if(p==0||p==128)led=v};
const pin=(p,w)=>w?rdp(p)|rdp(p+1)<<8:rdp(p),pout=(p,w)=>{wrp(p,r[0]);if(w)wrp(p+1,r[0]>>8)};
const A=(g,o)=>(g*16+(o&65535))&1048575;
const rb=a=>M[a],rw=a=>M[a]|M[a+1&1048575]<<8;
const wb=(a,x)=>{a<262144&&(M[a]=x)},ww=(a,x)=>{wb(a,x);wb(a+1&1048575,x>>8)};
const f8=()=>{const x=M[A(s[1],ip)];ip=ip+1&65535;return x},f16=()=>f8()|f8()<<8;
const gb=i=>i<4?r[i]&255:r[i-4]>>8;
const sb=(i,x)=>{i<4?r[i]=r[i]&65280|x&255:r[i-4]=r[i-4]&255|(x&255)<<8};
const sx=(x,w)=>w?x<<16>>16:x<<24>>24;
const pf=x=>{x&=255;x^=x>>4;x^=x>>2;x^=x>>1;return x&1?0:4};
const push=x=>{r[4]-=2;ww(A(s[2],r[4]),x)},pop=()=>{const x=rw(A(s[2],r[4]));r[4]+=2;return x};
const gE=w=>ea<0?(w?r[rm]:gb(rm)):(w?rw:rb)(A(sg,ea));
const pE=(w,x)=>ea<0?(w?(r[rm]=x):sb(rm,x)):(w?ww:wb)(A(sg,ea),x);
const gR=w=>w?r[rg]:gb(rg),pR=(w,x)=>w?(r[rg]=x):sb(rg,x);
const stop=(m,e)=>{run=0;ex=e||'HALt';note=m;pq=1};
const bad=()=>stop('Unsupported opcode '+hx(op,2)+' at '+hx(s[1],4)+':'+hx(q,4),'Err ');
const cc=c=>{const C=F&1,P=F&4,Z=F&64,S=F&128,O=F&2048;return[O,!O,C,!C,Z,!Z,C||Z,!(C||Z),S,!S,P,!P,!S!=!O,!S==!O,Z||!S!=!O,!Z&&!S==!O][c]};
function mr(){const m=f8();md=m>>6;rg=m>>3&7;rm=m&7;ea=-1;if(md==3)return;
 let b=[r[3]+r[6],r[3]+r[7],r[5]+r[6],r[5]+r[7],r[6],r[7],r[5],r[3]][rm],g=rm==2||rm==3||rm==6?2:3;
 if(md==0&&rm==6){b=f16();g=3}else if(md==1)b+=sx(f8(),0);else if(md==2)b+=f16();
 ea=b&65535;sg=ov<0?s[g]:s[ov]}
function alu(o,a,b,w){const m=w?65535:255,h=w?32768:128,c=o==2||o==3?F&1:0;let x,f=0;
 if(o==0||o==2){x=a+b+c;f=(x>m)|((a^b^x)&16)|(~(a^b)&(a^x)&h?2048:0)}
 else if(o==3||o==5||o==7){x=a-b-c;f=(x<0)|((a^b^x)&16)|((a^b)&(a^x)&h?2048:0)}
 else x=o==1?a|b:o==4?a&b:a^b;
 x&=m;F=F&~2261|f|(x?0:64)|(x&h?128:0)|pf(x);return x}
function sh(o,x,n,w){const m=w?65535:255,h=w?32768:128;let c;
 for(;n>0;n--){c=F&1;
  switch(o){
   case 0:x=(x<<1|(x&h?1:0))&m;F=F&~1|x&1;break;
   case 1:F=F&~1|x&1;x=x>>1|(x&1?h:0);break;
   case 2:F=F&~1|(x&h?1:0);x=(x<<1|c)&m;break;
   case 3:F=F&~1|x&1;x=x>>1|(c?h:0);break;
   case 5:F=F&~1|x&1;x>>=1;break;
   case 7:F=F&~1|x&1;x=x>>1|x&h;break;
   default:F=F&~1|(x&h?1:0);x=x<<1&m}}
 if(o>3)F=F&~196|(x?0:64)|(x&h?128:0)|pf(x);
 return x}
function g3(w){mr();const o=rg,m=w?65535:255,v=gE(w);
 if(o<2)alu(4,v,w?f16():f8(),w);
 else if(o==2)pE(w,~v&m);
 else if(o==3)pE(w,alu(5,0,v,w));
 else if(o<6){const S=o==5,a=w?r[0]:r[0]&255,x=S?sx(a,w)*sx(v,w):a*v,c=S?x!=sx(x&m,w):x>m;
  w?(r[0]=x,r[2]=x>>16):r[0]=x;F=F&~2049|(c?2049:0)}
 else{const d=w?(r[2]<<16|r[0])>>>0:r[0];let y,e;
  if(o==6){if(!v)return int(0);y=Math.floor(d/v);e=d%v;if(y>m)return int(0)}
  else{const sd=w?(r[2]<<16|r[0])|0:r[0]<<16>>16,sv=sx(v,w);if(!sv)return int(0);y=Math.trunc(sd/sv);e=sd%sv;if(y>m>>1||y<-(m>>1)-1)return int(0)}
  w?(r[0]=y,r[2]=e):r[0]=y&255|(e&255)<<8}}
function str(o){const w=o&1,k=o&254,d=(F&1024?-1:1)*(w?2:1),R=w?rw:rb,W=w?ww:wb;
 const one=()=>{const sa=A(ov<0?s[3]:s[ov],r[6]),da=A(s[0],r[7]);
  if(k==164){W(da,R(sa));r[6]+=d;r[7]+=d}
  else if(k==166){alu(7,R(sa),R(da),w);r[6]+=d;r[7]+=d}
  else if(k==170){W(da,w?r[0]:r[0]&255);r[7]+=d}
  else if(k==172){w?r[0]=R(sa):sb(0,R(sa));r[6]+=d}
  else{alu(7,w?r[0]:r[0]&255,R(da),w);r[7]+=d}};
 if(!rp)return one();
 while(r[1]){one();r[1]--;if((k==166||k==174)&&(rp==243)!=!!(F&64))break}}
function int(n){const vi=rw(n*4),vc=rw(n*4+2);if(!vi&&!vc){if(n==3){run=0;st='i';cmd='';buf='';ex=' CC ';pq=1;note='Program halted (CC)\nREG registers | GO run again';return}return stop('INT '+n+' executed - stopped')}push(F);push(s[1]);push(ip);F&=~768;ip=vi;s[1]=vc}
function step(){if(run){if(bpk)bpk=0;else if(bp>=0&&A(s[1],ip)==bp){run=0;ex=hx(ip,4)+'BrEA';note='Breakpoint hit at '+hx(bp,5)+'\nST step | GO resume | F1 edit';return}}
 ov=-1;rp=0;let w,a,b,t,o,x;q=ip;
 for(;;){op=f8();if(op==38)ov=0;else if(op==46)ov=1;else if(op==54)ov=2;else if(op==62)ov=3;else if(op>>1==121)rp=op;else if(op!=240)break}
 w=op&1;
 if(op<64&&(op&7)<6){o=op>>3;t=op&7;
  if(t<4){mr();if(t<2){a=gE(w);b=gR(w)}else{a=gR(w);b=gE(w)}x=alu(o,a,b,w);if(o<7)t<2?pE(w,x):pR(w,x)}
  else{x=alu(o,w?r[0]:r[0]&255,w?f16():f8(),w);if(o<7)w?r[0]=x:sb(0,x)}}
 else if(op<64&&(op&7)>5&&!(op&32))op&1?(s[op>>3&3]=pop()):push(s[op>>3&3]);
 else if(op==39||op==47){const d=op==47?-1:1,ol=r[0]&255,oc=F&1;let l=ol,c=0;
  if((l&15)>9||F&16){l+=6*d;c=oc||l>255||l<0;F|=16}else F&=~16;
  if(ol>153||oc){l+=96*d;c=1}
  l&=255;sb(0,l);F=F&~197|(c?1:0)|(l?0:64)|(l&128)|pf(l)}
 else if(op==55||op==63){const d=op==63?-1:1;let l=r[0]&255,h=r[0]>>8,c=0;
  if((l&15)>9||F&16){l+=6*d;h+=d;c=1}
  r[0]=(h&255)<<8|l&15;F=F&~17|(c?17:0)}
 else if(op>63&&op<80){t=F&1;r[op&7]=alu(op<72?0:5,r[op&7],1,1);F=F&~1|t}
 else if(op>79&&op<96)op<88?push(r[op&7]):(r[op&7]=pop());
 else if(op>111&&op<128){b=f8();if(cc(op&15))ip=ip+sx(b,0)&65535}
 else if(op>127&&op<132){mr();a=gE(w);b=op==129?f16():op==131?sx(f8(),0)&65535:f8();x=alu(rg,a,b,w);if(rg<7)pE(w,x)}
 else if(op==132||op==133){mr();alu(4,gE(w),gR(w),w)}
 else if(op==134||op==135){mr();a=gE(w);pE(w,gR(w));pR(w,a)}
 else if(op==136||op==137){mr();pE(w,gR(w))}
 else if(op==138||op==139){mr();pR(w,gE(w))}
 else if(op==140){mr();pE(1,s[rg&3])}
 else if(op==141){mr();r[rg]=ea}
 else if(op==142){mr();s[rg&3]=gE(1)}
 else if(op==143){mr();pE(1,pop())}
 else if(op==144);
 else if(op>144&&op<152){a=r[0];r[0]=r[op&7];r[op&7]=a}
 else if(op==152)r[0]=r[0]<<24>>24;
 else if(op==153)r[2]=r[0]&32768?65535:0;
 else if(op==156)push(F|2);
 else if(op==157)F=pop()&4095|2;
 else if(op==158)F=F&~213|r[0]>>8&213;
 else if(op==159)r[0]=r[0]&255|(F&213|2)<<8;
 else if(op>159&&op<164){a=A(ov<0?s[3]:s[ov],f16());op<162?(w?(r[0]=rw(a)):sb(0,rb(a))):(w?ww(a,r[0]):wb(a,r[0]))}
 else if(op==168||op==169)alu(4,w?r[0]:r[0]&255,w?f16():f8(),w);
 else if(op>163&&op<176)str(op);
 else if(op>175&&op<184)sb(op&7,f8());
 else if(op>183&&op<192)r[op&7]=f16();
 else if(op==194||op==195){b=op==194?f16():0;ip=pop();r[4]+=b}
 else if(op==202||op==203){b=op==202?f16():0;ip=pop();s[1]=pop();r[4]+=b}
 else if(op==198||op==199){mr();pE(w,w?f16():f8())}
 else if(op==196||op==197){mr();r[rg]=rw(A(sg,ea));s[op&1?3:0]=rw(A(sg,ea+2))}
 else if(op==206){if(F&2048)int(4)}
 else if(op==212||op==213){b=f8();
  if(op==212){if(!b)return int(0);x=r[0]&255;r[0]=(x/b|0)<<8|x%b}
  else r[0]=((r[0]>>8)*b+r[0])&255;
  x=r[0]&255;F=F&~196|(x?0:64)|(x&128)|pf(x)}
 else if(op==154){b=f16();x=f16();push(s[1]);push(ip);ip=b;s[1]=x}
 else if(op==204)int(3);
 else if(op==205)int(f8());
 else if(op==207){ip=pop();s[1]=pop();F=pop()&4095|2}
 else if(op>207&&op<212){mr();b=op&2?r[1]&255:1;pE(w,sh(rg,gE(w),b,w))}
 else if(op==215)sb(0,rb(A(ov<0?s[3]:s[ov],r[3]+(r[0]&255))));
 else if(op>223&&op<228){b=sx(f8(),0);if(op==227?!r[1]:(r[1]--,op==226?r[1]:op==225?r[1]&&F&64:r[1]&&!(F&64)))ip=ip+b&65535}
 else if(op>>1==114){x=pin(f8(),w);w?(r[0]=x):sb(0,x)}
 else if(op>>1==115)pout(f8(),w);
 else if(op>>1==118){x=pin(r[2],w);w?(r[0]=x):sb(0,x)}
 else if(op>>1==119)pout(r[2],w);
 else if(op==232){b=f16();push(ip);ip=ip+b&65535}
 else if(op==233){b=f16();ip=ip+b&65535}
 else if(op==234){b=f16();x=f16();ip=b;s[1]=x}
 else if(op==235){b=sx(f8(),0);ip=ip+b&65535}
 else if(op==244)stop('HLT executed - program halted');
 else if(op==245)F^=1;else if(op==248)F&=~1;else if(op==249)F|=1;
 else if(op==250)F&=~512;else if(op==251)F|=512;else if(op==252)F&=~1024;else if(op==253)F|=1024;
 else if(op==246||op==247)g3(w);
 else if(op==254||op==255){mr();
  if(rg<2){t=F&1;pE(w,alu(rg?5:0,gE(w),1,w));F=F&~1|t}
  else if(w&&rg==2){a=gE(1);push(ip);ip=a}
  else if(w&&rg==4)ip=gE(1);
  else if(w&&(rg==3||rg==5)&&ea>=0){a=rw(A(sg,ea));x=rw(A(sg,ea+2));if(rg==3){push(s[1]);push(ip)}ip=a;s[1]=x}
  else if(w&&rg==6)push(gE(1));
  else bad()}
 else bad()}
/* ---- monitor / keypad ---- */
const CM=['EB','ER','GO','ST','IB','OB','MV','EW','IW','OW','','','BC','LS','VR','PRG'];
const RN=['AX','BX','CX','DX','SP','BP','SI','DI','CS','DS','SS','ES','IP','FL'],MAP=[0,3,1,2,4,5,6,7],SM=[1,3,2,0];
const G={0:63,1:6,2:91,3:79,4:102,5:109,6:125,7:7,8:127,9:111,A:119,B:124,C:57,D:94,E:121,F:113,'-':64,S:109,I:6,r:80,o:92,H:118,P:115,n:84,t:120,L:56,U:62,u:28};
const RD=['A','B','C','D','SP','BP','SI','DI','CS','DS','SS','ES','IP','FL'];
const rget=i=>i<8?r[MAP[i]]:i<12?s[SM[i-8]]:i==12?ip:F;
const rset=(i,x)=>{x&=65535;if(i<8)r[MAP[i]]=x;else if(i<12)s[SM[i-8]]=x;else if(i==12)ip=x;else F=x};
const dsp=$('dsp');
dsp.innerHTML=('<svg viewBox="-1 -1 16 22">'+[[2,0,8,2],[10,2,2,7],[10,11,2,7],[2,18,8,2],[0,11,2,7],[0,2,2,7],[2,9,8,2]].map(e=>`<rect x=${e[0]} y=${e[1]} width=${e[2]} height=${e[3]} rx=1 />`).join('')+'<circle cx=13.7 cy=19 r=1.3 /></svg>').repeat(8);
$('led').innerHTML='<i></i>'.repeat(8);
function show(a,d,dp){const t=a+d;dsp.querySelectorAll('svg').forEach((e,i)=>{e.querySelectorAll('rect').forEach((p,j)=>p.classList.toggle('on',((G[t[i]]||0)>>j&1)==1));e.querySelector('circle').classList.toggle('on',!!dp&&i==3)})}
const MK='EB/EW edit | GO run | ST step | REG',MON='Monitor Ready\n'+MK;
function ui(){let a,d,n=note;
 if(run){a='----';d='rUn ';n='Running...\nRESET stops it'}
 else if(ex){a=ex.length>4?ex.slice(0,4):ex==' CC '?hx(ip,4):'----';d=ex.length>4?ex.slice(4):ex}
 else if(st=='i'){a=vw?hx(ip,4):pq?'-   ':'8086';d=vw?'  '+hx(M[A(s[1],ip)],2):pq?'    ':' uP '}
 else if(st=='addr'){a=buf?buf.padStart(4):'----';d='    ';n=cmd=='GO'?'GO: type the address\nthen TTY to run':cmd+': type the address\nthen NEXT'}
 else if(st=='gor'){a=hx(adr,4);d='    ';n='GO @ '+hx(adr,4)+'\nTTY to run'}
 else if(st=='data'){a=hx(adr,4);d=(buf||(cmd=='EW'?hx(rw(adr),4):hx(rb(adr),2))).padStart(4);n=cmd+' @ '+hx(adr,5)+': type '+(cmd=='EW'?'word':'byte')+'\nNEXT save | PRV back | TTY exit'}
 else if(st=='rdy'){a=buf?buf.padStart(4):'----';d='    ';n=buf?'Address: '+buf+(buf.length>3?' | Press GO (key 2) then TTY to execute':' | Type 4 hex digits, then GO (key 2)'):'Type the 4-digit start address, then GO (key 2 or G) and TTY'}
 else if(st=='wz'){const W=WZ[cmd],P=W.p[wi],v=dv(wi);a=P.l;d=(buf||(v===undefined||v<0?'----':hx(v,P.n))).padStart(4);n=wzNote()}
 else if(st=='io'){const w=cmd=='IW',v=pin(pt,w);a=hx(pt,4);d=w?hx(v,4):'  '+hx(v,2);
  n=cmd+' port '+hx(pt,4)+'h = '+hx(v,w?4:2)+'h'+(w?'':' ('+v.toString(2).padStart(8,'0')+'b)')+'\nNEXT/PRV next or previous port\nor type another port address | TTY exit'}
 else if(st=='dmp'){const row=p=>hx(p&65535,4)+': '+Array.from({length:8},(_,i)=>hx(M[p+i],2)).join(' ');
  a=hx(adr,4);d=hx(M[adr],2)+hx(M[adr+1],2);n='DUMP | NEXT/PRV = 16 bytes | TTY exit\n'+row(adr)+'\n'+row(adr+8)}
 else if(st=='cmp'){const x=wv[0]+ci,y=wv[2]+ci;a=hx(x&65535,4);d=hx(M[x],2)+hx(M[y],2);
  n=cmd+' mismatch #'+mm+'\n'+hx(x&65535,4)+': '+hx(M[x],2)+' | '+hx(y&65535,4)+': '+hx(M[y],2)+'\nNEXT finds the next | TTY stops'}
 else{a=st=='regv'?RD[ri].padStart(4):'----';d=st=='regv'?(buf||hx(rget(ri),4)).padStart(4):'    ';n=st=='reg'?'REG: press a register key\nname after the / on the key':RN[ri]+': type hex value\nNEXT save | PRV back | TTY exit'}
 if(tm&&!run&&!ex)n=tm+'\n'+n;show(a,d,!run&&!ex&&(st!='i'||vw));$('stat').textContent=n;
 $('regs').innerHTML=RN.map((e,i)=>`<div>${e} <b>${hx(rget(i),4)}</b></div>`).join('')+(bp>=0?`<div>BRK <b>${hx(bp,4)}</b></div>`:'');
 $('fl').innerHTML=[['OF',2048],['DF',1024],['IF',512],['TF',256],['SF',128],['ZF',64],['AF',16],['PF',4],['CF',1]].map(e=>`<span class="${F&e[1]?'on':''}">${e[0]}</span>`).join('');
 [...$('led').children].forEach((e,i)=>e.classList.toggle('on',(led>>(7-i)&1)==1));
 if(!wc){if(st=='data'||st=='dmp'){lm=adr&1048575;wk=[];wr(lm);wr(lm+(st=='dmp'?15:cmd=='EW'?1:0))}else if(st=='cmp'){lm=(wv[0]+ci)&1048575;wk=[];wr(lm)}}
 const hl=lm,rows=wk.length?[...wk].sort((a,b)=>a-b):[0,1,2,3,4,5,6,7];let h='',pv=-2;
 rows.forEach(r=>{if(pv>=0&&r!=pv+1)h+='<s class=dots>\u22EE</s>\n';pv=r;const bs=r<<4;h+='<s>'+hx(bs,5)+'</s>: ';for(let i=0;i<16;i++){const p=bs+i;h+=(p==hl?'<b>'+hx(M[p],2)+'</b>':hx(M[p],2))+' '}h+='\n'});
 $('mem').innerHTML=h.replace(/\n$/,'')}
/* RESET restarts the monitor only: memory, registers and flags are kept. POWER clears everything. */
function reset(){run=0;led=0;io.fill(0);wv=[];wi=0;tm='';st='i';cmd='';buf='';ex='';vw=0;pq=0;note=MON;ui()}
function power(q){run=0;M.fill(0);r.fill(0);s.fill(0);r[4]=0x3FFE;ip=0x2000;F=2;adr=0x2000;lm=-1;lf=1;wk=[];bp=-1;bpk=0;pt=0;ci=0;mm=0;reset();
 if(!q){const d=$('dsp');d.classList.add('pof');clearTimeout(power.t);power.t=setTimeout(()=>d.classList.remove('pof'),450)}}
function go(){run=1;(function t(){if(run){for(let i=0;i<40000&&run;i++)step();ui();if(run)setTimeout(t,0)}})()}
function cm(){if(!buf)return;const x=parseInt(buf,16);if(st=='data')cmd=='EW'?ww(adr,x):wb(adr,x);else if(st=='regv')rset(ri,x);buf=''}
function key(k){
 if(k=='RESET')return reset();
 if(run)return;
 vw=0;ex='';tm='';const isHex=typeof k=='number';if(k=='.')pq=1;if(ext(k,isHex))return;

 if(k=='BS'){buf=buf.slice(0,-1);return ui()}

 // 1. TTY / . Key Handling
 if(k=='.'){
  if(st=='data'){
   cm();st='i';buf='';cmd='';note='Saved. '+MON;
  }else if(st=='gor'){
   ip=adr&65535;buf='';cmd='';st='i';go();return;
  }else if(st=='addr'&&cmd=='GO'&&buf){
   /* GO + address + TTY runs the program directly (NEXT is optional) */
   adr=parseInt(buf,16);ip=adr&65535;buf='';cmd='';st='i';go();return;
  }else if(st=='addr'&&cmd=='GO'){
   /* no address typed yet: stay in GO */
  }else if(st=='addr'||st=='rdy'||st=='i'){
   st='i';buf='';cmd='';note=MON;
  }else if(st=='reg'||st=='regv'){
   cm();st='i';buf='';cmd='';note=MON;
  }
  return ui();
 }

 // 2. NEXT & PRV Keys
 if(k=='NEXT'||k=='PRV'){
  const d=k=='NEXT'?1:-1;
  if(st=='addr'){
   if(cmd=='GO'){if(k=='NEXT'&&buf){adr=parseInt(buf,16);buf='';st='gor'}return ui()}
   if(buf)adr=parseInt(buf,16);
   buf='';
   st='data';
  }else if(st=='data'){
   cm();adr=(adr+d*(cmd=='EW'?2:1))&1048575;
  }else if(st=='regv'){
   cm();ri=(ri+d+14)%14;
  }
  return ui();
 }

 // 3. Command Keys Handling
 if(k=='REG'){st='reg';buf='';return ui()}
 
 if(k=='GO'||(!isHex&&k=='GO')){
  if(st!='i'&&st!='rdy'&&st!='addr')buf='';
  cmd='GO';st='addr';
  note='GO: type the address\nthen TTY to run';
  return ui();
 }

 // Check for Key 2 pressed when Buffer is already full (4 hex digits) -> Treat as GO
 if(isHex&&k==2&&(st=='rdy'||st=='i')&&buf.length>=4){
  cmd='GO';st='addr';
  note='GO: type the address\nthen TTY to run';
  return ui();
 }

 // Hardware Functions / Opcodes on Keypad
 if(!isHex&&k in CM)k=CM.indexOf(k);

 if(st=='i'&&isHex&&buf===''){
  const c=CM[k];
  if(c=='ST'){note='Stepped: next IP + opcode\nST again | REG registers';step();vw=1;return ui()}
  if(c=='ER'){st='reg';return ui()}
  if(c=='EB'||c=='EW'){st='addr';cmd=c;buf='';return ui()}
  if(c=='GO'){st='addr';cmd='GO';buf='';return ui()}
 }

 // 4. Hex Input (0-9, A-F)
 if(isHex){
  if(st=='reg'){
   if(k<14){ri=k;st='regv';buf=''}
  }else if(st=='i'){
   note='Key '+hx(k,1)+(CM[k]?' ('+CM[k]+')':'')+' is not active now.\nTry commands like EB, GO, ST, REG...';
  }else if(st=='gor'){
   st='addr';buf=hx(k,1);
  }else if(st=='rdy'||st=='addr'){
   buf=(buf+hx(k,1)).slice(-4);
  }else if(st=='data'){
   buf=(buf+hx(k,1)).slice(cmd=='EW'?-4:-2);
  }else if(st=='regv'){
   buf=(buf+hx(k,1)).slice(-4);
  }
 }
 ui();
}

/* ---- extended monitor commands: INS/DEL, FILL, MV, BC, VR, IB/IW, OB/OW, VCT/INTR, F1-F3 ---- */
const WC={4:'IB',5:'OB',6:'MV',8:'IW',9:'OW',12:'BC',14:'VR'},FK={PRV:'FILL',VCT:'INTR',F1:'BRK',F2:'DUMP',F3:'HOOK'};
const PA=(l,h,o)=>({l,n:4,h,o}),PB=(l,h)=>({l,n:2,h});
const blk=(v,i)=>i==1&&v<wv[0]?'End address is below the\nstart address ('+hx(wv[0],4)+')':'';
const sgn=(v,n)=>v<0?'--':hx(v,n);
const done=(m,c)=>{st='i';cmd='';buf='';wv=[];wi=0;ex=c||'';pq=1;note=m+'\n'+MK};
const err=m=>{ex='Err ';note=m;buf=''};
const dv=i=>{const W=WZ[cmd],d=W.def?W.def(i):undefined;return d!==undefined?d:wv[i]};
function cmpNext(){const[s0,e0,d0]=wv,n=e0-s0+1;
 for(ci++;ci<n;ci++)if(M[s0+ci]!=M[d0+ci]){mm++;st='cmp';return}
 mm?done(cmd+' finished: '+mm+' mismatch'+(mm>1?'es':''),hx(e0,4)+'EnD '):done(cmd+' PASS: '+n+' bytes identical',hx(e0,4)+'PASS')}
function fire(n){
 if(r[4]<6)return err('Stack too low for INTR\n(SP='+hx(r[4],4)+', needs 6 bytes)');
 const vi=rw(n*4),vc=rw(n*4+2);
 if(!vi&&!vc)return err('Vector '+hx(n,2)+'h is empty (IVT '+hx(n*4,4)+')\nHook one with F3, or EW at '+hx(n*4,4));
 push(F|2);push(s[1]);push(ip);F&=~768;ip=vi;s[1]=vc;
 done('INTR '+hx(n,2)+'h: FL, CS, IP pushed\nCS:IP = '+hx(vc,4)+':'+hx(vi,4)+' | SP = '+hx(r[4],4));vw=1}
const WZ={
 FILL:{p:[PA('SA  ','start address'),PA('EA  ','end address'),PB('DAtA','fill byte')],chk:blk,
  run(){const[a,b,v]=wv;M.fill(v,a,b+1);done('FILL done: '+hx(a,4)+'-'+hx(b,4)+' = '+hx(v,2)+'h',hx(b,4)+'DonE')}},
 MV:{p:[PA('SA  ','source start'),PA('EA  ','source end'),PA('DESt','destination start')],
  chk:(v,i)=>blk(v,i)||(i==2&&v+wv[1]-wv[0]>262143?'Destination leaves RAM\n(RAM is 00000-3FFFF)':''),
  run(){const[a,b,d]=wv;M.copyWithin(d,a,b+1);done('MV done: '+hx(a,4)+'-'+hx(b,4)+' -> '+hx(d,4)+'\n'+(b-a+1)+' bytes copied',hx(d+b-a&65535,4)+'DonE')}},
 BC:{p:[PA('SA  ','1st block start'),PA('EA  ','1st block end'),PA('SA2 ','2nd block start')],chk:blk,run(){ci=-1;mm=0;cmpNext()}},
 VR:{p:[PA('SA  ','block start'),PA('EA  ','block end'),PA('SA2 ','block to verify against')],chk:blk,run(){ci=-1;mm=0;cmpNext()}},
 IB:{p:[PA('Port','port address')],run(){pt=wv[0];st='io'}},
 IW:{p:[PA('Port','port address')],run(){pt=wv[0];st='io'}},
 OB:{p:[PA('Port','port address'),PB('DAtA','byte to write')],keep:1,def:i=>i==1?rdp(wv[0]):undefined,
  run(){const p=wv[0],v=wv[1];wrp(p,v);tm='OUT '+hx(p,4)+'h <- '+hx(v,2)+'h'+(p==0||p==128?' (LEDs)':'')}},
 OW:{p:[PA('Port','port address'),PA('DAtA','word to write')],keep:1,def:i=>i==1?pin(wv[0],1):undefined,
  run(){const p=wv[0],v=wv[1];wrp(p,v);wrp(p+1,v>>8);tm='OUT '+hx(p,4)+'h <- '+hx(v,4)+'h'+([p,p+1&65535].some(x=>x==0||x==128)?' (LEDs)':'')}},
 INTR:{p:[PB('Intr','vector type (00-FF)')],run(){fire(wv[0])}},
 BRK:{p:[PA('BrEA','address (empty = clear)',1)],
  run(){const v=wv[0];if(v<0){bp=-1;done('Breakpoint cleared','---- CLr')}else{bp=v;done('Breakpoint set at '+hx(v,4)+'\nGO stops just before it',hx(v,4)+' SEt')}}},
 DUMP:{p:[PA('ADDr','address (empty = IP)',1)],run(){adr=wv[0]<0?A(s[1],ip)&65535:wv[0];st='dmp'}},
 HOOK:{p:[PB('Intr','INT type to hook'),PA('ADDr','handler (empty = unhook)',1)],
  run(){const n=wv[0],h=wv[1],a=n*4,z=h<0;
   wb(a,z?0:h);wb(a+1,z?0:h>>8);wb(a+2,z?0:s[1]);wb(a+3,z?0:s[1]>>8);
   done(z?'INT '+hx(n,2)+'h unhooked (IVT cleared)':'INT '+hx(n,2)+'h -> '+hx(s[1],4)+':'+hx(h,4)+(n==3?'\nCC now calls this handler':''),'  '+hx(n,2)+(z?'----':hx(h,4)))}}
};
function wzNote(){const W=WZ[cmd],L=W.p.length,ks=W.keep&&wi==L-1,P=W.p[wi],
 pv=W.p.slice(0,wi).map((z,i)=>z.l.trim()+'='+sgn(wv[i],z.n)).join('  ');
 return cmd+' '+(wi+1)+'/'+L+': '+P.h+(pv?'\n'+pv:'')+'\nNEXT '+(ks?'write':'ok')+(wi?' | PRV back':'')+' | TTY '+(ks?'exit':'cancel')}
function wzNext(){const W=WZ[cmd],P=W.p[wi];let v;
 if(buf!=='')v=parseInt(buf,16);
 else{v=dv(wi);if(v===undefined){if(!P.o)return err('Type the '+P.h+',\nthen press NEXT');v=-1}}
 const e=W.chk&&W.chk(v,wi);if(e)return err(e);
 wv[wi]=v;buf='';
 if(wi<W.p.length-1){wi++;return}
 W.run()}
/* returns 1 when the key was fully handled here, 0 to fall through to the original key logic */
function ext(k,isHex){
 if(k=='INS'||k=='DEL'){
  if(st!='data'){tm=k+' only works in Data Mode.\n(EB/EW -> Address -> NEXT -> '+k+')';ui();return 1}
  if(adr>262143){err('Address '+hx(adr,5)+' is not RAM\nRAM is 00000-3FFFF');ui();return 1}
  const e=Math.min(adr|16383,262143),p=hx(adr&65535,4),z=hx(e&65535,4);
  if(k=='INS'){M.copyWithin(adr+1,adr,e);M[adr]=0;tm='INS: '+p+'-'+z+' moved up, 00h at '+p}
  else{M.copyWithin(adr,adr+1,e+1);M[e]=0;tm='DEL: '+p+'-'+z+' moved down, '+z+' = 00h'}
  buf='';
  ui();return 1}
 if(st=='i'&&buf===''){const c=isHex?WC[k]:FK[k];if(c){cmd=c;st='wz';wi=0;wv=[];buf='';ui();return 1}return 0}
 if(k=='VCT'||k=='F1'||k=='F2'||k=='F3'){tm='Finish your current step first,\nor press TTY (.) to cancel';ui();return 1}
 if(st=='wz'){const W=WZ[cmd],P=W.p[wi];
  if(k=='.'){done(cmd+(W.keep&&wi==W.p.length-1?' finished':' cancelled'));ui();return 1}
  if(k=='NEXT'){wzNext();ui();return 1}
  if(k=='PRV'){if(wi){wi--;buf=''}else tm='Already at the first prompt\nTTY cancels '+cmd;ui();return 1}
  if(isHex){buf=(buf+hx(k,1)).slice(-P.n);ui();return 1}
  if(k=='BS')return 0;
  tm=cmd+' is active. Finish your step,\nor press TTY (.) to cancel';ui();return 1}
 if(st=='io'){
  if(k=='.'){done(cmd+' finished');ui();return 1}
  if(k=='NEXT'||k=='PRV'){const d=cmd=='IW'?2:1;pt=pt+(k=='NEXT'?d:-d)&65535;ui();return 1}
  if(isHex){st='wz';wi=0;wv=[];buf=hx(k,1);ui();return 1}
  if(k=='BS')return 0;
  tm='NEXT/PRV step the port, TTY exits';ui();return 1}
 if(st=='dmp'){
  if(k=='.'){done('DUMP finished');ui();return 1}
  if(k=='NEXT'||k=='PRV'){adr=adr+(k=='NEXT'?16:-16)&65535;ui();return 1}
  if(isHex){st='wz';wi=0;wv=[];buf=hx(k,1);ui();return 1}
  if(k=='BS')return 0;
  tm='NEXT/PRV page the dump, TTY exits';ui();return 1}
 if(st=='cmp'){
  if(k=='.'){const c=cmd,m=mm;done(c+' stopped: '+m+' mismatch'+(m>1?'es':'')+' so far');ui();return 1}
  if(k=='NEXT'){cmpNext();ui();return 1}
  if(k=='BS')return 0;
  tm='NEXT finds the next difference,\nTTY stops';ui();return 1}
 return 0}

function ld(t){const b=($('hx').value.match(/[0-9a-f]{2}/gi)||[]).map(e=>parseInt(e,16)),a=parseInt($('ha').value,16);
 if(isNaN(a)){note='Type a load address first\n(hex, in the Load a program box)';$('ha').focus();return ui()}
 b.forEach((e,i)=>wb(a+i,e));adr=a;wk=[];for(let q=0;q<b.length;q+=16)wr(a+q);if(b.length)wr(a+b.length-1);lm=a&1048575;lf=1;ip=a&65535;s[1]=0;st='i';cmd='';buf='';ex='';vw=0;run=0;note=(typeof t=='string'?t+'\n':'')+'Loaded '+b.length+' bytes at '+hx(a,4)+'\nRun: GO, '+hx(a,4)+', TTY';ui()}
$('ld').onclick=ld;
(()=>{const D=[['Sum 1\u201310','B8 00 00 B9 0A 00 01 C8 E2 FC A3 00 21 E6 80 CC'],
['Fibonacci','BF 40 20 B9 0C 00 B3 00 B0 01 88 05 47 88 C2 00 D8 88 D3 E2 F5 88 D8 E6 80 CC'],
['Max of 5','BE 17 20 B9 05 00 B0 00 3A 04 73 02 8A 04 46 E2 F7 A2 00 21 E6 80 CC 12 45 A7 3C 8E']];
let n=0;const b=$('dm'),tg=i=>'Demo '+(i+1)+'/'+D.length,lab=()=>b.textContent=tg(n)+' \u00b7 '+D[n][0];
b.onclick=()=>{$('ha').value='2000';$('hx').value=D[n][1];ld(tg(n)+': '+D[n][0]);n=(n+1)%D.length;lab()};
lab();
$('lc').onclick=()=>{$('ha').value='';$('hx').value=''}})();
const LB=['RESET','VCT|INTR','F3','INS|+','DEL|-','F2','REG','B.S|:','F1','FILL|PRV','CRT|NEXT','TTY|.'],
BA=['RESET','VCT','F3','INS','DEL','F2','REG','BS','F1','PRV','NEXT','.'],BK=[12,13,14,15,8,9,10,11,4,5,6,7,0,1,2,3];
let kh='';
for(let i=0;i<4;i++){
 for(let j=0;j<3;j++)kh+=`<button class=b data-k="${BA[i*3+j]}">${LB[i*3+j].replace('|','<br>')}</button>`;
 for(let j=0;j<4;j++){const k=BK[i*4+j];kh+=`<button class=k data-k="${k}"><b>${hx(k,1)}</b><small>${CM[k]}/${RN[k]||''}</small></button>`}}
$('keys').innerHTML=kh;
$('keys').onclick=e=>{const b=e.target.closest('button');if(b){const k=b.dataset.k;key(/^\d+$/.test(k)?+k:k);b.blur()}};
document.onkeydown=e=>{if(/^(TEXTAREA|INPUT)$/.test(e.target.tagName)||(e.key=='Enter'&&e.target.tagName=='SUMMARY')||e.ctrlKey||e.metaKey||e.altKey)return;const c=e.key;
 if(/^[0-9a-f]$/i.test(c)){key(parseInt(c,16));e.preventDefault()}
 else{const m={Enter:'NEXT',Backspace:'BS','-':'PRV','.':'.',Escape:'RESET',g:'GO',G:'GO',Insert:'INS','+':'INS',Delete:'DEL',v:'VCT',V:'VCT',F1:'F1',F2:'F2',F3:'F3'}[c];if(m){key(m);e.preventDefault()}}};
power(1);
$('pwr').onclick=()=>power();

(()=>{const g=i=>document.getElementById(i),t=g('asm'),l=g('ln'),i=g('asi');
const S=['; Sum of 1..10  ->  [2100h] and port 80h','        ORG  2000h','        MOV  AX, 0','        MOV  CX, 10','AGAIN:  ADD  AX, CX','        LOOP AGAIN','        MOV  [2100h], AX','        OUT  80h, AL','        INT  3',''].join('\n');
const u=()=>{const n=t.value.split('\n').length;l.textContent=Array.from({length:n},(_,k)=>k+1).join('\n');i.textContent=n+' lines \u00b7 '+t.value.length+' chars';l.scrollTop=t.scrollTop};
t.addEventListener('input',u);t.addEventListener('scroll',()=>{l.scrollTop=t.scrollTop});
t.addEventListener('keydown',e=>{if(e.key==='Tab'){e.preventDefault();t.setRangeText('\t',t.selectionStart,t.selectionEnd,'end');u()}});
g('asx').onclick=()=>{t.value='';u();t.focus()};
g('asc').onclick=()=>{t.select();(navigator.clipboard?navigator.clipboard.writeText(t.value):Promise.reject()).catch(()=>document.execCommand('copy'))};
g('ass').onclick=()=>{const a=document.createElement('a');a.href=URL.createObjectURL(new Blob([t.value],{type:'text/plain'}));a.download='program.asm';a.click()};
t.value=S;u()})();

(()=>{
const g=i=>document.getElementById(i),H=(n,l)=>(n>>>0).toString(16).toUpperCase().padStart(l,'0');
const R16='AX CX DX BX SP BP SI DI'.split(' '),R8='AL CL DL BL AH CH DH BH'.split(' '),SR='ES CS SS DS'.split(' ');
const ALU={ADD:0,OR:1,ADC:2,SBB:3,AND:4,SUB:5,XOR:6,CMP:7},SHF={ROL:0,ROR:1,RCL:2,RCR:3,SHL:4,SAL:4,SHR:5,SAR:7},UNA={NOT:2,NEG:3,MUL:4,IMUL:5,DIV:6,IDIV:7};
const NO={NOP:[144],HLT:[204],CLC:[248],STC:[249],CMC:[245],CLD:[252],STD:[253],CLI:[250],STI:[251],CBW:[152],CWD:[153],LAHF:[159],SAHF:[158],PUSHF:[156],POPF:[157],XLAT:[215],XLATB:[215],DAA:[39],DAS:[47],AAA:[55],AAS:[63],AAM:[212,10],AAD:[213,10],RET:[195],RETF:[203],IRET:[207],INTO:[206],MOVSB:[164],MOVSW:[165],CMPSB:[166],CMPSW:[167],STOSB:[170],STOSW:[171],LODSB:[172],LODSW:[173],SCASB:[174],SCASW:[175]};
const PF={REP:243,REPE:243,REPZ:243,REPNE:242,REPNZ:242,LOCK:240};
const JCC='JO JNO JB JAE JE JNE JBE JA JS JNS JP JNP JL JGE JLE JG'.split(' '),ALS={JC:'JB',JNAE:'JB',JNB:'JAE',JNC:'JAE',JZ:'JE',JNZ:'JNE',JNA:'JBE',JNBE:'JA',JPE:'JP',JPO:'JNP',JNGE:'JL',JNL:'JGE',JNG:'JLE',JNLE:'JG'};
const LP={LOOPNE:224,LOOPNZ:224,LOOPE:225,LOOPZ:225,LOOP:226,JCXZ:227};
let L={},V={},cur=0,ur='';
const xp=s=>{const t=s.match(/\d+|<<|>>|[-+*\/%()&|^~]/g)||[],P={'|':1,'^':2,'&':3,'<<':4,'>>':4,'+':5,'-':5,'*':6,'/':6,'%':6};let i=0;
 const pr=()=>{const c=t[i++];if(c=='('){const v=ex(0);i++;return v}if(c=='-')return-pr();if(c=='+')return pr();if(c=='~')return~pr();if(c===undefined||!/^\d/.test(c))throw'Bad value';return+c};
 const ex=m=>{let a=pr(),o;while((o=t[i])&&P[o]>m){i++;const b=ex(P[o]);a=o=='+'?a+b:o=='-'?a-b:o=='*'?a*b:o=='/'?(b?a/b|0:0):o=='%'?(b?a%b:0):o=='&'?a&b:o=='|'?a|b:o=='^'?a^b:o=='<<'?a<<b:a>>b}return a};
 const v=ex(0);if(i<t.length)throw'Bad value';return v|0};
const ev=s=>{s=s.replace(/\b(offset|short|near)\b/gi,'').replace(/0x[0-9a-f]+|[0-9][0-9a-f]*h\b|[01]+b\b|\d+|'.'|"."|\$|[a-z_.?@][\w.?@]*/gi,t=>{
 if(t=='$')return cur;if(t[0]=="'"||t[0]=='"')return t.charCodeAt(1);
 if(/^0x/i.test(t)||/^\d.*h$/i.test(t))return parseInt(t,16);
 if(/^[01]+b$/i.test(t))return parseInt(t,2);if(/^\d/.test(t))return parseInt(t,10);
 const v=L[t.toUpperCase()];if(v===undefined){if(/^[0-9a-f]+h$/i.test(t))return parseInt(t,16);ur=ur||t;return 0}return v});
 if(!/^[\d\s+\-*\/%()<>&|^~]*$/.test(s))throw'Bad value: '+s.trim();return xp(s)};
const po=t=>{let m,z=0,sg=-1;t=t.trim();
 if(m=t.match(/^(byte|word)\b(\s+ptr\b)?\s*/i)){z=/^b/i.test(m[1])?1:2;t=t.slice(m[0].length)}
 if(m=t.match(/^(es|cs|ss|ds)\s*:\s*/i)){sg=SR.indexOf(m[1].toUpperCase());t=t.slice(m[0].length)}
 const u=t.toUpperCase();let n;
 if((n=R16.indexOf(u))>=0)return{k:'r',n,z:2};
 if((n=R8.indexOf(u))>=0)return{k:'r',n,z:1};
 if((n=SR.indexOf(u))>=0)return{k:'s',n};
 if(m=t.match(/^([^\[]*)\[(.*)\]$/)){const rs=[],e=m[2]+(m[1].trim()?'+'+m[1]:''),d=ev(e.replace(/\b(bx|bp|si|di)\b/ig,a=>(rs.push(a.toUpperCase()),'0'))),rm={'BP,DI':3,'BP,SI':2,'BX,DI':1,'BX,SI':0,SI:4,DI:5,BP:6,BX:7}[rs.sort().join()];
  if(!rs.length)return{k:'m',rm:6,md:0,dl:2,d,dir:1,z,g:sg};
  if(rm===undefined)throw'Bad address: '+t;
  const md=d==0&&rm!=6?0:d>=-128&&d<128?1:2;return{k:'m',rm,md,dl:md,d,z,g:sg}}
 const w=V[u];if(w)return{k:'m',rm:6,md:0,dl:2,d:ev(t),dir:1,z:z||w,g:sg};
 return{k:'i',v:t}};
const MM=(x,o)=>o.k=='r'?[192|x<<3|o.n]:[o.md<<6|x<<3|o.rm,...(o.dl==1?[o.d&255]:o.dl==2?[o.d&255,o.d>>8&255]:[])];
const SP=o=>o.k=='m'&&o.g>=0?[[38,46,54,62][o.g]]:[];
const E=(op,x,o,ib=[])=>{if(o.k!='r'&&o.k!='m')throw'Invalid operand';return[...SP(o),op,...MM(x,o),...ib]};
const Z=(a,b={})=>{if(a.z&&b.z&&a.z!=b.z)throw'Operand sizes differ';return a.z||b.z||0};
const im=(v,z)=>z>1?[v&255,v>>8&255]:[v&255];
const ti=o=>{if(o.k!='i')throw'Port must be a number or DX';return ev(o.v)&255};
const enc=(mn,ops)=>{
 const a=ops.length?po(ops[0]):0,b=ops.length>1?po(ops[1]):0,jc=JCC.indexOf(ALS[mn]||mn),need=n=>{if(ops.length!=n)throw mn+' needs '+n+' operand'+(n>1?'s':'')};
 if((mn=='RET'||mn=='RETF')&&ops.length)return[mn=='RET'?194:202,...im(ev(ops[0]),2)];
 if(NO[mn]){need(0);return NO[mn]}
 if(mn=='INT'){need(1);const v=ev(ops[0])&255;return v==3?[204]:[205,v]}
 if(mn in ALU){need(2);const i=ALU[mn];
  if(b.k=='i'){const v=ev(b.v),z=Z(a);if(!z)throw'Add BYTE PTR or WORD PTR';
   if(a.k=='r'&&!a.n)return z==1?[i*8+4,v&255]:[i*8+5,...im(v,2)];
   return z==1?E(128,i,a,[v&255]):v>=-128&&v<128?E(131,i,a,[v&255]):E(129,i,a,im(v,2))}
  if(a.k=='m'&&b.k=='m')throw'Memory to memory is not allowed';
  const z=Z(a,b);return b.k=='r'&&a.k!='r'?E(i*8+(z>1),b.n,a):E(i*8+2+(z>1),a.n,b)}
 if(mn=='MOV'){need(2);
  if(a.k=='s'){if(b.k=='i'||b.k=='s')throw'Invalid MOV to segment register';return E(142,a.n,b)}
  if(b.k=='s')return E(140,b.n,a);
  if(b.k=='i'){const v=ev(b.v);if(a.k=='r')return a.z==1?[176+a.n,v&255]:[184+a.n,...im(v,2)];
   if(!a.z)throw'Add BYTE PTR or WORD PTR';return E(198+(a.z>1),0,a,im(v,a.z))}
  if(a.k=='m'&&b.k=='m')throw'Memory to memory is not allowed';
  const z=Z(a,b);
  if(a.k=='r'&&!a.n&&b.dir)return[...SP(b),160+(z>1),b.d&255,b.d>>8&255];
  if(b.k=='r'&&!b.n&&a.dir)return[...SP(a),162+(z>1),a.d&255,a.d>>8&255];
  return b.k=='r'&&a.k!='r'?E(136+(z>1),b.n,a):E(138+(z>1),a.n,b)}
 if(mn=='XCHG'){need(2);let x=a,y=b;if(x.k!='r')[x,y]=[y,x];if(x.k!='r')throw'XCHG needs a register';
  const z=Z(x,y);if(z==2&&y.k=='r'&&(!x.n||!y.n))return[144+(x.n||y.n)];return E(134+(z>1),x.n,y)}
 if(mn=='TEST'){need(2);
  if(b.k=='i'){const v=ev(b.v),z=Z(a);if(!z)throw'Add BYTE PTR or WORD PTR';
   if(a.k=='r'&&!a.n)return z==1?[168,v&255]:[169,...im(v,2)];return E(246+(z>1),0,a,im(v,z))}
  let x=a,y=b;if(x.k=='r'&&y.k=='m')[x,y]=[y,x];if(y.k!='r')throw'Invalid TEST operands';
  return E(132+(Z(x,y)>1),y.n,x)}
 if(mn=='LEA'||mn=='LDS'||mn=='LES'){need(2);if(a.k!='r'||a.z!=2||b.k!='m')throw mn+' needs reg16, [memory]';return E({LEA:141,LDS:197,LES:196}[mn],a.n,b)}
 if(mn=='INC'||mn=='DEC'){need(1);const d=+(mn=='DEC');if(a.k=='r'&&a.z==2)return[64+d*8+a.n];
  const z=Z(a);if(!z)throw'Add BYTE PTR or WORD PTR';return E(254+(z>1),d,a)}
 if(mn in UNA){need(1);const z=Z(a);if(!z)throw'Add BYTE PTR or WORD PTR';return E(246+(z>1),UNA[mn],a)}
 if(mn in SHF){need(2);const z=Z(a);if(!z)throw'Add BYTE PTR or WORD PTR';
  const cl=b.k=='r'&&b.z==1&&b.n==1;if(!cl&&!(b.k=='i'&&ev(b.v)==1))throw'Shift count must be 1 or CL';
  return E(208+(z>1)+2*cl,SHF[mn],a)}
 if(mn=='PUSH'||mn=='POP'){need(1);const p=mn=='PUSH';
  if(a.k=='r'){if(a.z!=2)throw'Use a 16-bit register';return[(p?80:88)+a.n]}
  if(a.k=='s'){if(!p&&a.n==1)throw'POP CS is not valid';return[(p?6:7)+a.n*8]}
  return E(p?255:143,p?6:0,a)}
 if(mn=='IN'){need(2);if(a.k!='r'||a.n)throw'IN needs AL or AX';return b.k=='r'&&b.n==2&&b.z==2?[236+(a.z>1)]:[228+(a.z>1),ti(b)]}
 if(mn=='OUT'){need(2);if(b.k!='r'||b.n)throw'OUT needs AL or AX';return a.k=='r'&&a.n==2&&a.z==2?[238+(b.z>1)]:[230+(b.z>1),ti(a)]}
 if(mn in LP||jc>=0){need(1);const d=ev(ops[0])-(cur+2);
  if(!ur&&(d<-128||d>127))throw'Jump out of range ('+d+' bytes). Use JMP for long jumps';return[mn in LP?LP[mn]:112+jc,d&255]}
 if(mn=='JMP'||mn=='CALL'){need(1);const j=mn=='JMP';if(a.k!='i')return E(255,j?4:2,a);
  const t=ev(ops[0]),d=t-(cur+2);if(j&&!/\bnear\b/i.test(ops[0])&&d>=-128&&d<128)return[235,d&255];
  const w=t-(cur+3);return[j?233:232,w&255,w>>8&255]}
 throw'Unknown instruction '+mn};
const dat=(w,s)=>{const o=[],put=v=>w?o.push(v&255,v>>8&255):o.push(v&255);
 (s.match(/"[^"]*"|'[^']{2,}'|[^,]+/g)||[]).forEach(t=>{t=t.trim();let m;
  if(/^["']/.test(t)&&t.length>3)[...t.slice(1,-1)].forEach(c=>put(c.charCodeAt(0)));
  else if(m=t.match(/^(.+?)\s+dup\s*\((.*)\)$/i)){const n=ev(m[1]),v=m[2].trim()=='?'?0:ev(m[2]);for(let i=0;i<n;i++)put(v)}
  else put(t=='?'?0:ev(t))});return o};
const pass=ls=>{const N={},out=[],err=[],img=[];let base=null;cur=0x2000;
 ls.forEach((raw,n)=>{let s=raw.replace(/;.*$/,'').trim(),m,b,pre=[];if(!s)return;ur='';
  try{
   if(/^(\.\w+|assume\b|ends\b|endp\b|segment\b)/i.test(s)||/^\S+\s+(endp|ends|segment)\b/i.test(s))return;if(m=s.match(/^(\S+)\s+proc\b/i)){N[m[1].toUpperCase()]=cur;return}
   if(m=s.match(/^([a-z_.?@][\w.?@]*)\s*:\s*(.*)$/i)){N[m[1].toUpperCase()]=cur;s=m[2]}
   else if(m=s.match(/^([a-z_.?@][\w.?@]*)\s+(equ|db|dw)\b\s*(.*)$/i)){
    if(/^equ$/i.test(m[2])){N[m[1].toUpperCase()]=ev(m[3]);s=''}else{N[m[1].toUpperCase()]=cur;V[m[1].toUpperCase()]=/^db$/i.test(m[2])?1:2;s=m[2]+' '+m[3]}}
   if(!s)return;
   m=s.match(/^(\S+)\s*(.*)$/);let mn=m[1].toUpperCase(),rest=m[2].trim();
   while(PF[mn]){pre.push(PF[mn]);m=rest.match(/^(\S+)\s*(.*)$/);if(!m)throw'Missing instruction after '+mn;mn=m[1].toUpperCase();rest=m[2].trim()}
   if(mn=='END')return;
   if(mn=='ORG'){cur=ev(rest)&65535;if(base===null)base=cur;return}
   b=pre.concat(mn=='DB'||mn=='DW'?dat(mn=='DW',rest):enc(mn,rest?rest.split(','):[]));
   if(ur)err.push({n,m:'Unknown symbol '+ur})
  }catch(e){err.push({n,m:e.message||String(e)});b=0}
  if(b){if(base===null)base=cur;b.forEach((x,i)=>img[cur-base+i]=x&255);out.push({n,a:cur,b,t:raw.trim()});cur+=b.length}});
 return{N,out,err,img:Array.from(img,x=>x||0),base}};
const asm=src=>{const ls=src.split('\n');let r,pv='';L={};V={};
 for(let p=0;p<12;p++){r=pass(ls);const sg=JSON.stringify(r.N);if(sg==pv)break;pv=sg;L=r.N}
 return r};
const esc=s=>s.replace(/[&<>]/g,c=>'&#'+c.charCodeAt(0)+';');
const doAsm=fl=>{const o=g('alst'),r=asm(g('asm').value);
 window.hlErr&&hlErr(r.err.map(x=>x.n));if(r.err.length){o.innerHTML=r.err.map(x=>'<span class=e>Line '+(x.n+1)+': '+esc(x.m)+'</span>').join('\n');return}
 if(!r.img.length){o.textContent='Nothing to assemble yet.';return}
 g('ha').value=H(r.base,4);g('hx').value=r.img.map(x=>H(x,2)).join(' ');ld();
 o.innerHTML=r.out.map(x=>'<span class=h>'+H(x.a,4)+'</span>  '+x.b.map(y=>H(y,2)).join(' ').padEnd(12)+' '+esc(x.t)).join('\n')+'\n<span class=h>'+r.img.length+' bytes loaded at '+H(r.base,4)+'h</span>';
 if(fl){led=0;go()}};
g('asb').onclick=()=>doAsm(0);g('asr').onclick=()=>doAsm(1);
g('ast').onclick=()=>{run=0;tok++;ui()};{const H0=document.documentElement,sl=()=>{g('ast').textContent=H0.lang=='ar'?'\u0625\u064a\u0642\u0627\u0641':'Stop'};new MutationObserver(sl).observe(H0,{attributes:true,attributeFilter:['lang']});sl()}
g('asm').addEventListener('keydown',e=>{if((e.ctrlKey||e.metaKey)&&e.key=='Enter'){e.preventDefault();doAsm(1)}});
let tok=0;
go=function(){const id=++tok;let t0=performance.now();run=1;(function t(){if(!run||id!=tok)return;const n=performance.now(),k=Math.min((n-t0)*300|0,30000);t0=n;for(let i=0;i<k&&run;i++)step();ui();if(run)setTimeout(t,20)})()};
const u0=ui;ui=function(){u0();g('lh').textContent='OUT '+H(led,2)+'h'};ui();
})();

(()=>{const c=document.getElementById('led').children,cnt=new Uint32Array(256);let duty=null,tok=0;
[...c].forEach((e,i)=>e.dataset.b='D'+(7-i));
const u1=ui;ui=function(){u1();for(let i=0;i<8;i++)c[i].style.setProperty('--d',run&&duty?duty[7-i]:(led>>(7-i))&1)};
go=function(){const id=++tok;let t0=performance.now();run=1;bpk=1;duty=null;cnt.fill(0);(function t(){if(!run||id!=tok)return;const n=performance.now(),k=Math.min((n-t0)*300|0,30000);t0=n;
 for(let i=0;i<k&&run;i++){step();cnt[led]++}
 let tot=0;for(let v=0;v<256;v++)tot+=cnt[v];
 if(tot){duty=[0,0,0,0,0,0,0,0];for(let v=0;v<256;v++)if(cnt[v])for(let b=0;b<8;b++)if(v>>b&1)duty[b]+=cnt[v]/tot;cnt.fill(0)}
 ui();if(run)setTimeout(t,20)})()};
ui()})();

const EX=[
['Sum of 1..10',`; Sum of 1..10  ->  [2100h] and LEDs
        ORG  2000h
        MOV  AX, 0
        MOV  CX, 10
AGAIN:  ADD  AX, CX
        LOOP AGAIN
        MOV  [2100h], AX
        OUT  80h, AL
        INT  3
`],
['Running light',`; Running light on the 8 LEDs (port 80h)
        ORG  2000h
        MOV  AL, 1
SHOW:   OUT  80h, AL
        MOV  CX, 0FFFFh
DELAY:  LOOP DELAY
        ROL  AL, 1
        JMP  SHOW
`],
['Binary counter (LEDs)',`; Binary counter on the LEDs
        ORG  2000h
        MOV  AL, 0
NEXT:   OUT  80h, AL
        MOV  CX, 0FFFFh
WAIT:   LOOP WAIT
        INC  AL
        JMP  NEXT
`],
['Traffic light (LEDs)',`; D2 red, D0 green, D1 yellow
        ORG  2000h
LIGHT:  MOV  AL, 04h
        CALL SHOW
        MOV  AL, 01h
        CALL SHOW
        MOV  AL, 02h
        CALL SHOW
        JMP  LIGHT
SHOW:   OUT  80h, AL
        MOV  CX, 0FFFFh
WAIT:   LOOP WAIT
        RET
`],
['Fibonacci -> 2100h',`; First 10 Fibonacci numbers stored from 2100h
        ORG  2000h
        MOV  SI, 2100h
        MOV  CX, 10
        MOV  AL, 0
        MOV  BL, 1
FIB:    MOV  [SI], AL
        INC  SI
        MOV  DL, AL
        ADD  DL, BL
        MOV  AL, BL
        MOV  BL, DL
        LOOP FIB
        INT  3
`],
['Factorial of 5',`; 5! = 78h -> [2100h] and LEDs
        ORG  2000h
        MOV  AX, 1
        MOV  CX, 5
FACT:   MUL  CX
        LOOP FACT
        MOV  [2100h], AX
        OUT  80h, AL
        INT  3
`],
['Largest of 5 bytes',`; Largest of 5 bytes -> [2110h] and LEDs
        ORG  2000h
        MOV  SI, OFFSET DATA
        MOV  CX, 5
        MOV  AL, 0
SCAN:   CMP  AL, [SI]
        JAE  SKIP
        MOV  AL, [SI]
SKIP:   INC  SI
        LOOP SCAN
        MOV  [2110h], AL
        OUT  80h, AL
        INT  3
DATA:   DB   12h, 45h, 0A7h, 3Ch, 8Eh
`],
['Bubble sort (6 bytes)',`; Sort 6 bytes at 2100h in ascending order
        ORG  2000h
        MOV  DL, 5
OUTER:  MOV  SI, 2100h
        MOV  CL, DL
        MOV  CH, 0
INNER:  MOV  AL, [SI]
        CMP  AL, [SI+1]
        JBE  OK
        XCHG AL, [SI+1]
        MOV  [SI], AL
OK:     INC  SI
        LOOP INNER
        DEC  DL
        JNZ  OUTER
        INT  3
        ORG  2100h
        DB   9, 3, 7, 1, 8, 2
`],
['Copy block (REP MOVSB)',`; Copy 8 bytes from 2100h to 2200h
        ORG  2000h
        MOV  SI, 2100h
        MOV  DI, 2200h
        MOV  CX, 8
        CLD
        REP  MOVSB
        INT  3
        ORG  2100h
        DB   11h, 22h, 33h, 44h, 55h, 66h, 77h, 88h
`]
];
(()=>{const g=i=>document.getElementById(i),W=1400,SH=new Uint8Array(262144),TT={},PV={},RC=[],FM=[2048,1024,512,256,128,64,16,4,1],D=document.documentElement,
LS=(k,v)=>{try{return v===undefined?localStorage.getItem(k):localStorage.setItem(k,v)}catch(e){}},an=d=>'flash 1.4s ease-out '+(-d)+'ms';
const th=v=>{D.dataset.theme=v;LS('m86t',v)},fz=v=>{v=Math.max(80,Math.min(160,+v||100));D.style.setProperty('--fz',v/100);g('tfr').value=v;LS('m86f',v);tl()};
let LG='en';th(LS('m86t')=='light'?'light':'dark');
var tmW=0;const tb=g('tb'),mp=g('tmp'),mn=g('tmn'),mo=o=>{mp.hidden=!o;mn.setAttribute('aria-expanded',o);tmWg()};
mn.onclick=e=>{e.stopPropagation();mo(mp.hidden)};document.addEventListener('click',e=>{if(e.target.isConnected&&!tb.contains(e.target))mo(false)});
g('tth').onclick=()=>{const d=D.dataset.theme!='light';th(d?'light':'dark');thZ(d)};
g('tfz').onclick=()=>{g('tfw').hidden=!g('tfw').hidden};g('tfr').oninput=e=>fz(e.target.value);
g('tlg').onclick=()=>lgFx();
let ac,sn=LS('m86s')!=='0';const sl2=()=>tl();
const SV=p=>'<svg class=ic viewBox="0 0 24 24" aria-hidden=true>'+p+'</svg>',IT=SV('<path d="m5 8 6 6"/><path d="m4 14 6-6 2-3"/><path d="M2 5h12"/><path d="M7 2h1"/><path d="m22 22-5-10-5 10"/><path d="M14 18h6"/>'),IV=SV('<path d="M11 5 6 9H2v6h4l5 4z"/><path d="M15.5 8.5a5 5 0 0 1 0 7"/><path d="M19 5a10 10 0 0 1 0 14"/>'),IX=SV('<path d="M11 5 6 9H2v6h4l5 4z"/><path d="m22 9-6 6"/><path d="m16 9 6 6"/>'),FZ=v=>'<span class=fzW><span class=fzS><i>A</i><b>A</b></span><span class=fzP style="--p:'+Math.max(0,Math.min(100,(v-80)/.8))+'%">'+v+'%</span></span>';
const beep=d=>{if(!sn)return;try{ac=ac||new(window.AudioContext||window.webkitAudioContext)();if(ac.state==='suspended')ac.resume();const t=ac.currentTime;
if(d>=.1){[[659,0],[988,.09]].forEach(([q,s])=>{const o=ac.createOscillator(),v=ac.createGain();o.frequency.value=q;v.gain.setValueAtTime(.0001,t+s);v.gain.linearRampToValueAtTime(.08,t+s+.005);v.gain.exponentialRampToValueAtTime(.0001,t+s+.3);o.connect(v);v.connect(ac.destination);o.start(t+s);o.stop(t+s+.32)});return}
const o=ac.createOscillator(),v=ac.createGain(),u=t+d+.02;o.type='triangle';o.frequency.value=1500;v.gain.setValueAtTime(.0001,t);v.gain.linearRampToValueAtTime(.05,t+.004);v.gain.exponentialRampToValueAtTime(.0001,u);o.connect(v);v.connect(ac.destination);o.start(t);o.stop(u+.01)}catch(e){}};
g('tsn').onclick=()=>{sn=!sn;LS('m86s',sn?'1':'0');sl2();beep(.05)};
g('keys').addEventListener('click',e=>{if(e.target.closest('button'))beep(.03)});
/* changed registers / flags / memory */
let pr=0;const AT=[
['Monitor Ready','الشاشة جاهزة'],['EB/EW edit | GO run | ST step | REG','EB/EW تعديل | GO تشغيل | ST خطوة | REG'],
['Running...','قيد التشغيل...'],['RESET stops it','RESET يوقفه'],['GO: type the address','GO: اكتب العنوان'],['NEXT, then TTY to run','NEXT ثم TTY للتشغيل'],['then TTY to run','ثم TTY للتشغيل'],
[': type the address',': اكتب العنوان'],['then NEXT','ثم NEXT'],['TTY to run','TTY للتشغيل'],[': type word',': اكتب كلمة'],[': type byte',': اكتب بايت'],
['NEXT save | PRV back | TTY exit','NEXT حفظ | PRV رجوع | TTY خروج'],['Address: ','العنوان: '],
[' | Press GO (key 2) then TTY to execute',' | اضغط GO (المفتاح 2) ثم TTY للتنفيذ'],[' | Type 4 hex digits, then GO (key 2)',' | اكتب 4 أرقام hex ثم GO (المفتاح 2)'],
['Type the 4-digit start address, then GO (key 2 or G) and TTY','اكتب عنوان البداية (4 أرقام) ثم GO (المفتاح 2 أو G) ثم TTY'],[' port ',' منفذ '],
['NEXT/PRV next or previous port\nor type another port address | TTY exit','NEXT/PRV المنفذ التالي أو السابق\nأو اكتب عنوان منفذ آخر | TTY خروج'],
['DUMP | NEXT/PRV = 16 bytes | TTY exit','عرض الذاكرة | NEXT/PRV = 16 بايت | TTY خروج'],[' mismatches',' اختلافات'],[' mismatch #',' اختلاف رقم '],[' mismatch',' اختلاف'],
['NEXT finds the next | TTY stops','NEXT التالي | TTY إيقاف'],['REG: press a register key\nname after the / on the key','REG: اضغط مفتاح سجل\nاسمه بعد علامة / على المفتاح'],[': type hex value',': اكتب قيمة hex'],
['Saved. ','تم الحفظ. '],['Stepped: next IP + opcode\nST again | REG registers','خطوة: IP التالي + الأوبكود\nST خطوة أخرى | REG السجلات'],
['Key ','المفتاح '],[' is not active now.\nTry commands like EB, GO, ST, REG...',' غير مفعّل الآن.\nجرّب أوامر مثل EB, GO, ST, REG...'],
['Program halted (CC)\nREG registers | GO run again','توقف البرنامج (CC)\nREG السجلات | GO تشغيل مجدداً'],['Breakpoint hit at ','وصل إلى نقطة التوقف عند '],
['ST step | GO resume | F1 edit','ST خطوة | GO متابعة | F1 تعديل'],[' executed - stopped',' نُفِّذ - توقف'],['Unsupported opcode ','أوبكود غير مدعوم '],
['End address is below the\nstart address (','عنوان النهاية أصغر من\nعنوان البداية ('],[' finished: ',' انتهى: '],[' stopped: ',' توقف: '],[' so far',' حتى الآن'],
[' PASS: ',' نجح: '],[' bytes identical',' بايت متطابقة'],['Stack too low for INTR\n(SP=','المكدس منخفض لـ INTR\n(SP='],[', needs 6 bytes)','، يلزم 6 بايت)'],
['Vector ','المتجه '],['h is empty (IVT ','h فارغ (IVT '],[')\nHook one with F3, or EW at ',')\nاربطه بـ F3 أو EW عند '],['h: FL, CS, IP pushed\nCS:IP = ','h: تم دفع FL وCS وIP\nCS:IP = '],
[' bytes copied',' بايت منسوخة'],['FILL done: ','تمت التعبئة: '],['MV done: ','تم النسخ: '],['Destination leaves RAM\n(RAM is 00000-3FFFF)','الوجهة خارج الذاكرة\n(الذاكرة 00000-3FFFF)'],
['Breakpoint cleared','تم مسح نقطة التوقف'],['Breakpoint set at ','نقطة التوقف عند '],['\nGO stops just before it','\nGO يتوقف قبلها'],
['h unhooked (IVT cleared)','h فُكّ ربطه (تم مسح IVT)'],['\nCC now calls this handler','\nCC يستدعي هذا المعالج الآن'],['Type the ','اكتب '],[',\nthen press NEXT','،\nثم اضغط NEXT'],
[' only works in Data Mode.\n(EB/EW -> Address -> NEXT -> ',' يعمل فقط في وضع البيانات.\n(EB/EW -> العنوان -> NEXT -> '],['Address ','العنوان '],
[' is not RAM\nRAM is 00000-3FFFF',' ليس في الذاكرة\nالذاكرة 00000-3FFFF'],[' moved up, 00h at ',' نُقلت للأعلى، 00h عند '],[' moved down, ',' نُقلت للأسفل، '],
['Finish your current step first,\nor press TTY (.) to cancel','أنهِ الخطوة الحالية أولاً،\nأو اضغط TTY (.) للإلغاء'],[' finished',' انتهى'],[' cancelled',' أُلغي'],
['Already at the first prompt\nTTY cancels ','أنت في أول خطوة\nTTY يلغي '],[' is active. Finish your step,\nor press TTY (.) to cancel',' نشط. أنهِ خطوتك،\nأو اضغط TTY (.) للإلغاء'],
['NEXT/PRV step the port, TTY exits','NEXT/PRV للتنقل بين المنافذ، TTY للخروج'],['DUMP finished','انتهى عرض الذاكرة'],['NEXT/PRV page the dump, TTY exits','NEXT/PRV للتنقل في العرض، TTY للخروج'],
['NEXT finds the next difference,\nTTY stops','NEXT يجد الاختلاف التالي،\nTTY للإيقاف'],['Type a load address first\n(hex, in the Load a program box)','اكتب عنوان التحميل أولاً\n(hex في خانة تحميل برنامج)'],
['Loaded ','تم تحميل '],[' bytes at ',' بايت عند '],['\nRun: GO, ','\nللتشغيل: GO, '],[' bytes loaded at ',' بايت محمّلة عند '],
['State imported from ','تم استيراد الحالة من '],['Import failed: not a valid\nM86-01 state file','فشل الاستيراد: ملف حالة\nM86-01 غير صالح'],
['\nNEXT write','\nNEXT كتابة'],['\nNEXT ok','\nNEXT موافق'],[' | PRV back',' | PRV رجوع'],[' | TTY exit',' | TTY خروج'],[' | TTY cancel',' | TTY إلغاء'],
['start address','عنوان البداية'],['end address','عنوان النهاية'],['fill byte','بايت التعبئة'],['source start','بداية المصدر'],['source end','نهاية المصدر'],['destination start','بداية الوجهة'],
['1st block start','بداية الكتلة 1'],['1st block end','نهاية الكتلة 1'],['2nd block start','بداية الكتلة 2'],['block start','بداية الكتلة'],['block end','نهاية الكتلة'],
['block to verify against','الكتلة المراد مقارنتها'],['port address','عنوان المنفذ'],['byte to write','بايت للكتابة'],['word to write','كلمة للكتابة'],['vector type (00-FF)','رقم المتجه (00-FF)'],
['address (empty = clear)','العنوان (فارغ = مسح)'],['address (empty = IP)','العنوان (فارغ = IP)'],['INT type to hook','رقم INT للربط'],['handler (empty = unhook)','المعالج (فارغ = فك الربط)'],[' at ',' عند ']
].sort((a,b)=>b[0].length-a[0].length);
const arS=()=>{const e=g('stat');let x=e.textContent;for(const[a,b]of AT)x=x.split(a).join(b);e.textContent=x};
let lmS=-2;const LW=new Set;
const u2=ui;ui=function(){const t=performance.now(),sp=A(s[2],r[4]);let ch=-1;const nr=new Set,ws=[];
 for(let i=0;i<262144;i++)if(M[i]!==SH[i]){SH[i]=M[i];TT['m'+i]=t;if(!(i>=sp-16&&i<sp+64)){if(ch<0)ch=i;nr.add(i>>4);ws.push(i)}const j=RC.indexOf(i);if(j>=0)RC.splice(j,1);RC.unshift(i);RC.length>8&&RC.pop()}
 wc=0;if(lf&&lm<0)LW.clear();if(!(lf&&lm<0)&&nr.size){wc=1;if(!pr)LW.clear();ws.forEach(a=>LW.add(a));if(!pr&&!lf)wk=[];[...nr].sort((a,b)=>a-b).forEach(r=>wr(r<<4))}
 if(ch>=0&&!lf)lm=ch;if(lm>=0&&(ch>=0||lf))wr(lm);lf=0;
 u2();if(LG=='ar')arS();const hot=(k,v)=>{if(PV[k]!==undefined&&PV[k]!=v)TT[k]=t;PV[k]=v;const d=t-(TT[k]||-1e9);return d<W?d:-1};
 [...g('regs').children].forEach((e,i)=>{if(i<RN.length){const d=hot('r'+i,rget(i));if(d>=0)e.lastChild.style.animation=an(d)}});
 [...g('fl').children].forEach((e,i)=>{const d=hot('f'+i,F&FM[i]?1:0);if(d>=0)e.style.animation=an(d)});
 const mk=!wc&&(st=='data'||st=='dmp'||st=='cmp')?null:LW,m=g('mem');m.innerHTML=m.innerHTML.replace(/^(?:<s>)?([0-9A-F]{5})(?:<\/s>)?: (.*)$/gm,(z,a,x)=>{let i=0;return '<s>'+a+'</s>: '+x.replace(/(?:<b>)?[0-9A-F]{2}(?:<\/b>)? /g,y=>{const p=parseInt(a,16)+i++,d=t-(TT['m'+p]||-1e9),z=mk&&mk.has(p)&&y[0]!='<'?'<u>'+y.slice(0,-1)+'</u> ':y;return d<W?'<i style="animation:'+an(d)+'">'+z.slice(0,-1)+'</i> ':z})});
 if(lm!==lmS){lmS=lm;const bb=m.querySelector('b');if(bb)m.scrollTop=Math.max(0,bb.offsetTop-m.clientHeight/2)}
 if(pr&&!run)beep(.15);pr=run};
/* assembly error lines + examples */
const t=g('asm'),eb=document.createElement('div');eb.id='eb';t.parentNode.appendChild(eb);let er=[];
const lh=()=>parseFloat(getComputedStyle(t).lineHeight)||20.8,pd=()=>parseFloat(getComputedStyle(t).paddingTop)||12,
dr=()=>{const h=lh(),p=pd();eb.innerHTML=er.map(n=>'<i style="top:'+(p+n*h-t.scrollTop)+'px;height:'+h+'px"></i>').join('')};
window.hlErr=a=>{er=a;if(a.length){const y=pd()+a[0]*lh();if(y<t.scrollTop||y>t.scrollTop+t.clientHeight-lh())t.scrollTop=Math.max(0,y-t.clientHeight/3)}dr()};
t.addEventListener('input',()=>{er=[];dr()});t.addEventListener('scroll',dr);
g('alst').addEventListener('click',e=>{const s=e.target.closest('.e'),m=s&&s.textContent.match(/\d+/);if(!m)return;const n=m[0]-1,L=t.value.split('\n');let a=0;for(let i=0;i<n;i++)a+=L[i].length+1;t.focus();t.setSelectionRange(a,a+(L[n]||'').length);t.scrollTop=Math.max(0,n*lh()-t.clientHeight/3)});
const sx2=g('exs');sx2.innerHTML='<option value="">Examples\u2026</option>'+EX.map((e,i)=>'<option value='+i+'>'+e[0]+'</option>').join('');
sx2.onchange=()=>{if(sx2.value==='')return;t.value=EX[sx2.value][1];t.dispatchEvent(new Event('input'));sx2.selectedIndex=0;t.scrollTop=0;g('alst').textContent='Example loaded. Press Assemble or Assemble & Run.'};
/* export / import state */
g('tex').onclick=()=>{const m=[];for(let i=0;i<262144;){if(!M[i]){i++;continue}const a=i;let e=i;while(i<262144&&i-e<=16){if(M[i])e=i;i++}m.push([a.toString(16),Array.from(M.subarray(a,e+1),x=>hx(x,2)).join('')])}
 const o={app:'M86-01',v:1,r:[...r],s:[...s],ip,F,led,io:{},bp,m,asm:t.value};io.forEach((x,i)=>{if(x)o.io[i]=x});
 const a=document.createElement('a');a.href=URL.createObjectURL(new Blob([JSON.stringify(o)],{type:'application/json'}));a.download='m86-state.json';a.click()};
g('tim').onclick=()=>g('tfi').click();
g('tfi').onchange=e=>{const f=e.target.files[0];e.target.value='';if(!f)return;f.text().then(x=>{try{const o=JSON.parse(x);if(o.app!=='M86-01')throw 0;
 run=0;M.fill(0);o.m.forEach(([a,h])=>{a=parseInt(a,16);(h.match(/../g)||[]).forEach((b,i)=>M[a+i]=parseInt(b,16))});
 r.set(o.r);s.set(o.s);ip=o.ip;F=o.F;led=o.led;io.fill(0);for(const k in o.io)io[k]=o.io[k];bp=o.bp??-1;
 if(typeof o.asm=='string'){t.value=o.asm;t.dispatchEvent(new Event('input'))}
 st='i';cmd='';buf='';ex='';vw=0;note='State imported from '+f.name;ui()}catch(_){note='Import failed: not a valid\nM86-01 state file';ui()}})};
const AG=[
['ابدأ هنا (للمبتدئين)',`<ul><li>الشاشة <b>الخضراء</b> تخبرك بالخطوة التالية، والشاشتان الحمراوان تعرضان العنوان (يسار) والبيانات (يمين).</li><li>الأرقام <b>سداسية عشرية</b> (0-9 وA-F)؛ كتابة <kbd>5</kbd><kbd>0</kbd><kbd>0</kbd> تعني العنوان 0500h.</li><li>عند ظهور <b>8086 uP</b> يكون الكيت في وضع الخمول والمفاتيح السوداء أوامر: 0 EB، 1 ER، 2 GO، 3 ST، 4 IB، 5 OB، 6 MV، 7 EW، 8 IW، 9 OW، C BC، E VR.</li><li><kbd>NEXT</kbd> للتأكيد والانتقال، <kbd>TTY</kbd> للإنهاء أو الخروج، <kbd>B.S</kbd> لمسح رقم، <kbd>RESET</kbd> لإعادة التشغيل (الذاكرة تبقى).</li></ul>`],
['أول برنامج',`خزّن <b>B4 AA CC</b> عند 0500 ثم شغّله:<ol><li>في وضع الخمول اضغط <kbd>0</kbd> (EB).</li><li>اكتب <kbd>5</kbd><kbd>0</kbd><kbd>0</kbd> ثم <kbd>NEXT</kbd>.</li><li>أدخل <b>B4</b> ثم <b>AA</b> ثم <b>CC</b> مع <kbd>NEXT</kbd> بعد كل بايت، ثم اضغط <kbd>TTY</kbd>.</li><li>للتشغيل: <kbd>2</kbd> (GO)، اكتب 500، ثم <kbd>TTY</kbd>.</li><li>يتوقف عند CC ويظهر AX = AA00 في بطاقة السجلات.</li></ol>`],
['تعديل الذاكرة (EB / EW)',`<ol><li><kbd>0</kbd> (EB) لتعديل البايتات و<kbd>7</kbd> (EW) لتعديل الكلمات 16 بت.</li><li>اكتب العنوان ثم <kbd>NEXT</kbd>.</li><li>اكتب قيمة ثم <kbd>NEXT</kbd> للحفظ والانتقال للعنوان التالي؛ <kbd>PRV</kbd> للحفظ والرجوع.</li><li><kbd>NEXT</kbd> دون كتابة يتصفح الذاكرة، و<kbd>TTY</kbd> يحفظ ويخرج.</li></ol>EW تخزّن البايت الأدنى أولاً (1234 تُحفظ 34 12).`],
['إدراج وحذف بايتات (INS / DEL)',`<ol><li>افتح بايتاً بـ EB أو EW ثم <kbd>NEXT</kbd> لعرض البيانات (يعملان في هذا الوضع فقط).</li><li><kbd>INS</kbd> يفتح فراغاً 00h ويزيح ما بعده للأعلى.</li><li><kbd>DEL</kbd> يحذف البايت الحالي ويزيح ما بعده للأسفل.</li></ol>إزاحات القفز والنداء لا تُصحَّح تلقائياً، فتحقق منها بعد التعديل.`],
['ملء ونسخ ومقارنة الكتل (FILL, MV, BC, VR)',`<ul><li><b>FILL</b> (مفتاح PRV في الخمول): SA البداية، EA النهاية، DAtA البايت. <kbd>NEXT</kbd> بعد القيمة الأخيرة ينفّذ.</li><li><b>MV</b> (<kbd>6</kbd>): نسخ كتلة (SA وEA وdESt)، والتداخل يُعالَج صحيحاً.</li><li><b>BC</b> (<kbd>C</kbd>) و<b>VR</b> (<kbd>E</kbd>): SA ثم EA ثم SA2 بداية الكتلة الثانية؛ عند أي اختلاف يتوقف الكيت ويعرض العنوان والبايتين.</li><li><kbd>PRV</kbd> يرجع خطوة و<kbd>TTY</kbd> يلغي دون تغيير الذاكرة، والنطاق الخاطئ يعرض Err.</li></ul>`],
['منافذ الإدخال والإخراج (IB, IW, OB, OW)',`<ul><li><b>IB</b> (<kbd>4</kbd>) و<b>IW</b> (<kbd>8</kbd>): اكتب عنوان المنفذ ثم <kbd>NEXT</kbd> لعرض قيمته.</li><li><b>OB</b> (<kbd>5</kbd>) و<b>OW</b> (<kbd>9</kbd>): اكتب المنفذ و<kbd>NEXT</kbd> ثم القيمة و<kbd>NEXT</kbd> للكتابة؛ <kbd>TTY</kbd> للخروج.</li><li>المنفذان 00h و80h هما الـ LEDs D7-D0 (تظهر في شاشة Assembly editor)، وكل منفذ آخر يحتفظ بآخر قيمة كُتبت ويقرؤها IN.</li></ul>`],
['المقاطعات ومفاتيح الوظائف (VCT, F1-F3)',`<ul><li><b>VCT</b>: اكتب رقم المتجه (00-FF) ثم <kbd>NEXT</kbd>؛ يحفظ FLAGS وCS وIP ثم ينتقل إلى المعالج.</li><li><b>F1</b> نقطة توقف: أدخل عنواناً فيتوقف GO قبله (brEA). <kbd>NEXT</kbd> فارغ يمسحها.</li><li><b>F2</b> تفريغ: يعرض 16 بايتاً، و<kbd>NEXT</kbd>/<kbd>PRV</kbd> يتحركان 16 بايتاً.</li><li><b>F3</b> ربط: رقم INT ثم عنوان المعالج لملء جدول المتجهات.</li></ul>`],
['تشغيل برنامج (GO)',`<ol><li>اضغط <kbd>2</kbd> (GO).</li><li>اكتب عنوان البداية.</li><li>اضغط <kbd>TTY</kbd> للتشغيل مباشرة (بدون NEXT).</li></ol>يتوقف البرنامج عند CC (INT 3) أو HLT، و<kbd>RESET</kbd> يوقفه في أي وقت.`],
['التنفيذ خطوة بخطوة (ST)',`<ol><li>حدّد البداية: <kbd>REG</kbd> ثم <kbd>C</kbd> (IP) ثم العنوان ثم <kbd>TTY</kbd> (قيمة IP بعد Power هي 2000، و RESET يُبقي القيمة الحالية).</li><li>اضغط <kbd>3</kbd> (ST) لتنفيذ تعليمة واحدة.</li><li>كرر ST وراقب تغيّر بطاقة السجلات.</li></ol>`],
['السجلات (REG / ER)',`<ol><li>اضغط <kbd>REG</kbd> (أو <kbd>1</kbd> في وضع الخمول).</li><li>اضغط مفتاح السجل: 0 AX، 1 BX، 2 CX، 3 DX، 4 SP، 5 BP، 6 SI، 7 DI، 8 CS، 9 DS، A SS، B ES، C IP، D FL.</li><li>اكتب حتى 4 خانات لتغيير القيمة؛ <kbd>NEXT</kbd>/<kbd>PRV</kbd> للتنقل و<kbd>TTY</kbd> للحفظ والخروج.</li></ol>`],
['المفاتيح والشاشات',`<ul><li><b>الزرقاء</b>: RESET وREG وNEXT وPRV وTTY وB.S وINS وDEL وVCT وF1-F3.</li><li><b>زر Power</b> (الأحمر بجانب 5 MHz): يمسح الذاكرة والسجلات كلها (وفي وضع التدريب يعيدك أيضاً إلى الواجهة الرئيسية لاختيار المستوى). أما <b>RESET</b> فيعيد تشغيل المراقب فقط وتبقى الذاكرة والسجلات والأعلام كما هي.</li><li><b>السوداء</b>: أرقام 0-F، وفي الخمول تنفّذ الأوامر.</li><li><b>LEDs D7-D0</b> (في شاشة Assembly editor): آخر بايت كتبته تعليمة OUT.</li><li><b>لوحة المفاتيح</b>: 0-9 وA-F، Enter = NEXT، Backspace = B.S، - = PRV، . = TTY، G = GO، Esc = RESET، V = VCT.</li></ul>`],
['محرر Assembly',`<ol><li>اكتب كود 8086 وحدّد عنوان التحميل بـ ORG (مثل ORG 2000h).</li><li><b>تجميع</b> يترجم الكود ويحمّله في الذاكرة، ثم شغّله بـ GO.</li><li><b>تجميع وتشغيل</b> يفعل الاثنين (Ctrl+Enter)؛ أنهِ كودك بـ INT 3.</li><li>الأخطاء تظهر برقم السطر ويُظلَّل السطر بالأحمر؛ اضغط الخطأ للانتقال إليه.</li></ol>`],
['حل المشكلات',`<ul><li><b>مفتاح لا يعمل؟</b> راجع الشاشة الخضراء فهي توضح الوضع الحالي.</li><li><b>المفتاح الأسود يكتب رقماً:</b> الكيت ليس في الخمول، اضغط <kbd>RESET</kbd>.</li><li><b>TTY لا يشغّل البرنامج:</b> بعد GO اكتب عنوان البداية أولاً ثم اضغط <kbd>TTY</kbd>.</li><li><b>البرنامج لا يتوقف:</b> أنهِه بـ CC (INT 3) أو اضغط <kbd>RESET</kbd>.</li></ul>`]];
function lgFx(){if(lgFx.b)return;const nl=LG=='ar'?'en':'ar',ar=nl=='ar',rm=matchMedia('(prefers-reduced-motion:reduce)').matches,
 o=document.getElementById('lgo')||(()=>{const x=document.createElement('div');x.id='lgo';document.body.appendChild(x);return x})();
 lgZ(nl);
 if(rm||!o.animate){setLang(nl);return}
 lgFx.b=1;
 const T=1200,S0=260,SD=560,m=ar?1:-1,L=ar?'ابتثجحخدذرزسشصضطظعغفقكلمنهوي':'ABCDEFGHJKLMNPRSTUVWXYZ',N=10;
 let ps='';for(let i=0;i<N;i++)ps+='<span class="pt'+(i%2?' w':'')+'">'+L[Math.floor(Math.random()*L.length)]+'</span>';
 o.innerHTML='<div class="vl"></div><div class="cd"><div class="pl"><em>Aa</em><em>\u0639</em><u></u>'+ps+'<div class="kb"><span class="og">'+(ar?'Aa':'\u0639')+'</span><span class="ng">'+(ar?'\u0639':'Aa')+'</span></div></div><small dir="'+(ar?'rtl':'ltr')+'">'+(ar?'العربية':'English')+'</small></div>';
 o.style.display='block';
 const pl=o.querySelector('.pl'),dist=pl.clientWidth-72-16,s=ar?0:dist,e=ar?dist:0,cx=8+e+36,
 vl=o.querySelector('.vl'),cd=o.querySelector('.cd'),kb=o.querySelector('.kb'),og=o.querySelector('.og'),ng=o.querySelector('.ng'),rg=o.querySelector('u'),sm=o.querySelector('small');
 rg.style.left=(8+e)+'px';
 vl.animate([{opacity:0},{opacity:1,offset:.2},{opacity:1,offset:.84},{opacity:0}],{duration:T,fill:'both'});
 cd.animate([{opacity:0,transform:'scale(.55) translateY(24px)',easing:'cubic-bezier(.2,.9,.3,1.3)'},{opacity:1,transform:'none',offset:.25},{opacity:1,transform:'none',offset:.83,easing:'ease-in'},{opacity:0,transform:'scale(.9)'}],{duration:T,fill:'both'});
 kb.animate([{transform:'translateX('+s+'px) scale(1,1)'},{transform:'translateX('+(s+e)/2+'px) scale(1.3,.85)',offset:.45},{transform:'translateX('+(e+10*m)+'px) scale(.95,1.06)',offset:.8},{transform:'translateX('+e+'px) scale(1,1)'}],{duration:SD,delay:S0,easing:'cubic-bezier(.55,0,.25,1)',fill:'both'});
 og.animate([{opacity:1,transform:'scale(1)'},{opacity:0,transform:'scale(.2) rotate('+90*m+'deg)'}],{duration:150,delay:S0+170,fill:'both'});
 ng.animate([{opacity:0,transform:'scale(.2) rotate('+-90*m+'deg)'},{opacity:1,transform:'none'}],{duration:320,delay:S0+330,easing:'cubic-bezier(.2,.9,.3,1.5)',fill:'both'});
 rg.animate([{opacity:.9,transform:'scale(.9)'},{opacity:0,transform:'scale(2.4)'}],{duration:520,delay:S0+SD-80,easing:'ease-out',fill:'both'});
 sm.animate([{opacity:0,transform:'translateY(12px)'},{opacity:.9,transform:'none'}],{duration:300,delay:S0+SD-40,easing:'ease-out',fill:'both'});
 o.querySelectorAll('.pt').forEach((el,i)=>{const an=(i/N+Math.random()*.08)*Math.PI*2,dist2=70+Math.random()*90,sc=.8+Math.random()*.9,rt=(Math.random()-.5)*160;
  el.style.left=cx+'px';
  el.animate([{opacity:0,transform:'translate(0,0) scale(.3)'},{opacity:1,offset:.2},{opacity:0,transform:'translate('+Math.cos(an)*dist2+'px,'+Math.sin(an)*dist2+'px) scale('+sc+') rotate('+rt+'deg)'}],{duration:620,delay:S0+SD-60+Math.random()*60,easing:'cubic-bezier(.1,.7,.3,1)',fill:'both'})});
 setTimeout(()=>setLang(nl),320);
 setTimeout(()=>{o.style.display='none';o.innerHTML='';lgFx.b=0},T+60)}
function setLang(l){LG=l;LS('m86l',l);D.lang=l;D.classList.toggle('ar',l=='ar');const a=l=='ar',o0=document.querySelector('#exs option');if(o0)o0.textContent=a?'أمثلة…':'Examples…';
 t.dataset.pe=t.dataset.pe||t.placeholder;t.placeholder=a?'; اكتب كود 8086 هنا':t.dataset.pe;
 document.querySelectorAll('.lg>details').forEach((d,i)=>{d.dataset.en=d.dataset.en||d.innerHTML;d.innerHTML=a?'<summary>'+AG[i][0]+'</summary><div>'+AG[i][1]+'</div>':d.dataset.en});tl();ui();tmLb()}
function tmLb(){if(!PL)return;const a=LG=='ar',kb=g('tkb');kb.textContent=a?'\u203A':'\u2039';kb.title=a?'خطوة للخلف':'Back one step';kb.setAttribute('aria-label',kb.title);tkQz(PL,a);if(PL.nx)tkNq(PL);tmGo(PL);tmCv(PL)}
function tl(){const a=LG=='ar';document.querySelectorAll('[data-ar]').forEach(e=>{e.dataset.en=e.dataset.en||e.textContent;e.textContent=a?e.dataset.ar:e.dataset.en});
 g('tsn').innerHTML=(sn?IV:IX)+(sn?(a?'الصوت':'Sound'):(a?'صامت':'Muted'));g('tlg').innerHTML=IT+(a?'English':'العربية');g('pwr').title=a?'Power: مسح الذاكرة والسجلات':'Power: clears memory and registers';g('pwr').setAttribute('aria-label',g('pwr').title);
 g('tfz').innerHTML=FZ(g('tfr').value);g('tfz').title=(a?'حجم الخط ':'Text size ')+g('tfr').value+'%';tmL()}
[['#asr','تجميع وتشغيل'],['#asb','تجميع'],['#asc','نسخ'],['#ass','حفظ .asm'],['#asx','مسح'],['#ld','تحميل'],['#lc','مسح']].forEach(([q,a])=>document.querySelector(q).dataset.ar=a);
['السجلات','الذاكرة (RAM 00000–3FFFF)','تحميل برنامج','محرر Assembly','دليل المختبر'].forEach((a,i)=>document.querySelectorAll('.card.gd>summary')[i].dataset.ar=a);
/* Training Mode: top-centre toggle with a switch animation (state is saved; no animation on page load) */
let TM=LS('m86m')=='t',tmb=0,TO=+LS('m86p')||1,tmLg='',tmY=0,TV=0,PL=0,HLT=[],tmTy=0,DN={},uaAsk=0,UL=+LS('m86ua')||0;try{DN=JSON.parse(LS('m86d')||'{}')||{}}catch(e){}const ttm=g('ttm'),tmo=g('tmo'),tmd=tmo.querySelector('.tmo-d');
function tmL(){const a=LG=='ar';ttm.querySelector('.tml').textContent=a?'تدريب':'Training';ttm.setAttribute('aria-label',a?'وضع التدريب':'Training Mode');ttm.title=TM?(a?'العودة إلى الوضع العادي':'Back to normal mode'):(a?'وضع التدريب':'Training Mode');tmX()}
function tmS(){if(!TM)tmEnd();D.dataset.mode=TM?'training':'normal';ttm.classList.toggle('on',TM);ttm.setAttribute('aria-pressed',TM);tmL()}
ttm.onclick=()=>{if(tmb)return;tmb=1;const a=LG=='ar',k=TM?'out':'in',w=innerWidth,h=innerHeight,x=w/2,y=h/2,sp=(p,q)=>tmo.style.setProperty(p,q);
 sp('--x',x+'px');sp('--y',y+'px');sp('--d',2*Math.ceil(Math.hypot(Math.max(x,w-x),Math.max(y,h-y)))+'px');
 tmo.dataset.k=k;tmo.dir=a?'rtl':'ltr';tmZ(k=='in');
 tmo.querySelector('.tmo-t').textContent=k=='in'?(a?'وضع التدريب':'Training Mode'):(a?'الوضع العادي':'Normal Mode');
 tmo.querySelector('.tmo-s').textContent=k=='in'?(a?'الوضع التعليمي مفعّل':'Educational mode is on'):(a?'العودة إلى الوضع القياسي':'Back to the standard kit');
 let f=0,t2;const flip=()=>{if(f)return;f=1;TM=!TM;LS('m86m',TM?'t':'n');tmS();{const sq=sn;sn=false;g('pwr').click();sn=sq}document.dispatchEvent(new CustomEvent('m86:mode',{detail:{training:TM}}))},t1=setTimeout(flip,620),
 end=()=>{clearTimeout(t1);clearTimeout(t2);tmd.removeEventListener('animationend',end);flip();tmo.classList.remove('go');tmb=0;if(TM){tmLg=LG;tmG()}};
 tmo.classList.remove('go');void tmo.offsetWidth;tmo.classList.add('go');tmd.addEventListener('animationend',end);t2=setTimeout(end,2400)};
window.tmoMode=function(){if(!TM)return;TM=false;LS('m86m','n');tmS();{const sq=sn;sn=false;g('pwr').click();sn=sq}document.dispatchEvent(new CustomEvent('m86:mode',{detail:{training:TM}}))};
window.tmoView=function(k,x,y,flip){if(tmb)return false;tmb=1;const a=LG=='ar',w=innerWidth,h=innerHeight,sp=(p,q)=>tmo.style.setProperty(p,q),
 T={in:[a?'\u0648\u0636\u0639 \u0627\u0644\u062a\u062f\u0631\u064a\u0628':'Training Mode',a?'\u0627\u0644\u0648\u0636\u0639 \u0627\u0644\u062a\u0639\u0644\u064a\u0645\u064a \u0645\u0641\u0639\u0651\u0644':'Educational mode is on'],
 out:[a?'\u0627\u0644\u0648\u0636\u0639 \u0627\u0644\u0639\u0627\u062f\u064a':'Normal Mode',a?'\u0627\u0644\u0639\u0648\u062f\u0629 \u0625\u0644\u0649 \u0627\u0644\u0648\u0636\u0639 \u0627\u0644\u0642\u064a\u0627\u0633\u064a':'Back to the standard kit'],
 asm:[a?'\u0645\u062d\u0631\u0631 Assembly':'Assembly Editor',a?'\u0627\u0643\u062a\u0628 Assembly \u0623\u0648 \u0627\u0644\u0635\u0642 \u0628\u0627\u064a\u062a\u0627\u062a Hex':'Write 8086 assembly or paste hex bytes'],
 lab:[a?'\u062f\u0644\u064a\u0644 \u0627\u0644\u0645\u062e\u062a\u0628\u0631':'Lab Guide',a?'\u0627\u0644\u0645\u0641\u0627\u062a\u064a\u062d \u0648\u0627\u0644\u0634\u0627\u0634\u0627\u062a \u0648\u0627\u0644\u062a\u0639\u0644\u064a\u0645\u0627\u062a \u0628\u064a\u0646 \u064a\u062f\u064a\u0643':'Keys, displays and instructions at hand']}[k];
 x=w/2;y=h/2;sp('--x',x+'px');sp('--y',y+'px');sp('--d',2*Math.ceil(Math.hypot(Math.max(x,w-x),Math.max(y,h-y)))+'px');
 tmo.dataset.k=k;tmo.dir=a?'rtl':'ltr';tmZ(k!='out',k);tmo.querySelector('.tmo-t').textContent=T[0];tmo.querySelector('.tmo-s').textContent=T[1];
 let f=0,t2;const run=()=>{if(f)return;f=1;flip()},t1=setTimeout(run,620),
 end=()=>{clearTimeout(t1);clearTimeout(t2);tmd.removeEventListener('animationend',end);run();tmo.classList.remove('go');tmb=0};
 tmo.classList.remove('go');void tmo.offsetWidth;tmo.classList.add('go');tmd.addEventListener('animationend',end);t2=setTimeout(end,2400);return true};
g('tq1').onclick=()=>g('tlg').click();
g('tq2').onclick=()=>g('tfz').click();
g('tq3').onclick=()=>{g('tsn').click();tmX()};
function tmX(){const a=LG=='ar',s=(e,t)=>{e.title=t;e.setAttribute('aria-label',t)};
 s(g('tq1'),a?'English':'العربية');s(g('tq2'),(a?'حجم الخط ':'Text size ')+g('tfr').value+'%');s(g('tq3'),sn?(a?'الصوت يعمل':'Sound on'):(a?'الصوت صامت':'Sound muted'));g('tq3').innerHTML=sn?IV:IX;g('tq1').innerHTML=IT;g('tq2').innerHTML=FZ(g('tfr').value);
 g('tklv').lastElementChild.textContent=a?'المستويات':'Levels';g('tklv').setAttribute('aria-label',a?'المستويات':'Levels');g('tmv').innerHTML=TV?tmI(a):Array.from({length:10},(_,i)=>{const n=i+1,o=n<=TO||n<=UL;return '<button type=button class="lv'+(o?(n<TO?' dn':' cur'):'')+'" data-n='+n+(o?'':' disabled')+'><span class=n>'+n+'</span><span class=tx><b>'+(a?'المستوى ':'Level ')+n+'</b><i>'+(o?(n<TO?(a?'مكتمل':'Done'):(n==1?(a?'هيا نبدأ':"Let's begin"):(a?'أكمل':'Continue'))):(a?'مقفل':'Locked'))+'</i></span><span class=st>'+(o?(n<TO?tkCk():'\u25B6'):'<svg class="ic" viewBox="0 0 24 24" aria-hidden="true"><rect x="5" y="10.5" width="14" height="10" rx="2.5"/><path d="M8.5 10.5V8a3.5 3.5 0 0 1 7 0v2.5"/><circle class="lf" cx="12" cy="15.5" r="1.3"/></svg>')+'</span></button>'}).join('')+tmUa(a);if(TM&&!tmb&&tmLg!=LG){tmLg=LG;PL?tmSt():tmG()}}
function tmCnt(){return Object.keys(LV).filter(k=>(LV[k]||[]).length).length}
function tmUa(a){const c=tmCnt();if(Math.max(TO,UL)>=c)return '';return uaAsk?'<div class=ua><p>'+(a?'هل تريد فتح كل المراحل المتاحة ('+c+') دون إكمالها؟':'Unlock all available stages ('+c+') without completing them?')+'</p><div><button type=button class=uay>'+(a?'نعم':'Yes')+'</button><button type=button class=uan>'+(a?'لا':'No')+'</button></div></div>':'<button type=button class="lv ua0"><span class=n>\uD83D\uDD13</span><span class=tx><b>'+(a?'فتح كل المراحل':'Unlock all stages')+'</b><i>'+(a?'يفتح '+c+' مراحل':'Opens '+c+' stages')+'</i></span></button>'}
const TG={en:"Hi!\u00a0I'm TKE Bot. Open the levels menu (\u2630) and pick the level that suits you. I'll help you step by step.",ar:'أهلاً!\u00a0أنا TKE Bot. افتح قائمة المستويات (\u2630) واختر المستوى المناسب لك، وسأساعدك خطوة بخطوة.'};
/* welcome: the menu button (or the level list, once the menu is open) glows orange until a level is chosen */
function tmWg(){const w=!!tmW&&TM;mn.classList.toggle('tkw',w&&mp.hidden);g('tmv').classList.toggle('tkw',w&&!mp.hidden)}
function tmG(){g('tmw').classList.remove('fin');tmW=TV?0:1;tmWg();tmSay(TG[LG=='ar'?'ar':'en'])}
/* TKE Bot text renderer: one sentence per line, step badges, label chips, code chips, separate hint block */
const BR=/^(?:Step\s+(\d+)\s*:|⁦?(\d+)⁩?\s*\))\s*/,
LB=/^(Question|Goal|Result|Task|Objective|Note|Next|Last one|Hint|تلميح|السؤال|الهدف|النتيجة|المهمة|ملاحظة|التالي|الأخيرة)\s*:\s*/,
PC=/^[A-Z]{2,5}(?: [A-Z0-9\[\]+\-]+(?:,[A-Z0-9\[\]+\-]+)*)?$/,
HX=/(^|[^\w])((?:[0-9A-F]{2} )+[0-9A-F]{2})(?![\w])/g,
KY=/(^|[^\w\-\/<>])(RESET|NEXT|TTY|GO|EB|EW|ER|REG)(?![\w=\-\/])/g,
esc=x=>x.replace(/[&<>]/g,c=>'&#'+c.charCodeAt(0)+';'),
spl=x=>x.replace(/([.!?؟])[ \t]+(?=\S)/g,(m,c,o)=>x.slice(Math.max(0,o-3),o)=='Fig'?m:c+'\n'),
fmt=x=>esc(x).split(/(\u0002[^\u0003]*\u0003?)/).map((p,i)=>i%2?(c=>'<code class="cd'+(/[a-z]{3,}|[\u0600-\u06FF]/.test(c)?' w':'')+'">'+c+'</code>')(p.replace(/[\u0002\u0003]/g,'')):p.replace(HX,'$1<code>$2</code>').replace(KY,'$1<b class=kk>$2</b>')).join('');
function tmBk(x,lead){let o='',k=0;
 x.split('\n').forEach(L=>{
  if(!L.trim()&&!(lead&&!k))return;
  let b='',m,lb='';
  if(m=BR.exec(L)){b=m[1]||m[2];L=L.slice(m[0].length)}
  else if(m=/^\s*•\s*/.exec(L)){b='•';L=L.slice(m[0].length)}
  if(m=LB.exec(L)){lb='<b class="tlb'+(/^(Hint|تلميح)$/.test(m[1])?' h':'')+'">'+esc(m[1])+'</b>';L=L.slice(m[0].length)}
  const bl=b=='•';
  spl(L).split('\n').forEach((q,j)=>{
   const z=q.replace(/[⁦⁩]/g,''),pc=PC.test(z);
   o+='<div class="tl'+(j?(b&&!bl?' c':''):(k&&!bl?' n':''))+(pc?' pc':'')+'">'+(!j&&b?'<i class="sb'+(bl?' bd':'')+'">'+b+'</i>':'')+'<span class=tx>'+(!j?(lead&&!k?lead:'')+lb:'')+(pc?'<code class=cd>'+esc(z)+'</code>':fmt(q))+'</span></div>'});
  k++});
 return o}
function tmRn(el,s){const ar=LG=='ar',p=s.split('\u0001');
 let h=tmBk(p[0]);
 if(p.length>1)h+='<div class=thn>'+tmBk(p[1].replace(/^\s*(Hint|تلميح)\s*:\s*/,''),'<b class=tlb>'+(ar?'تلميح':'Hint')+'</b>')+'</div>';
 el.innerHTML=h||'<div class=tl><span class=tx></span></div>';
 const x=el.querySelectorAll('.tx');if(x.length)x[x.length-1].classList.add('lst')}
/* a step's leading label (Goal, Task, Next...) is shown in the fixed badge above TKE Bot instead of inside the text */
function tmLm(x){return /^\s*\u2066?(Goal|Result|Task|Objective|Note|Next|Last one|Common mistake|الهدف|النتيجة|المهمة|ملاحظة|التالي|الأخيرة|خطأ شائع)\u2069?\s*:\s*/.exec(x)}
function tmUc(x){return LG=='ar'?x:x.replace(/^[a-z]/,c=>c.toUpperCase())}
function tmLs(x){const m=tmLm(x);return m?tmUc(x.slice(m[0].length)):x}
function tmSay(s,cb,f){clearInterval(tmY);tmTy=1;const t=g('tmt'),r=document.querySelector('.tmr'),kk=g('tkk'),m=tmLm(s);let n=0;if(m){n=m[0].length;s=tmUc(s.slice(n))}if(kk)kk.textContent=m?m[1]:(kk.dataset.l||'');kk.classList.toggle('wn',!!m&&/^(Common mistake|خطأ شائع)$/.test(m[1]));const c=Array.from(s);let i=Math.max(0,(f||0)-n);t._h=0;tmRn(t,c.slice(0,i).join(''));t.classList.add('ty');r.classList.add('say');const ST=document.documentElement.classList.contains('lite')?3:2;tmY=setInterval(()=>{i=Math.min(c.length,i+ST);tmRn(t,c.slice(0,i).join(''));if(!t._h)t.scrollTop=t.scrollHeight;if(i>=c.length){clearInterval(tmY);tmTy=0;t.classList.remove('ty');r.classList.remove('say');cb&&cb()}},12*ST)}
(function(){const t=g('tmt');if(!t)return;let y0=0;const u=()=>{const d=t.scrollHeight-t.scrollTop-t.clientHeight;t.classList.toggle('mu',t.scrollTop>3);t.classList.toggle('md',d>3);if(d<4)t._h=0};t.addEventListener('wheel',e=>{if(e.deltaY<0)t._h=1},{passive:true});t.addEventListener('touchstart',e=>{y0=e.touches[0].clientY},{passive:true});t.addEventListener('touchmove',e=>{if(e.touches[0].clientY>y0+4)t._h=1},{passive:true});t.addEventListener('scroll',u,{passive:true});new MutationObserver(u).observe(t,{childList:true,subtree:true,characterData:true});addEventListener('resize',u);u()})();
window.tkeSay=tmSay;
const LV={
1:[{k:'c',t:['The 8086 chip','شريحة 8086'],s:[['The 8086 is a 40-pin processor that runs assembly programs.','معالج 8086 شريحة بـ40 رجلاً تنفذ برامج لغة التجميع.',''],['It works with the 8279, 8255 and 8087 chips for keyboard, display and I/O.','يعمل مع الشرائح 8279 و8255 و8087 للوحة المفاتيح والعرض والإدخال والإخراج.','']]},
{k:'c',t:['Keyboard','لوحة المفاتيح'],s:[['16 hex keys (0-F) enter addresses and data.','16 مفتاحاً سداسياً (0-F) لإدخال العناوين والبيانات.','0 1 2 3 4 5 6 7 8 9 A B C D E F'],['12 function keys edit, control and run, like RESET, INS, DEL, REG, NEXT and TTY.','12 مفتاحاً وظيفياً للتحرير والتحكم والتشغيل مثل RESET وINS وDEL وREG وNEXT وTTY.','FKEYS']]},
{k:'c',t:['Main commands','أهم الأوامر'],s:[['RESET restarts the kit and shows the sign-on message.','RESET يعيد تشغيل الكيت ويعرض رسالة البداية.','RESET'],['EB / EW examine a byte / word of memory. ER examines a register.','EB وEW لفحص بايت أو كلمة من الذاكرة، وER لفحص مسجّل.','EB EW ER'],['NEXT moves to the data field, then to the next address.','NEXT ينقلك إلى حقل البيانات ثم إلى العنوان التالي.','NEXT'],['GO runs a program: GO, address, then TTY.','GO لتشغيل برنامج: GO ثم العنوان ثم TTY.','GO TTY']]},
{k:'c',t:['Display and memory','الشاشة والذاكرة'],s:[['8 seven-segment digits: 4 show the address, 4 show the data, all in hex.','8 خانات سباعية: 4 للعنوان و4 للبيانات، كلها بالنظام السداسي.','DSP'],['RAM starts at 00000. At RESET the 8086 jumps to FFFF0, the monitor ROM.','الذاكرة RAM تبدأ من 00000، وعند RESET ينتقل المعالج إلى FFFF0 وهو برنامج المراقب.','']]},
{k:'c',t:['Registers','المسجلات'],s:[['Registers are small memory cells inside the 8086 that hold data while a program runs.','المسجلات خلايا ذاكرة صغيرة داخل المعالج 8086 تحتفظ بالبيانات أثناء تنفيذ البرنامج.',''],
['Reach a register: press RESET, then ER, then the key labelled AX (key 0).','للوصول إلى مسجل: اضغط RESET ثم ER ثم المفتاح المكتوب عليه AX وهو 0.','r:AX'],
['You are inside AX. The data digits show its 4 hex digits. The left two are AH, the high byte.','أنت الآن داخل AX. خانات البيانات تعرض أرقامه الأربعة. الخانات على اليسار هي AH وهو البايت العلوي.','r:AX dh'],
['The right two digits are AL, the low byte. BX, CX and DX split the same way.','الخانات على اليمين هي AL وهو البايت السفلي. وBX وCX وDX تنقسم بالمثل.','r:AX r:BX r:CX r:DX dl'],
['Set it directly: type 1234, then NEXT to save it in AX.','لوضع قيمة مباشرة: اكتب 1234 ثم NEXT لحفظها في AX.','r:AX'],
['Press TTY to leave. AX = 1234, with no program or memory needed.','اضغط TTY للخروج. صار AX = 1234 دون برنامج ولا ذاكرة.','r:AX']]},
{k:'e',t:['Example 1: AABB into AX','مثال 1: وضع AABB في AX'],s:[['Goal: store AABB in register AX. Write the program in memory at 400.','الهدف: خزّن القيمة AABB في المسجل AX، بكتابة برنامج في الذاكرة عند العنوان 400.','r:AX'],['Step 1: switch the kit on, then press RESET.','1) شغّل الكيت ثم اضغط RESET.','RESET'],['Step 2: press EB, then type the address 400.','2) اضغط EB ثم اكتب العنوان 400.','EB 0 4'],['Step 3: press NEXT to open the data field.','3) اضغط NEXT لفتح حقل البيانات.','NEXT'],['Step 4: type ⟦B8|MOV AX,AABB⟧, then NEXT. The address moves to 00401.','4) اكتب ⟦B8|MOV AX,AABB⟧ ثم NEXT فينتقل العنوان إلى 00401.','B 8 NEXT'],['Step 5: type ⟦BB, NEXT, then AA|the value AABB, low byte first⟧, NEXT.','5) اكتب ⟦BB ثم NEXT ثم AA|القيمة AABB بالبايت الأدنى أولاً⟧ ثم NEXT.','B A NEXT'],['Step 6: type ⟦CC|HLT⟧, then NEXT. The program is stored.','6) اكتب ⟦CC|HLT⟧ ثم NEXT فيُحفظ البرنامج.','F 4 NEXT'],['Step 7: press TTY, then GO, and type 400.','7) اضغط TTY ثم GO ثم اكتب 400.','TTY GO 0 4'],['Step 8: press TTY to run. AX now holds AABB.','8) اضغط TTY للتنفيذ فيصبح AX = AABB.','TTY r:AX']]},
{k:'e',t:['Example 2: 45h into AL','مثال 2: 45h في AL'],s:[['Goal: store 45h in register AL. Write the program in memory at 600.','الهدف: خزّن القيمة 45h في المسجل AL، بكتابة برنامج في الذاكرة عند العنوان 600.','r:AX'],['Step 1: press EB, type 600, then NEXT.','1) اضغط EB واكتب 600 ثم NEXT.','EB 6 0 0 NEXT'],['Step 2: type ⟦B0, NEXT, 45, NEXT|MOV AL,45⟧, then ⟦CC, NEXT|HLT⟧. The program is stored.','2) اكتب ⟦B0 ثم NEXT ثم 45 ثم NEXT|MOV AL,45⟧ ثم ⟦CC ثم NEXT|HLT⟧ فيُحفظ البرنامج.','B 0 NEXT 4 5 NEXT C C NEXT'],['Step 3: press TTY, GO, then type 600.','3) اضغط TTY ثم GO ثم اكتب 600.','TTY GO 6 0 0'],['Step 4: press TTY to run. AL = 45, the low half of AX.','4) اضغط TTY للتنفيذ فيصبح AL = 45.','TTY r:AX']]},
{k:'e',t:['Example 3: 6Ch into AH','مثال 3: 6Ch في AH'],s:[['Goal: store 6Ch in register AH. Write the program in memory at 500.','الهدف: خزّن القيمة 6Ch في المسجل AH، بكتابة برنامج في الذاكرة عند العنوان 500.','r:AX'],['Step 1: press EB, type 500, NEXT, then ⟦B4|MOV AH,6C⟧, NEXT.','1) اضغط EB واكتب 500 ثم NEXT ثم ⟦B4|MOV AH,6C⟧ ثم NEXT.','EB 5 0 0 NEXT B 4 NEXT'],['Step 2: type ⟦6C, NEXT, then CC, NEXT|the value 6C, then HLT⟧. The program is stored.','2) اكتب ⟦6C ثم NEXT ثم CC ثم NEXT|القيمة 6C ثم HLT⟧ فيُحفظ البرنامج.','6 C NEXT C C NEXT'],['Step 3: press TTY, GO, type 500, then TTY. AH = 6C.','3) اضغط TTY ثم GO ثم اكتب 500 ثم TTY فيصبح AH = 6C.','TTY GO 5 0 0 TTY r:AX']]},
{k:'x',t:['Exercise 1: AX values','تمرين 1: قيم AX'],s:[['Load DFA1 into AX, then run the program.','ضع DFA1 في AX ثم نفّذ البرنامج.','r:AX','Hint: B8 A1 DF CC.','تلميح: B8 A1 DF CC.','AX=DFA1'],['Now load 869B into AX the same way.','الآن ضع 869B في AX بنفس الطريقة.','r:AX','Hint: B8 9B 86 CC.','تلميح: B8 9B 86 CC.','AX=869B']]},
{k:'x',t:['Exercise 2: AL and AH','تمرين 2: AL وAH'],s:[['Load 7B into AL and 8F into AH, then run it.','ضع 7B في AL و8F في AH ثم نفّذه.','r:AX','Hint: B0 7B, B4 8F, then CC.','تلميح: B0 7B وB4 8F ثم CC.','AX=8F7B']]},
{k:'q',t:['Final test','الاختبار النهائي'],q:[['The kit has 16 hex keys and 12 function keys.','يحتوي الكيت على 16 مفتاحاً سداسياً و12 مفتاحاً وظيفياً.',true],['Registers are small, fast storage cells inside the CPU that temporarily hold data and addresses.','المسجلات (Registers) خلايا تخزين صغيرة وسريعة داخل المعالج تحتفظ مؤقتاً بالبيانات والعناوين.',true],['B8 BB AA loads AABB into BX.','الأمر B8 BB AA يضع AABB في BX.',false,'B8 is MOV AX, so AABB goes into AX, not BX.','الأمر B8 هو MOV AX، فتُخزَّن AABB في AX وليس BX.']]}],
2:[{k:'c',t:['16-bit and 8-bit','16 بت و8 بت'],s:[['Each 16-bit register splits into two 8-bit halves: AX = AH + AL.','كل مسجل 16 بت ينقسم إلى نصفين 8 بت: AX = AH + AL.','r:AX'],['The same for BX, CX and DX: the general-purpose registers.','وكذلك BX وCX وDX وهي المسجلات العامة.','r:BX r:CX r:DX']]},
{k:'c',t:['Register roles','وظائف المسجلات'],s:[['AX accumulator, BX base index, CX count, DX data. Their keys are 0, 1, 2 and 3.','AX المجمّع وBX القاعدة وCX العدّاد وDX البيانات، ومفاتيحها 0 و1 و2 و3.','r:AX r:BX r:CX r:DX 0 1 2 3'],['SP stack pointer, BP base pointer, SI source index, DI destination index (keys 4, 5, 6, 7). IP is the instruction pointer (key C) and FL the flags (key D).','SP مؤشر المكدس وBP مؤشر القاعدة وSI فهرس المصدر وDI فهرس الوجهة (المفاتيح 4 و5 و6 و7). وIP مؤشر التعليمات (المفتاح C) وFL الأعلام (المفتاح D).','r:SP r:BP r:SI r:DI r:IP r:FL 4 5 6 7 C D'],['Segment registers hold segment addresses: CS code, DS data, SS stack, ES extra (keys 8, 9, A, B).','مسجلات المقاطع تحمل عناوين المقاطع: CS للشيفرة وDS للبيانات وSS للمكدس وES للإضافي (المفاتيح 8 و9 وA وB).','r:CS r:DS r:SS r:ES 8 9 A B']]},
{k:'c',t:['Memory order','ترتيب الذاكرة'],s:[['A 16-bit value is stored low byte first: AB at 500 and 7D at 501 make 7DAB.','القيمة 16 بت تُخزّن بالبايت الأدنى أولاً: AB عند 500 و7D عند 501 تعطي 7DAB.','']]},
{k:'e',t:['Example 1: memory to CX to AX','مثال 1: من الذاكرة إلى CX ثم AX'],s:[['Goal: copy memory 500-501 into CX, then into AX. Data: AB at 500, 7D at 501.','الهدف: نسخ الذاكرة 500-501 إلى CX ثم AX. البيانات: AB عند 500 و7D عند 501.','r:CX r:AX'],['Step 1: press EB, type 500, press NEXT.','1) اضغط EB واكتب 500 ثم NEXT.','EB 0 5 NEXT'],['Step 2: type AB, NEXT, then 7D, NEXT. The data is stored.','2) اكتب AB ثم NEXT ثم 7D ثم NEXT فتُحفظ البيانات.','A B 7 D NEXT'],['Step 3: press RESET, then EB and type 700 to write the program.','3) اضغط RESET ثم EB واكتب 700 لكتابة البرنامج.','RESET EB 7 0'],['Step 4: NEXT, then ⟦8B 0E 00 05|MOV CX,[0500]⟧, ⟦8B C1|MOV AX,CX⟧, ⟦CC|HLT⟧, each followed by NEXT.','4) NEXT ثم ⟦8B 0E 00 05|MOV CX,[0500]⟧ ثم ⟦8B C1|MOV AX,CX⟧ ثم ⟦CC|HLT⟧ مع NEXT بعد كل بايت.','NEXT 8 B 0 E 5 C 1 F 4'],['Step 5: press TTY, GO, type 700, then TTY.','5) اضغط TTY ثم GO ثم اكتب 700 ثم TTY.','TTY GO 7 0 TTY'],['Result: CX and AX both hold 7DAB.','النتيجة: CX وAX يحملان 7DAB.','r:CX r:AX']]},
{k:'e',t:['Example 2: DL and DH','مثال 2: DL وDH'],s:[['Goal: DL = 8C and DH = [600] = AF, so DX = AF8C.','الهدف: DL = 8C وDH = [600] = AF فيصبح DX = AF8C.','r:DX'],['Step 1: first store AF at 600: EB, 600, NEXT, AF, NEXT.','1) خزّن AF أولاً عند 600: EB ثم 600 ثم NEXT ثم AF ثم NEXT.','r:DX'],['Step 2: press RESET, EB, 800, NEXT, then enter ⟦B2 8C|MOV DL,8C⟧, each byte then NEXT.','2) اضغط RESET ثم EB و800 وNEXT، ثم أدخل ⟦B2 8C|MOV DL,8C⟧ مع NEXT بعد كل بايت.',''],['Step 3: enter ⟦8A 36 00 06|MOV DH,[0600]⟧, each byte then NEXT.','3) أدخل ⟦8A 36 00 06|MOV DH,[0600]⟧ مع NEXT بعد كل بايت.',''],['Step 4: enter ⟦8B C2|MOV AX,DX⟧ then ⟦CC|HLT⟧, each byte then NEXT.','4) أدخل ⟦8B C2|MOV AX,DX⟧ ثم ⟦CC|HLT⟧ مع NEXT بعد كل بايت.',''],['Step 5: run with TTY, GO, 800, TTY. AX shows AF8C.','5) نفّذ بـ TTY ثم GO ثم 800 ثم TTY فيظهر AX = AF8C.','r:AX']]},
{k:'e',t:['Example 3: BX to memory','مثال 3: من BX إلى الذاكرة'],s:[['Goal: BX = 943E, then store BX at 650.','الهدف: BX = 943E ثم تخزينه عند 650.','r:BX'],['Step 1: press EB, 400, NEXT, then enter ⟦BB 3E 94|MOV BX,943E⟧, each byte then NEXT.','1) اضغط EB و400 وNEXT، ثم أدخل ⟦BB 3E 94|MOV BX,943E⟧ مع NEXT بعد كل بايت.','r:BX'],['Step 2: enter ⟦89 1E 50 06|MOV [0650],BX⟧ then ⟦CC|HLT⟧, each byte then NEXT.','2) أدخل ⟦89 1E 50 06|MOV [0650],BX⟧ ثم ⟦CC|HLT⟧ مع NEXT بعد كل بايت.','r:BX'],['Step 3: run with TTY, GO, 400, TTY.','3) نفّذ بـ TTY ثم GO ثم 400 ثم TTY.','r:BX'],['Step 4: check memory: EB, 650, NEXT. 3E is at 650 and 94 at 651.','4) افحص الذاكرة: EB ثم 650 ثم NEXT: ستجد 3E عند 650 و94 عند 651.','r:BX']]},
{k:'x',t:['Exercise: DX to AX','تمرين: DX إلى AX'],s:[['Make AX show 3C5A: put 5A in DL, 3C in DH, then copy DX to AX.','اجعل AX يعرض 3C5A: ضع 5A في DL و3C في DH ثم انسخ DX إلى AX.','r:DX r:AX','Hint: B2 5A, B6 3C, 8B C2, then CC.','تلميح: B2 5A وB6 3C و8B C2 ثم CC.','AX=3C5A']]},
{k:'q',t:['Final test','الاختبار النهائي'],q:[['AX is made of AH (high) and AL (low).','AX يتكوّن من AH (العلوي) وAL (السفلي).',true],['MOV AX,CX copies AX into CX.','الأمر MOV AX,CX ينسخ AX إلى CX.',false,'The destination is written first: MOV AX,CX copies CX into AX.','الوجهة تُكتب أولاً: الأمر MOV AX,CX ينسخ CX إلى AX.'],['A 16-bit value is stored with its low byte at the lower address.','القيمة 16 بت تُخزّن بالبايت الأدنى في العنوان الأقل.',true]]}],
/* Level 3: MOV instruction machine code (Experiment 3). Exercise checks: AX=.., AL=.. or M<addr>=<bytes>, joined with & */
3:[
{k:'c',t:['MOV instruction','تعليمة MOV'],s:[
['The 8086 has three groups of instructions: data movement, arithmetic and logic, and program control.','لدى 8086 ثلاث مجموعات من التعليمات: نقل البيانات، والعمليات الحسابية والمنطقية، والتحكم في البرنامج.',''],
['Each instruction has its own binary code. The chip decodes it and does the job.','لكل تعليمة كود ثنائي خاص بها، يفك المعالج شيفرته وينفّذ العمل المطلوب.',''],
['MOV is the main data movement instruction. It transfers data from a source to a destination.','التعليمة MOV هي أهم تعليمات نقل البيانات. وهي تنقل البيانات من المصدر (source) إلى الوجهة (destination).',''],
['The destination is written first: MOV AX,BX copies BX into AX, and BX keeps its value.','نكتب الوجهة أولاً ثم المصدر. مثال: MOV AX,BX تنسخ محتوى BX إلى AX، ويبقى BX محتفظاً بقيمته.','r:AX r:BX'],
['Goal of this level: understand how each MOV instruction becomes machine code bytes.','هدف هذا المستوى: فهم كيف تتحول كل تعليمة MOV إلى بايتات من الكود الآلي.','']]},
{k:'c',t:['MOV code format','صيغة كود MOV'],s:[
['A MOV instruction has four parts: opcode, MOD-REG-R/M, displacement and immediate.','تتكوّن تعليمة MOV من أربعة أجزاء:\n1) الأوبكود (opcode)\n2) بايت MOD-REG-R/M\n3) الإزاحة (displacement)\n4) القيمة الفورية (immediate)',''],
['Sizes: opcode 1-2 bytes, MOD-REG-R/M 0-1 byte, displacement 0-2 bytes, immediate 0-2 bytes.','الأحجام: الأوبكود 1-2 بايت، وMOD-REG-R/M من 0 إلى 1 بايت، والإزاحة من 0 إلى 2 بايت، والقيمة الفورية من 0 إلى 2 بايت.',''],
['Not every part is always present. MOV AX,BX is only two bytes: opcode and MOD-REG-R/M (8B C3).','لا تظهر الأجزاء الأربعة دائماً. مثال: التعليمة MOV AX,BX من بايتين فقط: الأوبكود ثم بايت MOD-REG-R/M. كودها: 8B C3.','b:8B-C3'],
['MOV CX,[0500] adds a 16-bit address: 8B 0E 00 05. A 16-bit value is stored low byte first.','التعليمة MOV CX,[0500] تضيف عنواناً من 16 بت. كودها: 8B 0E 00 05.\nلاحظ أن العنوان 0500 كُتب 00 05، لأن القيمة 16 بت تُخزّن بالبايت الأدنى أولاً.','b:8B-0E-00-05'],
['MOV with an immediate value into a register has no MOD-REG-R/M byte. Its opcode is 1011 W REG: W picks 8 or 16 bits and REG is the register code.','عندما ننقل قيمة فورية (رقماً نكتبه مباشرة) إلى مسجل، لا نحتاج إلى بايت MOD-REG-R/M.\nيتكوّن الأوبكود من 8 بتات: 1011 ثم W ثم REG.\nالبت W يحدد حجم القيمة: 8 بت أو 16 بت.\nوالحقل REG هو رمز المسجل.','b:B8-34-12'],
['So B0-B7 load an 8-bit value and B8-BF a 16-bit value. MOV AX,1234 = B8 34 12. MOV BL,5A = B3 5A.','إذن الأوبكودات من B0 إلى B7 تُستعمل لقيمة 8 بت، ومن B8 إلى BF لقيمة 16 بت.\nمثال: MOV AX,1234 كودها B8 34 12.\nومثال: MOV BL,5A كودها B3 5A.','b:B8-34-12']]},
{k:'c',t:['Opcode: D and W','الأوبكود: D وW'],s:[
['The opcode byte has 8 bits: six bits for the operation, then the bits D and W.','بايت الأوبكود من 8 بتات: ست بتات للعملية ثم البتان D وW.','t:DW g:dw:D:0 g:dw:W:0 b:8B-C2'],
['The six bits choose the operation: ADD, SUB, MOV... For MOV they are 100010.','البتات الست الأولى تحدد نوع العملية (ADD أو SUB أو MOV ...). وفي تعليمة MOV تكون قيمتها 100010.','t:DW b:8B-C2'],
['D is the direction. D=1: data goes to the register REG, so REG is the destination.','البت D هو اتجاه النقل. عندما D=1 تذهب البيانات إلى المسجل REG، أي أن REG هو الوجهة.','t:DW g:dw:D:0 g:dw:D:2 b:8B-C2'],
['D=0: data goes from REG to R/M, so R/M is the destination (usually memory).','عندما D=0 تذهب البيانات من REG إلى R/M، أي أن R/M هي الوجهة (غالباً الذاكرة).','t:DW g:dw:D:0 g:dw:D:1 b:89-D0'],
['W is the width. W=1: a word (16-bit). W=0: a byte (8-bit).','البت W هو عرض البيانات. عندما W=1 تكون كلمة (16 بت)، وعندما W=0 تكون بايت (8 بت).','t:DW g:dw:W:* b:8B-C2'],
['So MOV has four opcodes: 88 (D=0, W=0), 89 (D=0, W=1), 8A (D=1, W=0) and 8B (D=1, W=1).','إذن لـ MOV أربعة أوبكودات: 88 (D=0, W=0) و89 (D=0, W=1) و8A (D=1, W=0) و8B (D=1, W=1).','t:DW g:dw:D:* g:dw:W:* b:8B-C2'],
['Common mistake: thinking D=1 means the data comes from REG. It is the opposite: D=1 means the data goes to REG.','خطأ شائع: الظن أن D=1 تعني أن البيانات تأتي من REG. العكس صحيح: D=1 تعني أن البيانات تذهب إلى REG.','t:DW g:dw:D:0 g:dw:D:2 b:8B-C2']]},
{k:'c',t:['MOD-REG-R/M byte','بايت MOD-REG-R/M'],s:[
['The second byte of a data movement instruction is MOD-REG-R/M: 2 bits MOD, 3 bits REG, 3 bits R/M.','البايت الثاني في تعليمات نقل البيانات هو MOD-REG-R/M: بتان للحقل MOD وثلاث بتات للحقل REG وثلاث بتات للحقل R/M.','t:MOD b:8B-C2'],
['MOD sets the addressing mode. 00: no displacement. 01: 8-bit sign-extended displacement.','الحقل MOD يحدد نمط العنونة، أي طريقة الوصول إلى المعامل.\nإذا كان MOD=00 فلا توجد إزاحة.\nوإذا كان MOD=01 فهناك إزاحة من 8 بت.','t:MOD g:mod:00:* g:mod:01:* b:8B-C2'],
['10: 16-bit displacement. 11: R/M is a register.','وإذا كان MOD=10 فهناك إزاحة من 16 بت.\nوإذا كان MOD=11 فالمعامل R/M هو مسجّل وليس عنواناً في الذاكرة.','t:MOD g:mod:10:* g:mod:11:* b:8B-C2'],
['With MOD=11 both operands are registers. With MOD=00, 01 or 10 the R/M operand is in memory.','عند MOD=11 يكون المعاملان مسجّلين. وعند MOD=00 أو 01 أو 10 يكون المعامل R/M في الذاكرة.','t:MOD g:mod:00:* g:mod:01:* g:mod:10:* g:mod:11:* b:8B-C2'],
['REG always names a register. R/M names a register (MOD=11) or a memory address.','الحقل REG يحدد مسجلاً دائماً. أما R/M فتحدد مسجلاً (MOD=11) أو عنواناً في الذاكرة.','t:REG b:8B-C2'],
['Common mistake: thinking MOD=01 means a 16-bit displacement. MOD=01 is 8-bit, and MOD=10 is 16-bit.','خطأ شائع: الظن أن MOD=01 تعني إزاحة 16 بت. القيمة 01 هي إزاحة 8 بت، أما 10 فهي إزاحة 16 بت.','t:MOD g:mod:01:* g:mod:10:* b:8B-C2'],
['To write the byte in hex, split its 8 bits into two groups of 4. 1100 0010 = C2, and the other way round.','لكتابة البايت بنظام Hex قسّم بتاته الثمانية إلى مجموعتين من أربعة. 1100 0010 = C2 والعكس صحيح.','t:HEX g:hex:C g:hex:2 b:8B-C2'],
['Remember: MOD decides what R/M means. Next we read the REG and R/M tables.','تذكّر: الحقل MOD هو الذي يحدد معنى R/M. بعد ذلك نقرأ جداول REG وR/M.','t:MOD b:8B-C2']]},
{k:'c',t:['REG and R/M registers','المسجلات في REG وR/M'],s:[
['When MOD=11, the 3-bit code names a register and W picks the size: byte or word.','عند MOD=11 يحدد الرمز ذو الثلاث بتات مسجلاً، ويحدد W الحجم: بايت أو كلمة.','t:REG g:reg:H:1 g:reg:H:2 b:8B-C2'],
['W=0 (8-bit): 000 AL, 001 CL, 010 DL, 011 BL, 100 AH, 101 CH, 110 DH, 111 BH.','عند W=0 (8 بت): 000 AL و001 CL و010 DL و011 BL و100 AH و101 CH و110 DH و111 BH.','r:AX r:CX r:DX r:BX t:REG g:reg:*:1 b:8A-C2'],
['W=1 (16-bit): 000 AX, 001 CX, 010 DX, 011 BX, 100 SP, 101 BP, 110 SI, 111 DI.','عند W=1 (16 بت): 000 AX و001 CX و010 DX و011 BX و100 SP و101 BP و110 SI و111 DI.','r:AX r:CX r:DX r:BX r:SP r:BP r:SI r:DI t:REG g:reg:*:2 b:8B-C2'],
['Learn the 16-bit order: AX CX DX BX SP BP SI DI. Note that CX comes before BX.','احفظ ترتيب 16 بت: AX CX DX BX SP BP SI DI. لاحظ أن CX قبل BX.','t:REG g:reg:*:2 b:8B-C2'],
['REG is the destination when D=1 and the source when D=0. R/M is the other operand.','المسجل REG هو الوجهة عندما D=1 وهو المصدر عندما D=0، وR/M هو المعامل الآخر.','t:REG b:8B-C2'],
['Example: MOV AX,DX has D=1, W=1, MOD=11, REG=000 (AX), R/M=010 (DX).','مثال: في التعليمة MOV AX,DX تكون القيم هكذا:\nD=1 و W=1 و MOD=11\nREG=000 وهو AX\nR/M=010 وهو DX','r:AX r:DX t:REG g:reg:000:0 g:reg:000:2 g:reg:010:0 g:reg:010:2 g:reg:H:2 b:8B-C2'],
['The second byte is 11 000 010 = C2, so the code is 8B C2.','البايت الثاني هو 11 000 010 = C2، فيكون الكود 8B C2.','t:REG b:8B-C2 g:reg:000:0 g:reg:000:2 g:reg:010:0 g:reg:010:2 g:reg:H:2'],
['Common mistake: mixing CX and BX. In the code order, 001 is CX and 011 is BX.','خطأ شائع: الخلط بين CX وBX. في ترتيب الكود الرمز 001 هو CX والرمز 011 هو BX.','t:REG g:reg:001:0 g:reg:001:2 g:reg:011:0 g:reg:011:2 b:8B-C2']]},
{k:'c',t:['Memory addressing','عنونة الذاكرة'],s:[
['When MOD is 00, 01 or 10, R/M selects a memory address built from BX, BP, SI, DI and a displacement.','عندما يكون MOD هو 00 أو 01 أو 10 تحدد R/M عنواناً في الذاكرة يُبنى من BX وBP وSI وDI مع إزاحة.','t:RM g:rm:*:1 b:8B-0E-00-05'],
['R/M codes: 000 BX+SI, 001 BX+DI, 010 BP+SI, 011 BP+DI.','رموز R/M: 000 BX+SI و001 BX+DI و010 BP+SI و011 BP+DI.','t:RM g:rm:000:0 g:rm:000:1 g:rm:001:0 g:rm:001:1 g:rm:010:0 g:rm:010:1 g:rm:011:0 g:rm:011:1 b:8B-00'],
['100 SI, 101 DI, 110 direct address (it is BP when MOD is 01 or 10), 111 BX.','100 SI و101 DI و110 عنوان مباشر (وهي BP عندما يكون MOD هو 01 أو 10) و111 BX.','t:RM g:rm:100:0 g:rm:100:1 g:rm:101:0 g:rm:101:1 g:rm:110:0 g:rm:110:1 g:rm:111:0 g:rm:111:1 b:8B-0E-00-05'],
['MOD=00: no displacement. MOD=01: add D8, an 8-bit displacement. MOD=10: add D16, a 16-bit displacement.','MOD=00: بدون إزاحة. MOD=01: نضيف D8 أي إزاحة 8 بت. MOD=10: نضيف D16 أي إزاحة 16 بت.','t:MOD g:mod:00:* g:mod:01:* g:mod:10:* b:8A-45-02'],
['Special case: MOD=00 with R/M=110 is not [BP]. It means a direct address: a 16-bit address follows the byte.','حالة خاصة: عندما MOD=00 و R/M=110 فهذا لا يعني [BP]،\nبل يعني عنواناً مباشراً، ويأتي بعده عنوان من 16 بت.','t:RM g:rm:110:0 g:rm:110:1 b:8B-0E-00-05'],
['The displacement or address comes after MOD-REG-R/M, low byte first: 1234 is stored as 34 12.','تأتي الإزاحة أو العنوان بعد بايت MOD-REG-R/M بالبايت الأدنى أولاً: القيمة 1234 تُخزّن 34 12.','t:RM g:rm:*:1 b:8B-0E-34-12'],
['Examples: R/M=111 with MOD=01 is [BX+D8]. R/M=010 with MOD=10 is [BP+SI+D16].','أمثلة: R/M=111 مع MOD=01 تعني [BX+D8]. وR/M=010 مع MOD=10 تعني [BP+SI+D16].','t:RM g:rm:111:0 g:rm:111:1 g:rm:010:0 g:rm:010:1 b:8B-47-10'],
['Common mistake: reading MOD=00 with R/M=110 as [BP]. It is a direct address, and 2 address bytes follow.','خطأ شائع: قراءة MOD=00 مع R/M=110 على أنها BP. الصحيح أنها عنوان مباشر، ويليها بايتا العنوان.','t:RM g:rm:110:0 g:rm:110:1 b:8B-0E-00-05']]},
{k:'e',t:['Example 1: decode 8B EC','مثال 1: فك الكود 8B EC'],s:[
['Goal: interpret the machine code 8B EC.','الهدف: فك الكود الآلي 8B EC.',''],
['Step 1: write it in binary. 8B = 1000 1011 and EC = 1110 1100.','1) نكتبه ثنائياً: 8B = 1000 1011 وEC = 1110 1100.','t:HEX g:hex:8 g:hex:B g:hex:E g:hex:C b:8B-EC'],
['Step 2: the opcode byte 1000 1011 is 100010 + D=1 + W=1. So it is MOV, to the register REG, 16-bit.','2) بايت الأوبكود 1000 1011 يتكوّن من 100010 ثم D=1 ثم W=1.\nإذن هي MOV، والبيانات تذهب إلى المسجل REG، والحجم 16 بت.','t:DW b:8B-EC g:dw:D:0 g:dw:D:2 g:dw:W:0 g:dw:W:2'],
['Step 3: split the second byte EC = 11 101 100. MOD=11 means R/M is a register.','3) نقسم البايت الثاني EC = 11 101 100 إلى ثلاثة حقول.\nالحقل MOD=11 يعني أن R/M مسجّل.','t:MOD b:8B-EC g:mod:11:*'],
['Step 4: with W=1, REG=101 is BP and R/M=100 is SP.','4) مع W=1 يكون REG=101 هو BP وR/M=100 هو SP.','r:BP r:SP t:REG b:8B-EC g:reg:101:0 g:reg:101:2 g:reg:100:0 g:reg:100:2 g:reg:H:2'],
['Step 5: D=1, so REG (BP) is the destination. The instruction is MOV BP,SP.','5) بما أن D=1 فالوجهة هي REG (BP). إذن التعليمة هي MOV BP,SP.','r:BP r:SP t:DW b:8B-EC g:dw:D:0 g:dw:D:2'],
['Step 6: test it on the kit. Press RESET, EB, type 600, then NEXT.','6) جرّبها على الكيت: اضغط RESET ثم EB واكتب 600 ثم NEXT.','RESET EB 6 0 0 NEXT'],
['Step 7: type ⟦8B, NEXT, EC, NEXT|MOV BP,SP⟧, then ⟦CC, NEXT|HLT⟧.','7) اكتب ⟦8B ثم NEXT ثم EC ثم NEXT|MOV BP,SP⟧ ثم ⟦CC ثم NEXT|HLT⟧.','8 B NEXT E C NEXT C C NEXT'],
['Step 8: press TTY, GO, type 600, then TTY. BP now holds the same value as SP.','8) اضغط TTY ثم GO واكتب 600 ثم TTY. يحمل BP الآن نفس قيمة SP.','TTY GO 6 0 0 TTY r:BP r:SP'],
['Common mistake: reading the two registers in the wrong order. With D=1, REG is the destination, so 8B EC is MOV BP,SP and not MOV SP,BP.','خطأ شائع: قراءة المسجلين بترتيب خاطئ. عندما D=1 يكون REG هو الوجهة، فالكود 8B EC هو MOV BP,SP وليس MOV SP,BP.','t:REG g:reg:101:0 g:reg:101:2 b:8B-EC']]},
{k:'e',t:['Example 2: choosing MOD','مثال 2: اختيار MOD'],s:[
['Goal: choose MOD for three instructions that all use [DI]. In all of them R/M=101 means DI.','الهدف: اختيار MOD لثلاث تعليمات تستخدم كلها [DI]. في الثلاث تعني R/M=101 المسجل DI.','t:RM g:rm:101:0 g:rm:101:1'],
['MOV AL,[DI] has no displacement, so MOD=00.','التعليمة MOV AL,[DI] ليس فيها إزاحة، إذن MOD=00.','t:MOD g:mod:00:*'],
['MOV AL,[DI+02H]: 02H fits in 8 bits, so MOD=01 and one displacement byte follows.','التعليمة MOV AL,[DI+02H]: القيمة 02H تتسع في 8 بت، إذن MOD=01 ويتبعها بايت إزاحة واحد.','t:MOD g:mod:01:*'],
['MOV AL,[DI+1000H]: 1000H needs 16 bits, so MOD=10 and two displacement bytes follow.','التعليمة MOV AL,[DI+1000H]: القيمة 1000H تحتاج 16 بت، إذن MOD=10 ويتبعها بايتا إزاحة.','t:MOD g:mod:10:*'],
['Now the bytes. The opcode is 8A (D=1, W=0), AL is REG=000. With MOD=00 the second byte is 00 000 101 = 05: ⟦8A 05|MOV AL,[DI]⟧.','والآن البايتات. الأوبكود 8A (D=1 وW=0) وAL هو REG=000. مع MOD=00 يكون البايت الثاني 00 000 101 = 05: ⟦8A 05|MOV AL,[DI]⟧.','t:REG b:8A-05 g:reg:000:0 g:reg:000:1 g:reg:H:1'],
['With MOD=01 the byte is 01 000 101 = 45, then the displacement: ⟦8A 45 02|MOV AL,[DI+02H]⟧.','مع MOD=01 يكون البايت 01 000 101 = 45 ثم الإزاحة: ⟦8A 45 02|MOV AL,[DI+02H]⟧.','t:MOD b:8A-45-02 g:mod:01:*'],
['With MOD=10 the byte is 10 000 101 = 85, then 1000H low byte first: ⟦8A 85 00 10|MOV AL,[DI+1000H]⟧.','مع MOD=10 يكون البايت 10 000 101 = 85 ثم 1000H بالبايت الأدنى أولاً: ⟦8A 85 00 10|MOV AL,[DI+1000H]⟧.','t:MOD b:8A-85-00-10 g:mod:10:*'],
['Common mistake: using MOD=01 for [DI+80H]. An 8-bit displacement is sign-extended, so 80H would mean -128. Values from 80H up need MOD=10.','خطأ شائع: استعمال MOD=01 في التعليمة MOV AL,[DI+80H]. الإزاحة ذات 8 بت تُوسَّع بالإشارة، فالقيمة 80H تعني -128. القيم من 80H فما فوق تحتاج MOD=10.','t:MOD g:mod:01:* g:mod:10:* b:8A-85-80-00']]},
{k:'e',t:['Example 3: encode a MOV','مثال 3: كتابة كود MOV'],s:[
['Goal: write the machine code of MOV CX,[BX+DI+20H].','الهدف: كتابة الكود الآلي للتعليمة MOV CX,[BX+DI+20H].','r:CX r:BX r:DI'],
['Step 1: CX is a register and the destination, so D=1. It is 16-bit, so W=1. The opcode is 8B.','1) المسجل CX هو الوجهة إذن D=1، وهو 16 بت إذن W=1. الأوبكود هو 8B.','t:DW g:dw:D:0 g:dw:D:2 g:dw:W:0 g:dw:W:2'],
['Step 2: the address has a one-byte displacement (20H), so MOD=01.','2) العنوان فيه إزاحة من بايت واحد (20H)، إذن MOD=01.','t:MOD g:mod:01:*'],
['Step 3: REG=001 (CX) and R/M=001 (BX+DI). The byte is 01 001 001 = 49.','3) REG=001 (CX) وR/M=001 (BX+DI). فيكون البايت 01 001 001 = 49.','t:REG b:8B-49-20 g:reg:001:0 g:reg:001:2 g:reg:H:2'],
['Step 4: add the displacement byte 20. The code is ⟦8B 49 20|MOV CX,[BX+DI+20H]⟧.','4) نضيف بايت الإزاحة 20. فيكون الكود ⟦8B 49 20|MOV CX,[BX+DI+20H]⟧.','b:8B-49-20'],
['Common mistake: stopping at 8B 49. With MOD=01 one displacement byte must follow, so the code is 8B 49 20.','خطأ شائع: التوقف عند 8B 49. مع MOD=01 يجب أن يليهما بايت إزاحة، فيكون الكود 8B 49 20.','t:MOD g:mod:01:* b:8B-49-20']]},
{k:'x',t:['Exercise 1: decode','تمرين 1: فك الكود'],s:[
['Choose the instruction for 8B D1. Use Hint if needed.','اختر التعليمة التي يمثلها الكود 8B D1. استعمل التلميح عند الحاجة.','t:REG h:DX h:CX','8B means D=1, W=1. D1 = 11 010 001: REG=DX, R/M=CX. Answer: MOV DX,CX.','الأوبكود 8B يعني D=1 وW=1. و D1 = 11 010 001: REG=DX وR/M=CX. الجواب: MOV DX,CX.','',['MOV DX,CX', 'MOV CX,DX', 'MOV DX,BX']],
['Choose the instruction for 8B EC.','اختر التعليمة التي يمثلها الكود 8B EC.','t:REG h:BP h:SP','EC = 11 101 100: REG=BP, R/M=SP. Answer: MOV BP,SP.','EC = 11 101 100: REG=BP وR/M=SP. الجواب: MOV BP,SP.','',['MOV BP,SP', 'MOV SP,BP', 'MOV BP,SI']],
['Choose the instruction for 8B F0.','اختر التعليمة التي يمثلها الكود 8B F0.','t:REG h:SI h:AX','F0 = 11 110 000: REG=SI, R/M=AX. Answer: MOV SI,AX.','F0 = 11 110 000: REG=SI وR/M=AX. الجواب: MOV SI,AX.','',['MOV SI,AX', 'MOV AX,SI', 'MOV DI,AX']],
['Choose the instruction for 8B FE.','اختر التعليمة التي يمثلها الكود 8B FE.','t:REG h:DI h:SI','FE = 11 111 110: REG=DI, R/M=SI. Answer: MOV DI,SI.','FE = 11 111 110: REG=DI وR/M=SI. الجواب: MOV DI,SI.','',['MOV DI,SI', 'MOV SI,DI', 'MOV DI,BP']],
['Choose the instruction for 8A C7.','اختر التعليمة التي يمثلها الكود 8A C7.','t:REG h:AL h:BH','8A means D=1, W=0 (8-bit). C7 = 11 000 111: REG=AL, R/M=BH. Answer: MOV AL,BH.','الأوبكود 8A يعني D=1 وW=0 (8 بت). و C7 = 11 000 111: REG=AL وR/M=BH. الجواب: MOV AL,BH.','',['MOV AL,BH', 'MOV BH,AL', 'MOV AX,BX']],
['Choose the instruction for 8A EA.','اختر التعليمة التي يمثلها الكود 8A EA.','t:REG h:CH h:DL','EA = 11 101 010: REG=CH, R/M=DL. Answer: MOV CH,DL.','EA = 11 101 010: REG=CH وR/M=DL. الجواب: MOV CH,DL.','',['MOV CH,DL', 'MOV DL,CH', 'MOV BP,DX']],
['Choose the instruction for 8A D8.','اختر التعليمة التي يمثلها الكود 8A D8.','t:REG h:BL h:AL','D8 = 11 011 000: REG=BL, R/M=AL. Answer: MOV BL,AL.','D8 = 11 011 000: REG=BL وR/M=AL. الجواب: MOV BL,AL.','',['MOV BL,AL', 'MOV AL,BL', 'MOV BX,AX']],
['Choose the instruction for 88 71 02.','اختر التعليمة التي يمثلها الكود 88 71 02.','t:REG h:DH g:mod:01:* g:rm:001:0 g:rm:001:1','88 means D=0, W=0: REG to R/M, 8-bit. 71 = 01 110 001: MOD=01, REG=DH, R/M=BX+DI, displacement 02. Answer: MOV [BX+DI+02H],DH.','الأوبكود 88 يعني D=0 وW=0: من REG إلى R/M بحجم 8 بت. و 71 = 01 110 001: MOD=01 وREG=DH وR/M=BX+DI والإزاحة 02. الجواب: MOV [BX+DI+02H],DH.','',['MOV [BX+DI+02H],DH', 'MOV DH,[BX+DI+02H]', 'MOV [BX+SI+02H],DH']],
['Choose the instruction for 8B 87 23 01.','اختر التعليمة التي يمثلها الكود 8B 87 23 01.','t:REG h:AX g:mod:10:* g:rm:111:0 g:rm:111:1','8B means D=1, W=1. 87 = 10 000 111: MOD=10, REG=AX, R/M=BX. Displacement 23 01 = 0123H. Answer: MOV AX,[BX+0123H].','الأوبكود 8B يعني D=1 وW=1. و 87 = 10 000 111: MOD=10 وREG=AX وR/M=BX. الإزاحة 23 01 = 0123H. الجواب: MOV AX,[BX+0123H].','',['MOV AX,[BX+0123H]', 'MOV [BX+0123H],AX', 'MOV AX,[BP+0123H]']],
['Choose the instruction for 89 1E 00 06.','اختر التعليمة التي يمثلها الكود 89 1E 00 06.','t:REG h:BX g:mod:00:* g:rm:110:0 g:rm:110:1','89 means D=0, W=1. 1E = 00 011 110: MOD=00, REG=BX, R/M=110 direct address. Address 00 06 = 0600H. Answer: MOV [0600H],BX.','الأوبكود 89 يعني D=0 وW=1. و 1E = 00 011 110: MOD=00 وREG=BX وR/M=110 عنوان مباشر. العنوان 00 06 = 0600H. الجواب: MOV [0600H],BX.','',['MOV [0600H],BX', 'MOV BX,[0600H]', 'MOV [0006H],BX']]]},
{k:'x',t:['Exercise 2: encode','تمرين 2: كتابة الكود'],s:[
['Write the machine code of MOV AX,BX. Store it at 0600: RESET, EB, 600, NEXT, then each byte followed by NEXT.','اكتب الكود الآلي للتعليمة MOV AX,BX وخزّنه عند 0600: RESET ثم EB ثم 600 ثم NEXT ثم كل بايت متبوعاً بـ NEXT.','EB t:REG h:AX h:BX','D=1, W=1 gives 8B. MOD=11, REG=AX (000), R/M=BX (011): 11 000 011 = C3. Code: 8B C3.','D=1 وW=1 تعطي 8B. وMOD=11 وREG=AX (000) وR/M=BX (011): 11 000 011 = C3. الكود: 8B C3.','M0600=8BC3'],
['Next: MOV BL,CH. Store its code at 0600.','التالي: MOV BL,CH. خزّن كودها عند 0600.','EB t:REG h:BL h:CH','D=1, W=0 gives 8A. MOD=11, REG=BL (011), R/M=CH (101): 11 011 101 = DD. Code: 8A DD.','D=1 وW=0 تعطي 8A. وMOD=11 وREG=BL (011) وR/M=CH (101): 11 011 101 = DD. الكود: 8A DD.','M0600=8ADD'],
['Next: MOV AH,[0500H]. Store its code at 0600.','التالي: MOV AH,[0500H]. خزّن كودها عند 0600.','EB t:REG h:AH g:mod:00:* g:rm:110:0 g:rm:110:1','D=1, W=0 gives 8A. MOD=00, REG=AH (100), R/M=110 (direct address): 00 100 110 = 26. Address 0500, low byte first: 00 05. Code: 8A 26 00 05.','D=1 وW=0 تعطي 8A. وMOD=00 وREG=AH (100) وR/M=110 (عنوان مباشر): 00 100 110 = 26. العنوان 0500 بالبايت الأدنى أولاً: 00 05. الكود: 8A 26 00 05.','M0600=8A260005'],
['Next: MOV [0450H],BL. Store its code at 0600.','التالي: MOV [0450H],BL. خزّن كودها عند 0600.','EB t:REG h:BL g:mod:00:* g:rm:110:0 g:rm:110:1','D=0, W=0 gives 88. MOD=00, REG=BL (011), R/M=110 (direct address): 00 011 110 = 1E. Address 0450: 50 04. Code: 88 1E 50 04.','D=0 وW=0 تعطي 88. وMOD=00 وREG=BL (011) وR/M=110 (عنوان مباشر): 00 011 110 = 1E. العنوان 0450: 50 04. الكود: 88 1E 50 04.','M0600=881E5004'],
['Next: MOV [BX+SI],CX. Store its code at 0600.','التالي: MOV [BX+SI],CX. خزّن كودها عند 0600.','EB t:REG h:CX g:mod:00:* g:rm:000:0 g:rm:000:1','D=0, W=1 gives 89. MOD=00, REG=CX (001), R/M=BX+SI (000): 00 001 000 = 08. Code: 89 08.','D=0 وW=1 تعطي 89. وMOD=00 وREG=CX (001) وR/M=BX+SI (000): 00 001 000 = 08. الكود: 89 08.','M0600=8908'],
['Next: MOV DL,[BP+SI+1234H]. Store its code at 0600.','التالي: MOV DL,[BP+SI+1234H]. خزّن كودها عند 0600.','EB t:REG h:DL g:mod:10:* g:rm:010:0 g:rm:010:1','D=1, W=0 gives 8A. MOD=10 (16-bit displacement), REG=DL (010), R/M=BP+SI (010): 10 010 010 = 92. Displacement 1234: 34 12. Code: 8A 92 34 12.','D=1 وW=0 تعطي 8A. وMOD=10 (إزاحة 16 بت) وREG=DL (010) وR/M=BP+SI (010): 10 010 010 = 92. الإزاحة 1234: 34 12. الكود: 8A 92 34 12.','M0600=8A923412'],
['Next: MOV [DI+56H],AL. Store its code at 0600.','التالي: MOV [DI+56H],AL. خزّن كودها عند 0600.','EB t:REG h:AL g:mod:01:* g:rm:101:0 g:rm:101:1','D=0, W=0 gives 88. MOD=01 (56H fits in 8 bits), REG=AL (000), R/M=DI (101): 01 000 101 = 45. Code: 88 45 56.','D=0 وW=0 تعطي 88. وMOD=01 (القيمة 56H تتسع في 8 بت) وREG=AL (000) وR/M=DI (101): 01 000 101 = 45. الكود: 88 45 56.','M0600=884556'],
['Next: MOV SI,FC67H. Store its code at 0600.','التالي: MOV SI,FC67H. خزّن كودها عند 0600.','EB t:REG h:SI','This is an immediate MOV into a register: B8 + register code. SI is 110, so B8+6 = BE. The value FC67 goes low byte first. Code: BE 67 FC.','هذه MOV بقيمة فورية إلى مسجل: B8 + رمز المسجل. رمز SI هو 110 فيكون B8+6 = BE. والقيمة FC67 بالبايت الأدنى أولاً. الكود: BE 67 FC.','M0600=BE67FC'],
['Next: MOV SP,[0800H]. Store its code at 0600.','التالي: MOV SP,[0800H]. خزّن كودها عند 0600.','EB t:REG h:SP g:mod:00:* g:rm:110:0 g:rm:110:1','D=1, W=1 gives 8B. MOD=00, REG=SP (100), R/M=110 (direct address): 00 100 110 = 26. Address 0800: 00 08. Code: 8B 26 00 08.','D=1 وW=1 تعطي 8B. وMOD=00 وREG=SP (100) وR/M=110 (عنوان مباشر): 00 100 110 = 26. العنوان 0800: 00 08. الكود: 8B 26 00 08.','M0600=8B260008'],
['Last one: MOV [BX],CL. Store its code at 0600.','الأخيرة: MOV [BX],CL. خزّن كودها عند 0600.','EB t:REG h:CL g:mod:00:* g:rm:111:0 g:rm:111:1','D=0, W=0 gives 88. MOD=00, REG=CL (001), R/M=BX (111): 00 001 111 = 0F. Code: 88 0F.','D=0 وW=0 تعطي 88. وMOD=00 وREG=CL (001) وR/M=BX (111): 00 001 111 = 0F. الكود: 88 0F.','M0600=880F']]},
{k:'x',t:['Exercise 3: memory to BL','تمرين 3: من الذاكرة إلى BL'],s:[
['Task: move the byte at 0700 into BL, copy BL into AL, then stop. First store the test value 6E at 0700.','المهمة: انقل البايت الموجود عند 0700 إلى BL ثم انسخ BL إلى AL ثم توقف. خزّن أولاً القيمة التجريبية 6E عند 0700.','EB t:REG h:BL h:AL','RESET, EB, 700, NEXT, 6E (keys 6 then E), NEXT.','RESET ثم EB ثم 700 ثم NEXT ثم 6E (المفتاح 6 ثم E) ثم NEXT.','M0700=6E'],
['Now write the program at 0800:\nMOV BL,[0700]\nMOV AL,BL\nHLT\nEnter its machine code.','اكتب الآن البرنامج عند 0800:\nMOV BL,[0700]\nMOV AL,BL\nHLT\nأدخل الكود الآلي له.','EB t:REG h:BL g:mod:00:* g:rm:110:0 g:rm:110:1','MOV BL,[0700] = 8A 1E 00 07. MOV AL,BL = 8A C3. HLT = CC. So type 8A 1E 00 07 8A C3 CC.','MOV BL,[0700] = 8A 1E 00 07. وMOV AL,BL = 8A C3. وHLT = CC. إذن اكتب 8A 1E 00 07 8A C3 CC.','M0800=8A1E00078AC3CC'],
['Run it: TTY, GO, 800, then TTY. Both AL and BL should become 6E.','شغّله: TTY ثم GO ثم 800 ثم TTY. يجب أن يصبح AL وBL كلاهما 6E.','r:AX r:BX t:REG','TTY, GO, 8, 0, 0, TTY.','TTY ثم GO ثم 8 ثم 0 ثم 0 ثم TTY.','AL=6E&BL=6E'],
['To see the result on the 7-segment display: press REG, then 0 (AX). The two right digits are AL = 6E.','لرؤية النتيجة على الشاشة السباعية: اضغط REG ثم 0 (AX). الخانتان اليمنيان هما AL = 6E.','REG 0 dl t:REG h:AL h:BL']]},
{k:'x',t:['Exercise 4: what does it do?','تمرين 4: ماذا يفعل البرنامج؟'],s:[
['What does this program do?\nMOV CH,[0600H]\nMOV BL,[0700H]\nMOV AL,CH\nMOV AH,BL\nMOV [0800],AX\nHLT','ماذا يفعل هذا البرنامج؟\nMOV CH,[0600H]\nMOV BL,[0700H]\nMOV AL,CH\nMOV AH,BL\nMOV [0800],AX\nHLT','t:REG','It reads the bytes at 0600 and 0700, packs them into AX (AL = [0600], AH = [0700]) and stores AX at 0800-0801.','يقرأ البايتين عند 0600 و0700 ويجمعهما في AX (AL = [0600] وAH = [0700]) ثم يخزّن AX عند 0800-0801.'],
['Store test bytes: 25 at 0600 and 9C at 0700 (EB, address, NEXT, value, NEXT; press RESET between them).','خزّن بايتات تجريبية: 25 عند 0600 و9C عند 0700 (EB ثم العنوان ثم NEXT ثم القيمة ثم NEXT، مع RESET بينهما).','EB t:REG','RESET, EB, 600, NEXT, 25, NEXT. Then RESET, EB, 700, NEXT, 9C, NEXT.','RESET ثم EB ثم 600 ثم NEXT ثم 25 ثم NEXT. بعدها RESET ثم EB ثم 700 ثم NEXT ثم 9C ثم NEXT.','M0600=25&M0700=9C'],
['Enter the program at 0500 as machine code (RESET, EB, 500, NEXT, then every byte with NEXT). It writes its result at 0800, over the Exercise 3 program.','أدخل البرنامج عند 0500 ككود آلي (RESET ثم EB ثم 500 ثم NEXT ثم كل بايت مع NEXT). ويكتب نتيجته عند 0800 فوق برنامج التمرين 3.','EB t:REG','8A 2E 00 06 = MOV CH,[0600]. 8A 1E 00 07 = MOV BL,[0700]. 8A C5 = MOV AL,CH. 8A E3 = MOV AH,BL. 89 06 00 08 = MOV [0800],AX. CC = HLT.','8A 2E 00 06 = MOV CH,[0600]. و8A 1E 00 07 = MOV BL,[0700]. و8A C5 = MOV AL,CH. و8A E3 = MOV AH,BL. و89 06 00 08 = MOV [0800],AX. وCC = HLT.','M0500=8A2E00068A1E00078AC58AE389060008CC'],
['Run it: TTY, GO, 500, TTY. AX becomes 9C25 and 0800-0801 hold 25 9C.','شغّله: TTY ثم GO ثم 500 ثم TTY. يصبح AX = 9C25 وتحمل الخانتان 0800-0801 القيمتين 25 9C.','r:AX t:REG h:AX','TTY, GO, 5, 0, 0, TTY.','TTY ثم GO ثم 5 ثم 0 ثم 0 ثم TTY.','AX=9C25&M0800=259C']]},
{k:'q',t:['Final test','الاختبار النهائي'],q:[
['With W=0, the REG code 100 means AH.','عندما W=0 يعني الرمز 100 في REG المسجل AH.',true],
['MOV CX,DX is written in machine code as 8B CA.','التعليمة MOV CX,DX كودها الآلي 8B CA.',true],
['The code 89 D8 is MOV AX,BX.','الكود 89 D8 هو MOV AX,BX.',true],
['MOV SI,FC67H is written as BE FC 67.','التعليمة MOV SI,FC67H كودها BE FC 67.',false,'The value is stored low byte first: BE 67 FC.','القيمة تُخزَّن بالبايت الأدنى أولاً: BE 67 FC.'],
['MOV AL,[DI+80H] can use MOD=01.','التعليمة MOV AL,[DI+80H] يمكن أن تستعمل MOD=01.',false,'80H does not fit in a signed 8-bit displacement (it would mean -128), so MOD=10 is needed.','القيمة 80H لا تناسب إزاحة 8 بت بإشارة (ستعني -128)، لذلك نحتاج MOD=10.'],
['The code 8B 0E 00 05 is MOV CX,[0005H].','الكود 8B 0E 00 05 هو MOV CX,[0005H].',false,'The address is stored low byte first: 00 05 means 0500H.','العنوان يُخزَّن بالبايت الأدنى أولاً: 00 05 تعني 0500H.'],
['MOD=00 with R/M=110 means [BP].','القيمة MOD=00 مع R/M=110 تعني [BP].',false,'It means a direct address: a 16-bit address follows.','هي تعني عنواناً مباشراً: يليها عنوان من 16 بت.'],
['The byte 01 011 110 is 5E in hex.','البايت 01 011 110 هو 5E بنظام Hex.',true]]}
]};
/* Level 3 Arabic: every Latin/number run is wrapped in directional isolates so mixed Arabic/English text reads in the right order */
(function(){const R=/[A-Za-z0-9](?:[A-Za-z0-9\-\/+=,\[\] ]*[A-Za-z0-9\]])?/g,w=x=>typeof x=='string'?x.replace(R,'\u2066$&\u2069'):x;
LV[3].forEach(m=>{m.t[1]=w(m.t[1]);(m.s||[]).forEach(t=>{t[1]=w(t[1]);if(m.k=='x'&&t[4])t[4]=w(t[4])});(m.q||[]).forEach(q=>{q[1]=w(q[1]);if(q[4])q[4]=w(q[4])})})})();
/* Final tests of levels 1 and 2: 6 questions each, mostly practical / programming (machine code, memory order, running a program) */
(function(){const R=/[A-Za-z0-9](?:[A-Za-z0-9\-\/+=,\[\] ]*[A-Za-z0-9\]])?/g,w=x=>typeof x=='string'?x.replace(R,'\u2066$&\u2069'):x,
add=(n,A,keep)=>{const q=LV[n].find(m=>m.k=='q').q;A.forEach(r=>{r[1]=w(r[1]);if(r[4])r[4]=w(r[4]);q.push(r)});const k=keep.map(i=>q[i]);q.splice(0,q.length,...k)};
add(1,[
["To store a program at 400: press EB, type 400, NEXT, then type each byte followed by NEXT.","لتخزين برنامج عند 400: اضغط EB واكتب 400 ثم NEXT، ثم اكتب كل بايت متبوعاً بـ NEXT.",true],
["The program B4 6C CC ends with AL = 6C.","البرنامج B4 6C CC ينتهي وقيمة AL تساوي 6C.",false,"B4 is MOV AH, so 6C goes into AH, not AL.","الأمر B4 هو MOV AH، فتذهب القيمة 6C إلى AH وليس AL."],
["To run the program stored at 400: press GO, type 400, then TTY.","لتشغيل البرنامج المخزّن عند 400: اضغط GO واكتب 400 ثم TTY.",true],
["If AX = DFA1, then AL = DF and AH = A1.","إذا كان AX = DFA1 فإن AL = DF وAH = A1.",false,"AH is the high byte: AH = DF and AL = A1.","AH هو البايت العلوي: AH = DF وAL = A1."]
],[1,2,3,4,5,6]);
add(2,[
["MOV DL,8C is written in machine code as B2 8C.","التعليمة MOV DL,8C كودها الآلي B2 8C.",true],
["The code BB 3E 94 loads BX with 943E.","الكود BB 3E 94 يحمّل BX بالقيمة 943E.",true],
["After DL = 8C and DH = AF, the register DX = 8CAF.","بعد أن يصبح DL = 8C وDH = AF يكون المسجل DX = 8CAF.",false,"DH is the high byte, so DX = AF8C.","DH هو البايت العلوي، فيكون DX = AF8C."],
["To reach BX press ER, then key 1.","للوصول إلى BX اضغط ER ثم المفتاح 1.",true],
["In the code 89 1E 50 06 the address is 5006.","في الكود 89 1E 50 06 يكون العنوان هو 5006.",false,"The address is stored low byte first: 50 06 means 0650.","العنوان يُخزَّن بالبايت الأدنى أولاً: 50 06 تعني 0650."]
],[3,1,4,5,6,7]);
})();
/* Final tests v3: 9 questions per level = 3 true/false + 3 multiple choice (3 options) + 3 typed on the kit, in scattered order.
   true/false: [en, ar, bool, expEn, expAr]   multiple choice: [en, ar, null, expEn, expAr, [correct, wrong, wrong]]   typed: [en, ar, null, hintEn, hintAr, check] */
(function(){const R=/[A-Za-z0-9](?:[A-Za-z0-9\-\/+=,\[\] ]*[A-Za-z0-9\]])?/g,w=x=>typeof x=='string'?x.replace(R,'\u2066$&\u2069'):x;
const T=(e,a,v,xe,xa)=>[e,a,v,xe,xa],M=(e,a,o,xe,xa)=>[e,a,null,xe,xa,o],X=(e,a,he,ha,ck)=>[e,a,null,he,ha,ck];
const S={
1:[
T("B8 BB AA loads AABB into BX.","الأمر B8 BB AA يضع AABB في BX.",false,"B8 is MOV AX, so AABB goes into AX, not BX.","الأمر B8 هو MOV AX، فتُخزَّن AABB في AX وليس BX."),
M("Which register is the low half of AX?","أي مسجل هو النصف الأدنى من AX؟",["AL","AH","BX"],"AL is the low byte of AX, and AH is the high byte.","AL هو البايت الأدنى من AX، وAH هو البايت الأعلى."),
X("Store the byte 5A at address 400.","خزّن البايت 5A عند العنوان 400.","RESET, EB, 400, NEXT, 5A, NEXT.","RESET ثم EB ثم 400 ثم NEXT ثم 5A ثم NEXT.","M0400=5A"),
M("Which key lets you read and write a memory byte?","أي مفتاح يتيح قراءة بايت من الذاكرة وكتابته؟",["EB","ER","GO"],"EB examines a memory byte. ER examines a register and GO runs a program.","المفتاح EB يفحص بايتاً من الذاكرة. أما ER فيفحص مسجلاً وGO يشغّل برنامجاً."),
T("To store a program at 400: press EB, type 400, NEXT, then type each byte followed by NEXT.","لتخزين برنامج عند 400: اضغط EB واكتب 400 ثم NEXT، ثم اكتب كل بايت متبوعاً بـ NEXT.",true),
X("Show register BX on the display.","اعرض المسجل BX على الشاشة.","Press ER, then key 1 (BX).","اضغط ER ثم المفتاح 1 (BX).","V=1"),
M("What does the byte CC do at the end of the programs?","ماذا يفعل البايت CC في نهاية البرامج؟",["HLT","MOV AH","GO"],"CC is HLT: it stops the program.","البايت CC هو HLT: يوقف البرنامج."),
T("If AX = DFA1, then AL = DF and AH = A1.","إذا كان AX = DFA1 فإن AL = DF وAH = A1.",false,"AH is the high byte: AH = DF and AL = A1.","AH هو البايت العلوي: AH = DF وAL = A1."),
X("Put E3 in AL and 1D in AH, then run it, so that AX = 1DE3.","ضع E3 في AL و1D في AH ثم شغّله، فيصبح AX = 1DE3.","B0 E3, B4 1D, then CC. Then TTY, GO, the address, TTY.","B0 E3 ثم B4 1D ثم CC. بعدها TTY ثم GO ثم العنوان ثم TTY.","AX=1DE3")],
2:[
M("AB is at 500 and 7D is at 501. Which 16-bit value is read from 500?","AB عند 500 و7D عند 501. ما القيمة 16 بت المقروءة من 500؟",["7DAB","AB7D","7DBA"],"Low byte first: AB is the low half, so the value is 7DAB.","البايت الأدنى أولاً: AB هو النصف الأدنى، فتكون القيمة 7DAB."),
T("MOV AX,CX copies AX into CX.","الأمر MOV AX,CX ينسخ AX إلى CX.",false,"The destination is written first: MOV AX,CX copies CX into AX.","الوجهة تُكتب أولاً: الأمر MOV AX,CX ينسخ CX إلى AX."),
X("Store the byte 6B at address 0700.","خزّن البايت 6B عند العنوان 0700.","RESET, EB, 700, NEXT, 6B, NEXT.","RESET ثم EB ثم 700 ثم NEXT ثم 6B ثم NEXT.","M0700=6B"),
T("To store the value 60AB at address 500: write AB at 500 and 60 at 501 (the low byte is written first).","لتخزين القيمة 60AB في العنوان 500: نكتب AB في 500 و60 في 501 (البايت الأدنى يُكتب أولاً).",true),
M("Which code is MOV AX,CX?","أي كود هو MOV AX,CX؟",["8B C1","8B C8","8B C2"],"8B C1 copies CX into AX. 8B C8 is MOV CX,AX and 8B C2 is MOV AX,DX.","الكود 8B C1 ينسخ CX إلى AX. أما 8B C8 فهو MOV CX,AX و8B C2 هو MOV AX,DX."),
M("To check BX with ER, which key do you press after ER?","لفحص BX بـ ER، أي مفتاح تضغط بعد ER؟",["1","0","3"],"BX is key 1 (AX 0, BX 1, CX 2, DX 3).","BX هو المفتاح 1 (AX هو 0 وBX هو 1 وCX هو 2 وDX هو 3)."),
X("Show register DX on the display.","اعرض المسجل DX على الشاشة.","Press ER, then key 3 (DX).","اضغط ER ثم المفتاح 3 (DX).","V=3"),
T("In the code 89 1E 50 06 the address is 5006.","في الكود 89 1E 50 06 يكون العنوان هو 5006.",false,"The address is stored low byte first: 50 06 means 0650.","العنوان يُخزَّن بالبايت الأدنى أولاً: 50 06 تعني 0650."),
X("Make BX = 7A2D, store BX at 0680, then run it.","اجعل BX = 7A2D وخزّنه عند 0680 ثم شغّل البرنامج.","BB 2D 7A, 89 1E 80 06, then CC. Then TTY, GO, the address, TTY.","BB 2D 7A ثم 89 1E 80 06 ثم CC. بعدها TTY ثم GO ثم العنوان ثم TTY.","BX=7A2D&M0680=2D7A")],
3:[
X("Write MOV BX,CX as machine code at address 0A00.","اكتب التعليمة MOV BX,CX ككود آلي عند العنوان 0A00.","8B D9: after 8B comes MOD=11, REG=011 (BX), R/M=001 (CX), which is D9.","8B D9: بعد 8B يأتي MOD=11 وREG=011 (BX) وR/M=001 (CX) أي D9.","M0A00=8BD9"),
T("The code 89 D8 is MOV AX,BX.","الكود 89 D8 هو MOV AX,BX.",true),
M("With W=0, which register does the REG code 100 mean?","عندما W=0، أي مسجل يعني الرمز 100 في REG؟",["AH","AX","SP"],"With W=0 the 8-bit registers are used: 100 is AH. With W=1 it would be SP.","مع W=0 تُستعمل مسجلات 8 بت: الرمز 100 هو AH. أما مع W=1 فيكون SP."),
T("MOV SI,FC67H is written as BE FC 67.","التعليمة MOV SI,FC67H كودها BE FC 67.",false,"The value is stored low byte first: BE 67 FC.","القيمة تُخزَّن بالبايت الأدنى أولاً: BE 67 FC."),
X("Write MOV AX,DX as machine code at address 0B00.","اكتب التعليمة MOV AX,DX ككود آلي عند العنوان 0B00.","8B C2: MOD=11, REG=000 (AX), R/M=010 (DX), which is C2.","8B C2: MOD=11 وREG=000 (AX) وR/M=010 (DX) أي C2.","M0B00=8BC2"),
M("The byte 01 011 110 is which hex value?","البايت 01 011 110 هو أي قيمة Hex؟",["5E","6E","5B"],"0101 is 5 and 1110 is E, so the byte is 5E.","0101 هو 5 و1110 هو E، فالبايت هو 5E."),
T("The code 8B 0E 00 05 is MOV CX,[0005H].","الكود 8B 0E 00 05 هو MOV CX,[0005H].",false,"The address is stored low byte first: 00 05 means 0500H.","العنوان يُخزَّن بالبايت الأدنى أولاً: 00 05 تعني 0500H."),
M("Which code is MOV CX,DX?","أي كود هو MOV CX,DX؟",["8B CA","8B D1","8B C2"],"8B CA: MOD=11, REG=001 (CX), R/M=010 (DX). 8B D1 is the reverse, MOV DX,CX.","8B CA: MOD=11 وREG=001 (CX) وR/M=010 (DX). أما 8B D1 فهو العكس MOV DX,CX."),
X("Store 6D at 0900. Then at 0A00 write and run: MOV DL,[0900H], MOV AL,DL, HLT. AL must become 6D.","خزّن 6D عند 0900. ثم اكتب عند 0A00 وشغّل: MOV DL,[0900H] ثم MOV AL,DL ثم HLT. يجب أن يصبح AL = 6D.","EB 900: 6D. Then EB A00: 8A 16 00 09, 8A C2, CC. Then TTY, GO, A00, TTY.","EB ثم 900: القيمة 6D. ثم EB ثم A00: 8A 16 00 09 ثم 8A C2 ثم CC. بعدها TTY ثم GO ثم A00 ثم TTY.","AL=6D&M0900=6D")]};
Object.keys(S).forEach(n=>{const q=LV[n].find(m=>m.k=='q').q;q.splice(0,q.length,...S[n].map(r=>{r[1]=w(r[1]);if(r[4])r[4]=w(r[4]);return r}))})})();
/* Final tests: assembly instructions (MOV AX,CX / MOV DL,8C / MOV AH ...) are shown as code chips, like in the examples and exercises */
(function(){const I=/MOV(?: [A-Z]{2}| \[[0-9A-F]{2,4}\])(?:,(?:[A-Z]{2}|\[[0-9A-F]{2,4}\]|[0-9A-F]{2,4}))?/g,c=x=>typeof x=='string'?x.replace(I,'\u0002$&\u0003'):x;
Object.keys(LV).forEach(n=>LV[n].forEach(m=>(m.q||[]).forEach(q=>{[0,1,3,4].forEach(i=>{q[i]=c(q[i])})})))})();
function tkQi(ok){return '<svg class="ic qk" viewBox="0 0 24 24" aria-hidden="true">'+(ok?'<path d="M5.5 12.8l4.3 4.3L18.5 7.6"/>':'<path d="M7 7l10 10M17 7L7 17"/>')+'</svg>'}
function tkQz(p,a){const sk=g('tks');if(sk){sk.textContent=a?'تخطي':'Skip';sk.title=sk.textContent;sk.setAttribute('aria-label',sk.title)}const q=p.it.k=='q',n=g('tkn'),f=g('tkp');f.innerHTML=tkQi(0);f.title=a?'خطأ':'False';f.setAttribute('aria-label',f.title);if(q){n.innerHTML=tkQi(1);n.title=a?'صح':'True'}else{n.textContent=a?'\u2039':'\u203A';n.title=a?'التالي':'Next'}n.setAttribute('aria-label',n.title)}
function tkCk(){return '<svg class="ic ck" viewBox="0 0 64 64" aria-hidden="true"><circle cx="32" cy="32" r="29"/><path d="M19 33l9 9 17-19"/></svg>'}
function tmI(a){const L=LV[TV],kn={c:a?'مفهوم':'Concept',e:a?'مثال':'Example',x:a?'تمرين':'Exercise',q:a?'اختبار':'Test'};
 return '<button type=button class=lb>'+(a?'\u203A ':'\u2039 ')+(a?'المستوى ':'Level ')+TV+'</button>'+(L?L.map((m,i)=>'<button type=button class="lv li kd-'+m.k+(DN[TV+'.'+i]?' dn':'')+'" data-i='+i+'><span class=n>'+(i+1)+'</span><span class=tx><b>'+m.t[+a]+'</b><i>'+kn[m.k]+'</i></span><span class=st>'+(DN[TV+'.'+i]?tkCk():'\u25B6')+'</span></button>').join(''):'<p class=tmz>'+(a?'المحتوى قريباً':'Coming soon')+'</p>')}
function tmAp(){document.querySelectorAll('.tkhl').forEach(e=>e.classList.remove('tkhl'));void document.body.offsetWidth;const m={EB:0,ER:1,GO:2,ST:3,EW:7,TTY:'.'};HLT.forEach(t=>{const e=t=='dh'?[...g('dsp').children].slice(4,6):t=='dl'?[...g('dsp').children].slice(6,8):t=='DSP'?[g('dsp')]:t=='FKEYS'?[...document.querySelectorAll('#keys .b')]:t.startsWith('r:')?[[...g('regs').children].find(x=>x.textContent.trim().split(' ')[0]==t.slice(2))]:[document.querySelector('#keys [data-k="'+(t in m?m[t]:/^[0-9A-F]$/.test(t)?parseInt(t,16):t)+'"]')];e.forEach(x=>x&&x.classList.add('tkhl'))});window.tbHL&&tbHL(HLT,PL&&PL.lv)}
function tmHL(a){HLT=a;tmAp()}
new MutationObserver(tmAp).observe(g('regs'),{childList:true});
function tmEnd(){PL=0;delete g('tmw').dataset.lv;window.boHide&&boHide();tmW=0;HLT=[];tmAp();tmWg();g('tmw').classList.remove('ls','hx','cv','fin','xd','qz','qn','qm','big','bs','xo');g('tkn').classList.remove('tkg')}
const SQ={'1.4.1':'RESET ER 0','1.4.4':'1 2 3 4 NEXT','1.4.5':'TTY','1.5.1':'RESET','1.5.2':'EB 4 0 0','1.5.3':'NEXT','1.5.4':'B 8 NEXT','1.5.5':'B B NEXT A A NEXT','1.5.6':'C C NEXT','1.5.7':'TTY GO 4 0 0','1.5.8':'TTY','1.6.1':'EB 6 0 0 NEXT','1.6.2':'B 0 NEXT 4 5 NEXT C C NEXT','1.6.3':'TTY GO 6 0 0','1.6.4':'TTY','1.7.1':'EB 5 0 0 NEXT B 4 NEXT','1.7.2':'6 C NEXT C C NEXT','1.7.3':'TTY GO 5 0 0 TTY','2.3.1':'EB 5 0 0 NEXT','2.3.2':'A B NEXT 7 D NEXT','2.3.3':'RESET EB 7 0 0','2.3.4':'NEXT 8 B NEXT 0 E NEXT 0 0 NEXT 0 5 NEXT 8 B NEXT C 1 NEXT C C NEXT','2.3.5':'TTY GO 7 0 0 TTY','2.4.1':'EB 6 0 0 NEXT A F NEXT','2.4.2':'RESET EB 8 0 0 NEXT B 2 NEXT 8 C NEXT','2.4.3':'8 A NEXT 3 6 NEXT 0 0 NEXT 0 6 NEXT','2.4.4':'8 B NEXT C 2 NEXT C C NEXT','2.4.5':'TTY GO 8 0 0 TTY','2.5.1':'EB 4 0 0 NEXT B B NEXT 3 E NEXT 9 4 NEXT','2.5.2':'8 9 NEXT 1 E NEXT 5 0 NEXT 0 6 NEXT C C NEXT','2.5.3':'TTY GO 4 0 0 TTY','2.5.4':'EB 6 5 0 NEXT','3.6.6':'RESET EB 6 0 0 NEXT','3.6.7':'8 B NEXT E C NEXT C C NEXT','3.6.8':'TTY GO 6 0 0 TTY'};
/* Levels 1-2: extra step after storing a value in a register: check it with ER + the register key (0 AX, 1 BX, 2 CX, 3 DX), then TTY to leave */
(function(){const R=/[A-Za-z0-9](?:[A-Za-z0-9\-\/+=,\[\] ]*[A-Za-z0-9\]])?/g,w=x=>x.replace(R,'\u2066$&\u2069'),
X=h=>['Check AX: press ER, then 0 (AX). The display shows '+h+'. Then press TTY to leave.',w('تحقق من AX: اضغط ER ثم 0 (AX) فتظهر القيمة '+h+'. ثم اضغط TTY للخروج.'),'r:AX','Press ER, then key 0 (AX), then TTY.',w('اضغط ER ثم المفتاح 0 (AX) ثم TTY.'),'AX='+h+'&V=0'];
const e1=LV[1][5].s,e2=LV[1][6].s,e3=LV[1][7].s;
e1.push(['Step 9: check AX: press ER, then 0 (AX). The data display shows AABB. Then press TTY to leave.',w('9) تحقق من AX: اضغط ER ثم 0 (AX) فتظهر القيمة AABB. ثم اضغط TTY للخروج.'),'r:AX']);SQ['1.5.9']='ER 0 TTY';
e2.push(['Step 5: check AX: press ER, then 0 (AX). The two right digits are AL = 45. Then press TTY.',w('5) تحقق من AX: اضغط ER ثم 0 (AX) فتكون الخانتان على اليمين AL = 45. ثم اضغط TTY للخروج.'),'r:AX']);SQ['1.6.5']='ER 0 TTY';
e3.push(['Step 4: check AX: press ER, then 0 (AX). The two left digits are AH = 6C. Then press TTY.',w('4) تحقق من AX: اضغط ER ثم 0 (AX) فتكون الخانتان على اليسار AH = 6C. ثم اضغط TTY للخروج.'),'r:AX']);SQ['1.7.4']='ER 0 TTY';
LV[1][8].s.splice(1,0,X('DFA1'));LV[1][8].s.push(X('869B'));LV[1][9].s.push(X('8F7B'));
LV[2][3].s.splice(6,0,['Step 6: check CX: press ER, then 2 (CX). Then press TTY, ER, and 0 (AX). Both show 7DAB.',w('6) تحقق من CX: اضغط ER ثم 2 (CX). ثم اضغط TTY ثم ER ثم 0 (AX). كلاهما يعرض 7DAB.'),'r:CX r:AX']);SQ['2.3.6']='ER 2 TTY ER 0 TTY';
LV[2][4].s.push(['Step 6: check DX: press ER, then 3 (DX). Then press TTY, ER, and 0 (AX). Both show AF8C.',w('6) تحقق من DX: اضغط ER ثم 3 (DX). ثم اضغط TTY ثم ER ثم 0 (AX). كلاهما يعرض AF8C.'),'r:DX r:AX']);SQ['2.4.6']='ER 3 TTY ER 0 TTY';
const e5=LV[2][5].s;e5.splice(4,0,['Step 4: check BX: press ER, then 1 (BX). The display shows 943E. Then press TTY to leave.',w('4) تحقق من BX: اضغط ER ثم 1 (BX) فتظهر القيمة 943E. ثم اضغط TTY للخروج.'),'r:BX']);
e5[5][0]=e5[5][0].replace('Step 4:','Step 5:');e5[5][1]=e5[5][1].replace('4)','5)');SQ['2.5.5']=SQ['2.5.4'];SQ['2.5.4']='ER 1 TTY';
LV[2][6].s.push(X('3C5A'))})();
/* Lab-sheet material added to Levels 1-2 (Experiment 1 and 2 manuals) */
(function(){const R=/[A-Za-z0-9](?:[A-Za-z0-9\-\/+=,:\[\] ]*[A-Za-z0-9\]])?/g,w=x=>x.replace(R,'\u2066$&\u2069'),S=(e,a,t)=>[e,w(a),t||''];
LV[1][0].s.unshift(S('Objective: get to know the 8086-01 trainer kit, its parts, its memory and basic assembly programming on it.','الهدف: التعرّف على كيت التدريب 8086-01 ومكوناته وذاكرته وأساسيات البرمجة بلغة التجميع عليه.'));
LV[1][1].s.push(S('VCT/INTR gives a non-maskable interrupt (NMI) for testing and debugging. INS/+ inserts bytes into memory without overwriting. DEL deletes bytes and shifts the rest up.','VCT/INTR يولّد مقاطعة غير قابلة للحجب (NMI) لاختبار البرامج وتصحيحها. وINS/+ يدرج بايتات في الذاكرة دون الكتابة فوق البيانات. وDEL يحذف بايتات ويزيح الباقي للأعلى.','FKEYS'),
S('REG examines or modifies the CPU registers. TTY switches to the TTY interface for serial communication with a PC terminal. FILL fills a memory block with data, and PRV goes back to the previous address.','REG لفحص مسجلات المعالج أو تعديلها. وTTY يحوّل الكيت إلى واجهة TTY للاتصال التسلسلي مع حاسوب. وFILL يملأ كتلة من الذاكرة ببيانات، وPRV يرجع إلى العنوان السابق.','FKEYS')
);
LV[1][2].s.push(S('The important monitor commands are EB, EW, ER, IB/IW, OB/OW, MV, GO and ST: examine byte, examine word, examine register, input byte/word, output byte/word, move, go and step.','أوامر المراقب المهمة هي EB وEW وER وIB/IW وOB/OW وMV وGO وST، ومعناها: فحص بايت، فحص كلمة، فحص مسجّل، إدخال بايت أو كلمة، إخراج بايت أو كلمة، نقل، تشغيل، خطوة.','EB EW ER GO ST 4 5 6 8 9'),
S('The command keys are the number keys: 0 EB, 1 ER, 2 GO, 3 ST, 4 IB, 5 OB, 6 MV, 7 EW, 8 IW, 9 OW.','مفاتيح الأوامر هي مفاتيح الأرقام: 0 هو EB و1 هو ER و2 هو GO و3 هو ST و4 هو IB و5 هو OB و6 هو MV و7 هو EW و8 هو IW و9 هو OW.','0 1 2 3 4 5 6 7 8 9')
);
LV[1][3].s.push(S('The kit RAM is 32K made of 62256 chips: EVEN-RAM covers 00000 to 0FFFE and ODD-RAM covers 00001 to 0FFFF.','ذاكرة RAM في الكيت 32K من شرائح 62256: الذاكرة الزوجية EVEN-RAM من 00000 إلى 0FFFE، والفردية ODD-RAM من 00001 إلى 0FFFF.'),
S('Memory map (Fig. 4): the vector interrupt area starts at 00000 and the user RAM area at 00400. System RAM is 00F00 to 00FFF (FE00:2F00 to 2FFF), and user RAM continues at FE00:3000 to 5FFF.','خريطة الذاكرة (الشكل 4): منطقة متجهات المقاطعة تبدأ من 00000 ومنطقة ذاكرة المستخدم من 00400. وذاكرة النظام من 00F00 إلى 00FFF (أي FE00:2F00 إلى 2FFF)، وتستمر ذاكرة المستخدم من FE00:3000 إلى 5FFF.')
);
LV[2][1].s.push(S('In the manual, the display letters of the registers are: AX is A, BX is B, CX is C, DX is D, then SP, bp, SI, dl, CS, dS, SS, ES, IP and FL.','حسب الدليل، حروف عرض المسجلات هي: AX يظهر A وBX يظهر B وCX يظهر C وDX يظهر D، ثم SP وbp وSI وdl وCS وdS وSS وES وIP وFL.','DSP'));
LV[2][0].s.unshift(S('Objective: investigate the general-purpose registers of the 8086.','الهدف: دراسة المسجلات العامة في المعالج 8086.','r:AX r:BX r:CX r:DX'),
S('The 8086 works with 8-bit and 16-bit data, so it has 16-bit registers: general-purpose and special-purpose ones.','يتعامل المعالج 8086 مع بيانات 8 بت و16 بت، لذلك زُوّد بمسجلات 16 بت، منها مسجلات للأغراض العامة ومسجلات للأغراض الخاصة.'));
})();
/* Full lab-sheet questions: every example opens with its complete question (not only the goal), every exercise starts with its complete question */
(function(){const R=/[A-Za-z0-9\[](?:[A-Za-z0-9\-\/+=,:\[\] ]*[A-Za-z0-9\]])?/g,w=x=>x.replace(R,'\u2066$&\u2069'),
Q=(a,b)=>[a.replace(/^\n/,''),w(b.replace(/^\n/,''))],
E=(l,i,a,b)=>{const s=LV[l][i].s[0],q=Q(a,b);s[0]=q[0];s[1]=q[1]},
X=(l,i,a,b)=>{const q=Q(a,b);LV[l][i].s.unshift([q[0],q[1],''])};
/* Level 1 (Experiment 1) */
E(1,5,"Use the 86-01 kit to enter the number (AABBH) in the Accumulator (Register AX) and display the result in seven segment display. Please start your program from address 00400H.","استخدم الكيت 86-01 لإدخال الرقم (AABBH) في المجمّع (المسجل AX) وعرض النتيجة على الشاشة السباعية. ابدأ برنامجك من العنوان 00400H.");
E(1,6,"Write a program from address 600H to move the 8-bit data 45H to the Accumulator (AL).","اكتب برنامجاً ابتداءً من العنوان 600H لنقل البيانات 45H (8 بت) إلى المجمّع (المسجل AL).");
E(1,7,"Repeat the above program with the following 8-bit number 6CH by moving this data to the Accumulator (AH). Please start your program from 500H.","كرّر البرنامج السابق مع العدد 6CH (8 بت) بنقل هذه البيانات إلى المجمّع (المسجل AH). ابدأ برنامجك من العنوان 500H.");
X(1,8,"Repeat the above procedure with the following numbers data:\n• Enter DFA1H in AX\n• Enter 869BH in AX","كرّر الإجراء السابق مع البيانات التالية:\n• أدخل DFA1H في AX\n• أدخل 869BH في AX");
X(1,9,"\n• Load the value 7BH into AL and observe the result on the seven-segment display.\n• Load the value 8FH into AH and observe the result on the seven-segment display.\n• Record your observations in the result table.","\n• ضع القيمة 7BH في AL ولاحظ النتيجة على الشاشة السباعية.\n• ضع القيمة 8FH في AH ولاحظ النتيجة على الشاشة السباعية.\n• سجّل ملاحظاتك في جدول النتائج.");
/* Level 2 (Experiment 2) */
E(2,3,"Write a program to move the content of memory location (00500H-00501H) to Register CX. Then, display the result on seven segment display. Please start your program from address 00700H.\nData: AB at 500, 7D at 501.","اكتب برنامجاً لنقل محتوى موقع الذاكرة (00500H-00501H) إلى المسجل CX، ثم اعرض النتيجة على الشاشة السباعية. ابدأ برنامجك من العنوان 00700H.\nالبيانات: AB عند 500 و7D عند 501.");
E(2,4,"Load the data 8CH in register DL, and the content of memory location [00600H] to DH. Then check the content of DX register. Please let the content of memory address 00600H = AFH and start your program from 00800H.","حمّل البيانات 8CH في المسجل DL، وحمّل محتوى موقع الذاكرة [00600H] في المسجل DH. ثم افحص محتوى المسجل DX. اجعل محتوى العنوان 00600H يساوي AFH وابدأ برنامجك من العنوان 00800H.");
E(2,5,"Write a program starting at memory address 00400H to load the data 943EH into register BX. Then, move the content of register BX to memory location 0650H.","اكتب برنامجاً يبدأ من عنوان الذاكرة 00400H لتحميل البيانات 943EH في المسجل BX، ثم انقل محتوى المسجل BX إلى موقع الذاكرة 0650H.");
E(2,6,"Write a program that puts 5AH in DL and 3CH in DH, then copies the content of DX to AX. AX should show 3C5A.","اكتب برنامجاً يضع القيمة 5AH في DL والقيمة 3CH في DH، ثم ينسخ محتوى DX إلى AX. يجب أن يعرض AX القيمة 3C5A.");
/* Level 3 (Experiment 3). Exercises show only the question line: their values, instructions and program lines appear one step at a time */
E(3,6,"Interpret the machine code 8B EC.","فسّر الكود الآلي 8B EC.");
E(3,7,"Choose the MOD bits for each of the following instructions, then write its machine code:\n• MOV AL,[DI]\n• MOV AL,[DI+02H]\n• MOV AL,[DI+1000H]\nNote: in all of them R/M=101 means DI.","اختر قيمة MOD لكل تعليمة من التعليمات التالية، ثم اكتب كودها الآلي:\n• MOV AL,[DI]\n• MOV AL,[DI+02H]\n• MOV AL,[DI+1000H]\nملاحظة: في الثلاث تعني R/M=101 المسجل DI.");
E(3,8,"Write the machine code of the instruction MOV CX,[BX+DI+20H].","اكتب الكود الآلي للتعليمة MOV CX,[BX+DI+20H].");
X(3,9,"Given the following hexadecimal values, write the instruction of each value:","اكتب التعليمة التي تمثلها كل قيمة من القيم السداسية التالية:");
X(3,10,"Write the code of the following instructions:","اكتب الكود الآلي للتعليمات التالية:");
X(3,11,"The following program is used to move the content of memory location 700H to register BL and display the result in seven segments display.\nMOV BL,[0700]\nMOV AL,BL\nHLT\nPlease write the full code of this program.\nHint: your program should be started from memory location 00800H.","يُستخدم البرنامج التالي لنقل محتوى موقع الذاكرة 700H إلى المسجل BL وعرض النتيجة على الشاشة السباعية.\nMOV BL,[0700]\nMOV AL,BL\nHLT\nاكتب الكود الكامل لهذا البرنامج.\nتلميح: ابدأ برنامجك من موقع الذاكرة 00800H.");
X(3,12,"Explain what the function of the following program is, and write the code and execute it on the Lab Kit. Please write your code from 500H.","اشرح وظيفة البرنامج التالي، ثم اكتب كوده ونفّذه على الكيت. اكتب برنامجك ابتداءً من العنوان 500H.");
})();
/* Level 3: encoding-algorithm card + External Examples 1-2. Inserted after all index-based patches; SQ keys and saved progress are re-numbered. */
(function(){const R=/[A-Za-z0-9](?:[A-Za-z0-9\-\/+=,:\[\] ]*[A-Za-z0-9\]])?/g,w=x=>x.replace(R,'\u2066$&\u2069'),I=x=>'\u0002'+x+'\u0003',S=(e,a,t)=>[e,w(a),t||''];
const L=LV[3];if(!L||L.some(m=>m._x))return;
const alg={k:'c',_x:1,t:['Encoding algorithm',w('خوارزمية الترميز')],s:[
S('Goal: every MOV is encoded with the same six steps. Learn them once and use them in every exercise. You can open them any time from the Tables button, in the STEPS tab.','الهدف: كل تعليمة MOV تُرمَّز بنفس الخطوات الست. احفظها مرة واحدة واستعملها في كل تمرين. وتجدها دائماً في زر الجداول تحت تبويب «الخطوات».','t:ALG'),
S('Step 1: choose the opcode from D and W. D=1 when the destination is a register, W=1 when the data is 16-bit. The result is 88, 89, 8A or 8B.','1) اختر الأوبكود من D وW. نجعل D=1 عندما تكون الوجهة مسجلاً، وW=1 عندما تكون البيانات 16 بت. والنتيجة 88 أو 89 أو 8A أو 8B.','t:DW g:dw:D:* g:dw:W:* b:8B-C2'),
S('Step 2: choose MOD. 11 means two registers, 00 means memory with no displacement, 01 adds an 8-bit displacement, 10 adds a 16-bit one.','2) اختر MOD. القيمة 11 تعني مسجلين، و00 ذاكرة بلا إزاحة، و01 تضيف إزاحة 8 بت، و10 تضيف إزاحة 16 بت.','t:MOD g:mod:00:* g:mod:01:* g:mod:10:* g:mod:11:* b:8B-C2'),
S('Step 3: write the REG code of the register field. The W bit decides if you read the 8-bit or the 16-bit column of the table.','3) اكتب رمز REG للمسجل في هذا الحقل. والبت W يحدد هل نقرأ عمود 8 بت أم 16 بت في الجدول.','t:REG g:reg:H:1 g:reg:H:2 b:8B-C2'),
S('Step 4: write the R/M code: a register when MOD=11, or a memory form such as [BX+SI]. MOD=00 with R/M=110 is a direct address, not [BP].','4) اكتب رمز R/M: مسجل عندما MOD=11، أو صيغة ذاكرة مثل [BX+SI]. والحالة MOD=00 مع R/M=110 تعني عنواناً مباشراً وليس [BP].','t:RM g:rm:110:0 g:rm:110:1 b:8B-0E-00-05'),
S('Step 5: join MOD, REG and R/M into one byte (2+3+3 bits). Then turn each group of 4 bits into one hex digit.','5) اجمع MOD وREG وR/M في بايت واحد (2+3+3 بتات). ثم حوّل كل 4 بتات إلى رقم Hex واحد.','t:HEX g:hex:C g:hex:2 b:8B-C2'),
S('Step 6: add the displacement or the address after that byte, low byte first. For example 1234 is written 34 12.','6) أضف الإزاحة أو العنوان بعد ذلك البايت، بالبايت الأدنى أولاً. مثلاً 1234 تُكتب 34 12.','b:8B-0E-34-12'),
S('Note: a register loaded with an immediate value skips steps 2 to 5. Use B0+REG for 8-bit or B8+REG for 16-bit, then the value, low byte first.','ملاحظة: عند نقل قيمة فورية إلى مسجل نتخطى الخطوات من 2 إلى 5. نستعمل B0+REG لـ 8 بت أو B8+REG لـ 16 بت، ثم القيمة بالبايت الأدنى أولاً.','t:REG b:B8-34-12'),
S('Result: for '+I('MOV AX,DX')+' the steps give 8B, then 11 000 010 = C2. So the code is 8B C2.','النتيجة: في التعليمة '+I('MOV AX,DX')+' تعطي الخطوات 8B ثم 11 000 010 = C2. فيكون الكود 8B C2.','t:ALG r:AX r:DX b:8B-C2')
]};
const ex1={k:'e',_x:1,t:['External Example 1',w('مثال خارجي 1')],s:[
S('Goal: write the code of '+I('MOV CH,[0900H]')+'. Then flip its direction and widen it to 16 bits.','الهدف: اكتب كود التعليمة '+I('MOV CH,[0900H]')+'. ثم اقلب اتجاهها وبعدها وسّعها إلى 16 بت.','r:CX r:DX b:8A-2E-00-09'),
S('Step 1: CH is a register and the destination, so D=1. It is 8-bit, so W=0. The opcode is 8A.','1) المسجل CH هو الوجهة إذن D=1، وهو 8 بت إذن W=0. فيكون الأوبكود 8A.','t:DW g:dw:D:0 g:dw:D:2 g:dw:W:0 g:dw:W:1 b:8A-2E-00-09'),
S('Step 2: the address is written directly, with no register inside the brackets. So MOD=00 and R/M=110.','2) العنوان مكتوب مباشرة دون مسجل داخل الأقواس. إذن MOD=00 وR/M=110.','t:MOD g:mod:00:* g:rm:110:0 g:rm:110:1 b:8A-2E-00-09'),
S('Step 3: in the 8-bit column REG=101 is CH. The byte is 00 101 110 = 2E.','3) في عمود 8 بت يكون REG=101 هو CH. فيكون البايت 00 101 110 = 2E.','t:REG g:reg:101:0 g:reg:101:1 g:reg:H:1 b:8A-2E-00-09'),
S('Step 4: add the address 0900H after it, low byte first: 00 09. The code is 8A 2E 00 09.','4) نضيف العنوان 0900H بعده بالبايت الأدنى أولاً: 00 09. فيكون الكود 8A 2E 00 09.','b:8A-2E-00-09'),
S('Step 5: flip the direction. D=0 gives opcode 88, and now REG is the source. The code is 88 2E 00 09, which is '+I('MOV [0900H],CH')+'.','5) نقلب الاتجاه. القيمة D=0 تعطي الأوبكود 88 ويصبح REG هو المصدر. فيكون الكود 88 2E 00 09 وهو '+I('MOV [0900H],CH')+'.','t:DW g:dw:D:0 g:dw:D:1 b:88-2E-00-09'),
S('Step 6: widen to 16 bits to load DX. W=1 and D=1 give 8B, and REG=010 is DX. The byte is 00 010 110 = 16, so the code is 8B 16 00 09, which is '+I('MOV DX,[0900H]')+'.','6) نوسّع إلى 16 بت لتحميل DX. القيمتان W=1 وD=1 تعطيان 8B، وREG=010 هو DX. فيكون البايت 00 010 110 = 16، والكود 8B 16 00 09 وهو '+I('MOV DX,[0900H]')+'.','t:REG g:reg:010:0 g:reg:010:2 g:reg:H:2 b:8B-16-00-09'),
S('Common mistake: writing the address as 09 00. The address is 0900H, so the low byte comes first: 00 09.','خطأ شائع: كتابة العنوان 09 00. العنوان هو 0900H لذلك يأتي البايت الأدنى أولاً: 00 09.','b:8A-2E-00-09')
]};
const ex2={k:'e',_x:1,t:['External Example 2',w('مثال خارجي 2')],s:[
S('Goal: write the codes of '+I('MOV DI,2F4CH')+' and '+I('MOV CL,[SI+10H]')+'.','الهدف: اكتب كود التعليمتين '+I('MOV DI,2F4CH')+' و'+I('MOV CL,[SI+10H]')+'.','r:DI r:CX b:BF-4C-2F'),
S('Step 1: a register loaded with an immediate value has no MOD-REG-R/M byte. The opcode is B8+REG for 16-bit (B0+REG for 8-bit).','1) المسجل الذي نحمّله بقيمة فورية لا يحتاج بايت MOD-REG-R/M. الأوبكود هو B8+REG لـ 16 بت (وB0+REG لـ 8 بت).','t:REG b:BF-4C-2F'),
S('Step 2: DI is REG=111 in the 16-bit column, so the opcode is B8+7 = BF.','2) المسجل DI هو REG=111 في عمود 16 بت، فيكون الأوبكود B8+7 = BF.','t:REG g:reg:111:0 g:reg:111:2 g:reg:H:2 b:BF-4C-2F'),
S('Step 3: the value 2F4C follows the opcode, low byte first. The code is BF 4C 2F.','3) تأتي القيمة 2F4C بعد الأوبكود بالبايت الأدنى أولاً. فيكون الكود BF 4C 2F.','b:BF-4C-2F'),
S('Step 4: now '+I('MOV CL,[SI+10H]')+'. CL is the destination, so D=1, and it is 8-bit, so W=0. The opcode is 8A.','4) والآن '+I('MOV CL,[SI+10H]')+'. المسجل CL هو الوجهة إذن D=1، وهو 8 بت إذن W=0. فيكون الأوبكود 8A.','t:DW g:dw:D:0 g:dw:D:2 g:dw:W:0 g:dw:W:1 b:8A-4C-10'),
S('Step 5: 10H fits in one byte, so MOD=01. The register in the brackets is SI, so R/M=100.','5) القيمة 10H تتسع في بايت واحد، إذن MOD=01. والمسجل داخل الأقواس هو SI، إذن R/M=100.','t:MOD g:mod:01:* g:rm:100:0 g:rm:100:1 b:8A-4C-10'),
S('Step 6: CL is REG=001 in the 8-bit column. The byte is 01 001 100 = 4C.','6) المسجل CL هو REG=001 في عمود 8 بت. فيكون البايت 01 001 100 = 4C.','t:REG g:reg:001:0 g:reg:001:1 g:reg:H:1 b:8A-4C-10'),
S('Step 7: add the displacement 10 after it. The code is 8A 4C 10.','7) نضيف الإزاحة 10 بعده. فيكون الكود 8A 4C 10.','t:HEX g:hex:4 g:hex:C b:8A-4C-10'),
S('Common mistake: using B8 for every register. B8 is only AX, so the register code is added to it. DI gives BF.','خطأ شائع: استعمال B8 لكل المسجلات. الرمز B8 هو AX فقط، ونضيف إليه رمز المسجل. فالمسجل DI يعطي BF.','b:BF-4C-2F')
]};
const mp=j=>j<6?j:j<9?j+1:j+2;
L.splice(9,0,ex1,ex2);L.splice(6,0,alg);
const E=Object.keys(SQ).filter(k=>/^3\.\d+\.\d+$/.test(k)).map(k=>{const a=k.split('.');return[k,'3.'+mp(+a[1])+'.'+a[2],SQ[k]]});
E.forEach(e=>{delete SQ[e[0]]});E.forEach(e=>{SQ[e[1]]=e[2]});
if(!LS('m86m3')){const N={};Object.keys(DN).forEach(k=>{const a=k.split('.');N[a[0]=='3'?'3.'+mp(+a[1]):k]=DN[k]});Object.keys(DN).forEach(k=>{delete DN[k]});Object.assign(DN,N);LS('m86d',JSON.stringify(DN));LS('m86m3','1')}
})();
/* Level 3: new concept "From hex to binary" placed right after "MOV code format"; SQ keys and saved progress are re-numbered */
(function(){const R=/[A-Za-z0-9](?:[A-Za-z0-9\-\/+=,:\[\] ]*[A-Za-z0-9\]])?/g,w=x=>x.replace(R,'⁦$&⁩'),S=(e,a,t)=>[e,w(a),t||''];
const L=LV[3];if(!L||L.some(m=>m._h))return;
const hb={k:'c',_x:1,_h:1,t:['From hex to binary',w('من Hex إلى ثنائي')],s:[
S('Goal: the machine code is written in hex, but the 8086 reads bits. First learn to turn every hex byte into 8 bits.','الهدف: الكود الآلي مكتوب بنظام Hex لكن المعالج يقرأ البتات. نبدأ بتحويل كل بايت Hex إلى 8 بتات.','t:HEX b:8B-C2'),
S('Every hex digit is exactly 4 bits. So one byte, which is two hex digits, is 8 bits.','كل رقم Hex يساوي 4 بتات بالضبط. إذن البايت (رقمان Hex) يساوي 8 بتات.','t:HEX g:hex:8 g:hex:B b:8B-C2'),
S('Example: 8B is the digits 8 and B. 8 is 1000 and B is 1011, so 8B = 1000 1011.','مثال: 8B هو الرقم 8 والرقم B. الرقم 8 هو 1000 والرقم B هو 1011، إذن 8B = 1000 1011.','t:HEX g:hex:8 g:hex:B b:8B-C2'),
S('The second byte C2 is C (1100) and 2 (0010), so C2 = 1100 0010.','والبايت الثاني C2 هو الرقم C (1100) والرقم 2 (0010)، إذن C2 = 1100 0010.','t:HEX g:hex:C g:hex:2 b:8B-C2'),
S('Then we cut the bits into fields. The first byte 1000 1011 is 100010, then D, then W. Here D=1 and W=1.','ثم نقطّع البتات إلى حقول. البايت الأول 1000 1011 هو 100010 ثم D ثم W، وهنا D=1 وW=1.','t:DW g:dw:D:0 g:dw:D:2 g:dw:W:0 g:dw:W:2 b:8B-C2'),
S('The second byte 1100 0010 is cut as 2-3-3 bits: MOD=11, REG=000 and R/M=010.','والبايت الثاني 1100 0010 نقطّعه 2-3-3 بتات: فيكون MOD=11 وREG=000 وR/M=010.','t:MOD g:mod:11:* b:8B-C2'),
S('The way back is the same: group the bits in fours and write each group as one hex digit. 1100 0010 = C2.','والعكس صحيح: نجمع البتات كل 4 معاً ونكتب كل مجموعة برقم Hex واحد. 1100 0010 = C2.','t:HEX g:hex:C g:hex:2 b:8B-C2'),
S('Note: so we always read the code in this order: hex, then binary, then fields, then meaning. The next concepts explain each field.','ملاحظة: إذن نقرأ الكود دائماً بهذا الترتيب: Hex ثم ثنائي ثم حقول ثم المعنى. وتشرح المفاهيم التالية كل حقل.','t:HEX b:8B-C2')
]};
const mp=j=>j<2?j:j+1;
L.splice(2,0,hb);
const E=Object.keys(SQ).filter(k=>/^3\.\d+\.\d+$/.test(k)).map(k=>{const a=k.split('.');return[k,'3.'+mp(+a[1])+'.'+a[2],SQ[k]]});
E.forEach(e=>{delete SQ[e[0]]});E.forEach(e=>{SQ[e[1]]=e[2]});
if(!LS('m86m4')){const N={};Object.keys(DN).forEach(k=>{const a=k.split('.');N[a[0]=='3'?'3.'+mp(+a[1]):k]=DN[k]});Object.keys(DN).forEach(k=>{delete DN[k]});Object.assign(DN,N);LS('m86d',JSON.stringify(DN));LS('m86m4','1')}
})();
function tmKv(t){const m={EB:0,ER:1,GO:2,ST:3,EW:7,TTY:'.'};return String(t in m?m[t]:/^[0-9A-F]$/.test(t)?parseInt(t,16):t)}
function tmKp(v){const p=PL;if(!p||v==null)return;p.kp=1;if(p.ck)setTimeout(()=>tmGc(p),150);
if(!p.sq||tmKv(p.sq[p.n])!==String(v))return;p.n++;const i0=p.i;if(p.n<p.sq.length)tmHL(p.rs.concat(p.sq[p.n]));else{tmHL(p.rs);p.sd=1;p.dd[p.i]=1;tmUl(p);if(p.i<p.it.s.length-1)setTimeout(()=>{if(PL===p&&p.i===i0&&p.i<p.it.s.length-1){p.i++;tmSt()}},450);else tmChk(p)}}
g('keys').addEventListener('click',e=>{const b=e.target.closest('button');if(b)tmKp(b.dataset.k)});
document.addEventListener('keydown',e=>{if(/^(TEXTAREA|INPUT)$/.test(e.target.tagName)||e.ctrlKey||e.metaKey||e.altKey||document.documentElement.dataset.view)return;const c=e.key;tmKp(/^[0-9a-f]$/i.test(c)?String(parseInt(c,16)):{Enter:'NEXT',Backspace:'BS','-':'PRV','.':'.',Escape:'RESET',g:'2',G:'2',Insert:'INS','+':'INS',Delete:'DEL',v:'VCT',V:'VCT',F1:'F1',F2:'F2',F3:'F3'}[c])});
let XP={};try{XP=JSON.parse(LS('m86x')||'{}')||{}}catch(e){}
if(!LS('m86m4x')){const N={};Object.keys(XP).forEach(k=>{const a=k.split('.');N[a[0]=='3'&&+a[1]>=2?'3.'+(+a[1]+1):k]=XP[k]});XP=N;LS('m86x',JSON.stringify(XP));LS('m86m4x','1')}
function tmXs(){LS('m86x',JSON.stringify(XP))}
function tmXr(it,lv){if(it.k!='x')return 0;const v=XP[lv+'.'+LV[lv].indexOf(it)];return v>0&&v<it.s.length?v:0}
function tmP(it,lv){tmW=0;tmWg();const lv2=lv==null?TV:lv;PL={it:it,i:tmXr(it,lv2),ok:0,lk:0,dd:{},lv:lv2};g('tmw').classList.add('ls');tmSt();g('tmw').scrollIntoView({behavior:'smooth',block:'center'})}
function tkLn(on){const d=g('tkln');if(d)d.classList.toggle('on',!!on);g('tmw').classList.toggle('ln',!!on)}
function tmSt(){tkLn(0);PL.ln=0;g('tmw').dataset.lv=PL.lv;if(PL.it.k=='x'){const j=LV[PL.lv].indexOf(PL.it);if(j>=0&&!DN[PL.lv+'.'+j]){XP[PL.lv+'.'+j]=PL.i;tmXs()}}g('tmw').classList.toggle('qn',!!PL.nx);tkNq(PL);const a=LG=='ar'?1:0,p=PL,q=p.it.k=='q',z=q?p.it.q:p.it.s,s=z[p.i],L=LV[p.lv],j=L.indexOf(p.src||p.it),nx=!q&&!!L[j+1],ls=p.i==z.length-1;
 if(p.ls!==p.i){p.ls=p.i;p.n=0;p.dn=0;p.h=0;p.as=p.lv==3?1:0;p.kp=0;p.sd=!!p.dd[p.i];p.wr=0;p.hu=0}
 g('tmw').classList.remove('fin');
 const kk=g('tkk'),kl=({c:a?'مفهوم':'Concept',e:a?'مثال':'Example',x:a?'تمرين':'Exercise',q:a?'اختبار':'Test'})[p.it.k]||'';kk.dataset.k=p.it.k;kk.dataset.l=kl;kk.textContent=kl;
 const qt=q&&typeof s[5]=='string',qm=q&&Array.isArray(s[5]),hn=(p.it.k=='x'||qt)?(s[3+a]||''):'',hb=g('tkhint');p.qt=qt;p.ck=(p.it.k=='x'||qt)?tmPk(s[5]):0;p.mq=p.it.k=='x'&&Array.isArray(s[6])?s[6]:qm?s[5]:0;tmMc(p);hb.classList.remove('tkg');
 g('tmw').classList.toggle('hx',p.it.k=='x'||qt);g('tmw').classList.toggle('qm',qt||qm);hb.innerHTML='<svg class="ic" viewBox="0 0 24 24" aria-hidden="true"><path d="M9.5 18.5h5M10.3 21.5h3.4"/><path class="bf" d="M12 2.8a6.2 6.2 0 0 0-3.7 11.2c.7.6 1.2 1.3 1.2 2.2v.3h5v-.3c0-.9.5-1.6 1.2-2.2A6.2 6.2 0 0 0 12 2.8z"/></svg>'+(a?'تلميح':'Hint');hb.disabled=true;
 const cvx=p.it.k=='e'&&s[a].indexOf('\u27E6')>=0;g('tmw').classList.toggle('cv',cvx);g('tmt').classList.toggle('as',!!p.as);g('tkcv').disabled=true;tmCv(p);tmSay(mc(p.h&&hn?s[a]+'\u0001'+((p.mq&&p.h==1)?tmH1(s,a):hn):s[a],p.as),()=>{tmMs(p,1);tmChk(p);if(PL===p){hb.disabled=!hn||p.h>=(p.mq?2:1)||!!p.sd;g('tkcv').disabled=false}});
 const tk=q?[]:(s[2]||'').split(' ').filter(Boolean),sq=(p.it.k=='e'||p.it.k=='c')?SQ[p.lv+'.'+j+'.'+p.i]:0;p.sq=sq?sq.split(' '):0;p.rs=tk.filter(t=>t.startsWith('r:'));tmHL(sq?p.rs.concat(p.n<p.sq.length?[p.sq[p.n]]:[]):(p.it.k=='x'&&p.lv==3)?p.rs:tk);window.tbSt&&tbSt(tk,p.it.k,p.lv,s[0]);window.boSt&&boSt(tk,p.it.k);g('tkc').textContent=(p.i+1)+'/'+z.length;
 g('tmw').classList.toggle('qz',q);tkQz(p,a);g('tkp').disabled=false;const kb=g('tkb');kb.textContent=a?'\u203A':'\u2039';kb.disabled=p.i==0;kb.title=a?'خطوة للخلف':'Back one step';kb.setAttribute('aria-label',kb.title);tmUl(p);if(p.it.k!='x')g('tkn').classList.toggle('tkg',!!(p.dn&&ls&&nx))}
/* next stays locked while the step's required action (key sequence / exercise result) is not done */
function tmUl(p){if(PL!==p)return;tmGo(p);const q=p.it.k=='q',L=LV[p.lv],ls=p.i==(q?p.it.q:p.it.s).length-1,nx=!!L[L.indexOf(p.src||p.it)+1];g('tkn').disabled=!q&&(((p.sq||p.ck||p.mq)&&!p.sd)||(ls&&!nx))}
/* exercise check: after a key press, look at the kit for the requested result.
   Spec = conditions joined by "&": "AX=DFA1" (16-bit register), "AL=6E" (8-bit register),
   "M0600=8BC3" (RAM bytes starting at that address, in memory order) */
const R8=['AL','CL','DL','BL','AH','CH','DH','BH'];
function tmPk(x){if(!x)return 0;const o=[];for(const c of x.split('&')){const m=/^(\w+)=([0-9A-F]+)$/i.exec(c);if(!m)return 0;const n=m[1].toUpperCase(),h=m[2].toUpperCase();
 if(/^M[0-9A-F]+$/.test(n)){if(h.length%2)return 0;o.push({n:n,a:parseInt(n.slice(1),16),v:h.match(/../g).map(b=>parseInt(b,16)),h:h})}
 else if(n=='V')o.push({n:'V',r:parseInt(h,16),h:h});
 else if(RN.indexOf(n)>=0||R8.indexOf(n)>=0)o.push({n:n,v:parseInt(h,16),h:h});else return 0}
 return o.length?o:0}
function tmOk(c){if(c.n=='V')return st=='regv'&&ri===c.r;if(Array.isArray(c.v))return c.v.every((b,i)=>M[c.a+i]===b);const k=RN.indexOf(c.n);return k>=0?rget(k)===c.v:gb(R8.indexOf(c.n))===c.v}
function tmGc(p){if(!p||PL!==p||!p.ck||p.sd||!p.kp||!p.ck.every(tmOk))return;p.sd=1;p.dd[p.i]=1;g('tkhint').disabled=true;if(p.it.k=='q'){if(!p.hu)p.ok++;p.lk=1;p.nx=1;g('tmw').classList.add('qn');tkNq(p)}tmUl(p);const a=LG=='ar'?1:0;
 tmSay((a?'صحيح! ':'Correct! ')+p.ck.filter(c=>c.n!='V').map(c=>Array.isArray(c.v)?(a?'الذاكرة ':'RAM ')+hx(c.a,4)+': '+c.h.match(/../g).join(' '):c.n+' = '+c.h).join(', ')+'.',()=>tmChk(p))}
new MutationObserver(()=>tmGc(PL)).observe(g('regs'),{childList:true});
/* exercise hint: appears only when the button is pressed */
/* multiple-choice steps have two hints: 1) the bytes split into their bit fields, 2) the full answer */
g('tkhint').onclick=()=>{const p=PL;if(!p||(p.it.k!='x'&&!p.qt)||tmTy)return;const mq=!!p.mq,a=LG=='ar'?1:0,s=(p.it.s||p.it.q)[p.i];if(p.h>=(mq?2:1)||(mq&&p.sd))return;const h=(mq&&!p.h)?tmH1(s,a):s[3+a];if(!h)return;p.h=(p.h||0)+1;if(p.it.k=='q'&&!p.hu){p.hu=1;(p.wl=p.wl||[]).push(s)}tmSn('h');window.tbHint&&tbHint(mq&&p.h==1?1:2);g('tkhint').disabled=true;g('tkhint').classList.remove('tkg');tmSay(s[a]+'\u0001'+h,()=>{tmMs(p,1);if(PL===p&&mq&&p.h==1&&!p.sd)g('tkhint').disabled=false},Array.from(s[a]).length)};
function tmIso(x){return '\u2066'+x+'\u2069'}
function tmH1(s,a){const m=/\b[0-9A-F]{2}(?: [0-9A-F]{2})+\b/.exec(s[0]);if(!m)return '';const B=m[0].split(' ').map(h=>parseInt(h,16)),b8=n=>n.toString(2).padStart(8,'0'),b1=b8(B[0]),b2=b8(B[1]),x1=B[0].toString(16).toUpperCase(),x2=B[1].toString(16).toUpperCase().padStart(2,'0'),
 f1=b1.slice(0,4)+' '+b1.slice(4)+' ('+b1.slice(0,6)+' D='+b1[6]+' W='+b1[7]+')',f2=b2.slice(0,2)+' '+b2.slice(2,5)+' '+b2.slice(5)+' (MOD='+b2.slice(0,2)+' REG='+b2.slice(2,5)+' R/M='+b2.slice(5)+')',r=B.length>2;
 return a?'قسّم البايتات: '+tmIso(x1+' = '+f1)+' ثم '+tmIso(x2+' = '+f2)+'.'+(r?' والبايتات الباقية إزاحة أو عنوان، بالبايت الأدنى أولاً.':'')+' ارجع إلى الجداول لقراءة REG وR/M.'
  :'Split the bytes: '+x1+' = '+f1+', then '+x2+' = '+f2+'.'+(r?' The remaining bytes are a displacement or address, low byte first.':'')+' Use the tables to read REG and R/M.'}
function tmMc(p){p.mcEl=null;if(!p.mq)return;const o=p.mq.map((x,k)=>({x:x,k:k})),r=(p.i*2+1)%o.length,v=o.slice(r).concat(o.slice(0,r)),d=document.createElement('div');d.className='tkch';d.dir='ltr';
 v.forEach(e=>{const b=document.createElement('button');b.type='button';b.textContent=e.x;b.dataset.k=e.k;if(p.sd){b.disabled=true;if(!e.k)b.classList.add('ok')}d.appendChild(b)});p.mcEl=d}
function tmMs(p,on){if(on&&p&&p.mcEl&&PL===p&&window.boMc)boMc(p.mcEl)}
document.addEventListener('click',e=>{const b=e.target.closest&&e.target.closest('.tkch button'),p=PL;if(!b||!p||!p.mq||p.sd||tmTy||b.disabled)return;const a=LG=='ar'?1:0,s=(p.it.s||p.it.q)[p.i];
 if(b.dataset.k!=='0'){b.classList.add('no');b.disabled=true;tmAz(false);p.wr=(p.wr||0)+1;if(p.it.k=='q'&&p.wr==1)(p.wl=p.wl||[]).push(s);if(p.wr>=2&&p.h<2&&!g('tkhint').disabled)g('tkhint').classList.add('tkg');return}
 if(p.it.k=='q'){if(!p.wr)p.ok++;p.lk=1;p.nx=1;g('tmw').classList.add('qn');tkNq(p)}p.sd=1;p.dd[p.i]=1;[...p.mcEl.children].forEach(x=>{x.disabled=true;if(x.dataset.k==='0')x.classList.add('ok')});g('tkhint').disabled=true;g('tkhint').classList.remove('tkg');tmAz(true);tmUl(p);tmSay((a?'صحيح! ':'Correct! ')+s[3+a],()=>{tmMs(p,1);tmChk(p)})});
/* end of a concept / example: tiny check animation, orange in the list, next button glows */
function tmChk(p){if(PL!==p||p.dn||tmTy||p.it.k=='q'||p.i!=p.it.s.length-1||(p.sq&&p.n<p.sq.length)||((p.ck||p.mq)&&!p.sd))return;tmDone(p)}
function tmDone(p){p.dn=1;const k=p.it.k,L=LV[p.lv],j=L.indexOf(p.it);if(k=='x'){delete XP[p.lv+'.'+j];tmXs()}if(L[j+1]&&k!='x')g('tkn').classList.add('tkg');
 if(k=='c'||k=='e'){const d=g('tkd');d.classList.remove('go');void d.offsetWidth;d.classList.add('go')}
 const y=p.lv+'.'+j;if(!DN[y]){DN[y]=1;LS('m86d',JSON.stringify(DN));tmX()}}
/* test answers: bright rising chime when correct, soft gentle two-note "oops" when wrong (never harsh) */
function tmAz(ok){if(!sn)return;try{ac=ac||new(window.AudioContext||window.webkitAudioContext)();if(ac.state==='suspended')ac.resume();const t=ac.currentTime,n=(f,s,d,ty,vl)=>{const o=ac.createOscillator(),v=ac.createGain();o.type=ty;o.frequency.setValueAtTime(f,t+s);v.gain.setValueAtTime(.0001,t+s);v.gain.linearRampToValueAtTime(vl,t+s+.015);v.gain.exponentialRampToValueAtTime(.0001,t+s+d);o.connect(v);v.connect(ac.destination);o.start(t+s);o.stop(t+s+d+.02)};
 if(ok){[[523,0],[659,.09],[784,.18],[1047,.27]].forEach(([f,s])=>{n(f,s,.3,'sine',.07);n(f*2,s,.16,'sine',.018)})}
 else{n(392,0,.22,'triangle',.09);n(330,.16,.3,'triangle',.08);n(330*2,.16,.2,'sine',.02)}}catch(e){}}
function tmA(v){const p=PL,a=LG=='ar'?1:0,q=p.it.q[p.i],r=q[2],ok=r===v,x=q[3+a]||'',m=(ok?(a?'صحيح!':'Correct!'):(a?'ليس تماماً. الإجابة: '+(r?'صح':'خطأ'):'Not quite. The answer is '+(r?'True':'False')+'.'))+(x?(a&&!ok?'. ':' ')+x:'');p.lk=1;if(ok)p.ok++;else(p.wl=p.wl||[]).push(q);tmAz(ok);tmSay(m);p.nx=1;g('tmw').classList.add('qn');tkNq(p)}
function tkNq(p){const b=g('tkq'),a=LG=='ar',l=p.it.k=='q'&&p.i==p.it.q.length-1;b.textContent=l?(a?'إنهاء':'Finish'):(a?'التالي \u2039':'Next \u203A');b.title=b.textContent;b.setAttribute('aria-label',b.textContent)}
g('tkq').onclick=()=>{const p=PL;if(!p||!p.nx)return;p.nx=0;p.lk=0;g('tmw').classList.remove('qn');tmSn('n');if(++p.i<p.it.q.length)tmSt();else tmQe(p)};
/* end of a test round: pass at 5/9; otherwise only the missed and given-up questions come back */
function tmQe(p){const src=p.src||p.it,tot=src.q.length,need=Math.min(5,tot),a=LG=='ar'?1:0,w=p.wl||[];if(p.ok>=need||!w.length)return tmPass(p);
 p.src=src;p.it=Object.assign({},src,{q:w});p.wl=[];p.dd={};p.sk=[];p.i=0;p.ls=-1;p.lk=1;
 tmSay(a?'نتيجتك '+p.ok+'/'+tot+'، والمطلوب '+need+'/'+tot+' للنجاح. سنعيد الأسئلة التي أخطأت فيها فقط.':'Score '+p.ok+'/'+tot+'. You need '+need+'/'+tot+' to pass. Let\'s redo only the questions you missed.',()=>setTimeout(()=>{if(PL!==p)return;p.lk=0;tmSt()},1500))}
function tmPass(p){const a=LG=='ar'?1:0,n=TV;DN[p.lv+'.'+LV[p.lv].indexOf(p.src||p.it)]=1;LS('m86d',JSON.stringify(DN));TO=Math.max(TO,n+1);LS('m86p',TO);thZ(true);tmEnd();TV=0;tmSay(a?'أحسنت! نتيجتك '+p.ok+'/'+(p.src||p.it).q.length+'. أنهيت المستوى '+n+' وفُتح المستوى التالي.':'Well done! Score '+p.ok+'/'+(p.src||p.it).q.length+'. Level '+n+' done, next level unlocked.');g('tmw').classList.add('fin');tmX()}
/* Levels button: opens the level list so a new level can be chosen */
g('tklv').onclick=e=>{e.stopPropagation();g('tmw').classList.remove('fin');TV=0;tmW=1;tmX();mo(true)};
/* skip: the question goes to the end of the round; skipping it a second time gives it up (counts as missed). The test only ends after the round, and passes at 5/9 */
g('tks').onclick=()=>{const p=PL;if(!p||p.it.k!='q'||p.nx)return;if(!p.src){p.src=p.it;p.it=Object.assign({},p.src,{q:p.src.q.slice()})}
 const q=p.it.q,it=q[p.i];p.sk=p.sk||[];p.lk=0;tmSn('n');
 if(p.sk.indexOf(it)>=0){p.wl=p.wl||[];if(p.wl.indexOf(it)<0)p.wl.push(it);if(++p.i<q.length)tmSt();else tmQe(p);return}
 p.sk.push(it);q.splice(p.i,1);q.push(it);p.ls=-1;tmSt()};
g('tkp').onclick=()=>{const p=PL;if(!p||p.lk)return;if(p.it.k=='q')return(p.mq||p.qt)?0:tmA(false)};
g('tkb').onclick=()=>{const p=PL;if(!p||p.lk||p.it.k=='q')return;if(p.i>0){tmSn('b');p.i--;tmSt()}};
g('tkn').onclick=()=>{const p=PL;if(!p||p.lk)return;if(p.ln)return tmSt();if(p.it.k=='q')return(p.mq||p.qt)?0:tmA(true);if(p.i<p.it.s.length-1){tmSn('n');p.i++;tmSt()}else{const L=LV[p.lv],n=L[L.indexOf(p.it)+1];if(n){tmSn('n');tmP(n,p.lv)}}};
/* examples: machine code only; the button between back and next converts it to Assembly. Sounds: back / next / convert / hint */
function mc(s,as){return s.replace(/\u27E6([^\u27E7|]*)\|([^\u27E7]*)\u27E7/g,(m,x,y)=>'\u0002'+(as?y:x)+'\u0003')}
function tmCv(p){const b=g('tkcv'),a=LG=='ar';if(b)b.innerHTML='\u21C4 '+(p&&p.as?(a?'إلى ':'To ')+'<span class=cvl>Machine Code</span><span class=cvs>M Code</span>':(a?'إلى Assembly':'To Assembly'))}
function tmSn(k){if(!sn)return;try{ac=ac||new(window.AudioContext||window.webkitAudioContext)();if(ac.state==='suspended')ac.resume();const t=ac.currentTime,P={n:[[520,780,0,.11,'triangle',.07]],b:[[780,520,0,.11,'triangle',.07]],c:[[440,440,0,.05,'square',.03],[660,660,.06,.05,'square',.03],[880,880,.12,.06,'square',.03],[1320,1320,.19,.12,'sine',.06]],h:[[988,988,0,.35,'sine',.08],[1319,1319,.12,.5,'sine',.07]]}[k];P.forEach(([a,b,s,d,ty,vl])=>{const o=ac.createOscillator(),v=ac.createGain();o.type=ty;o.frequency.setValueAtTime(a,t+s);if(a!=b)o.frequency.exponentialRampToValueAtTime(b,t+s+d);v.gain.setValueAtTime(.0001,t+s);v.gain.linearRampToValueAtTime(vl,t+s+.01);v.gain.exponentialRampToValueAtTime(.0001,t+s+d);o.connect(v);v.connect(ac.destination);o.start(t+s);o.stop(t+s+d+.02)})}catch(e){}}
g('tkcv').onclick=()=>{const p=PL;if(!p||p.lk||tmTy||p.it.k!='e')return;const s=p.it.s[p.i][LG=='ar'?1:0];if(s.indexOf('\u27E6')<0)return;p.as=p.as?0:1;tmSn('c');const t=g('tmt');tmRn(t,tmLs(mc(s,p.as)));t.classList.toggle('as',!!p.as);tmCv(p)};
g('tmv').onclick=e=>{const b=e.target.closest('button');if(!b||b.disabled)return;if(b.classList.contains('ua0')){uaAsk=1;tmX();return}if(b.classList.contains('uan')){uaAsk=0;tmX();return}if(b.classList.contains('uay')){uaAsk=0;UL=tmCnt();LS('m86ua',UL);tmX();return}tmW=0;tmWg();if(b.classList.contains('lb')){TV=0;setTimeout(tmX,0)}else if(b.classList.contains('li')){mo(false);tmP(LV[TV][+b.dataset.i])}else{TV=+b.dataset.n;setTimeout(tmX,0)}};
function thZ(day){if(!sn)return;try{ac=ac||new(window.AudioContext||window.webkitAudioContext)();if(ac.state==='suspended')ac.resume();const t=ac.currentTime,n=(f,s,d,ty,vl)=>{const o=ac.createOscillator(),v=ac.createGain();o.type=ty;o.frequency.value=f;v.gain.setValueAtTime(.0001,t+s);v.gain.linearRampToValueAtTime(vl,t+s+.015);v.gain.exponentialRampToValueAtTime(.0001,t+s+d);o.connect(v);v.connect(ac.destination);o.start(t+s);o.stop(t+s+d+.02)};
 (day?[784,988,1319,1568]:[587,466,349,262]).forEach((f,i)=>{n(f,i*.075,.35,day?'sine':'triangle',day?.06:.07);if(day)n(f*2,i*.075,.18,'sine',.02)})}catch(e){}}
function lgZ(l){if(!sn)return;try{ac=ac||new(window.AudioContext||window.webkitAudioContext)();if(ac.state==='suspended')ac.resume();const t=ac.currentTime,ar=(l||LG)=='ar',n=(a,b,s,d,ty,vl)=>{const o=ac.createOscillator(),v=ac.createGain();o.type=ty;o.frequency.setValueAtTime(a,t+s);o.frequency.exponentialRampToValueAtTime(b,t+s+d);v.gain.setValueAtTime(.0001,t+s);v.gain.linearRampToValueAtTime(vl,t+s+.02);v.gain.exponentialRampToValueAtTime(.0001,t+s+d);o.connect(v);v.connect(ac.destination);o.start(t+s);o.stop(t+s+d+.02)};
 if(ar){n(1100,300,0,.32,'triangle',.05);[784,587].forEach((f,i)=>n(f,f,.16+i*.1,.28,'sine',.07))}else{n(300,1100,0,.32,'triangle',.05);[587,784].forEach((f,i)=>n(f,f,.16+i*.1,.28,'sine',.07))}}catch(e){}}
function tmZ(up,k){if(!sn)return;try{ac=ac||new(window.AudioContext||window.webkitAudioContext)();if(ac.state==='suspended')ac.resume();const t=ac.currentTime,n=(a,b,s,d,ty,vl)=>{const o=ac.createOscillator(),v=ac.createGain();o.type=ty;o.frequency.setValueAtTime(a,t+s);o.frequency.exponentialRampToValueAtTime(b,t+s+d);v.gain.setValueAtTime(.0001,t+s);v.gain.linearRampToValueAtTime(vl,t+s+.03);v.gain.exponentialRampToValueAtTime(.0001,t+s+d);o.connect(v);v.connect(ac.destination);o.start(t+s);o.stop(t+s+d+.02)};
 if(k=='asm'){n(90,520,0,.4,'sawtooth',.03);n(240,1500,0,.4,'sine',.045);[440,660,880,1320].forEach((q,i)=>n(q,q,.4+i*.07,i==3?.45:.16,'triangle',.07))}else if(k=='lab'){n(350,780,0,.45,'sine',.06);n(1200,400,.14,.1,'triangle',.03);n(1200,400,.3,.1,'triangle',.03);[523,784,1047].forEach((q,i)=>n(q,q,.48+i*.14,.4,'sine',.065))}else{up?n(200,900,0,.55,'triangle',.06):n(900,200,0,.55,'triangle',.06);(up?[659,880,1319]:[1319,880,523]).forEach((q,i)=>n(q,q,.5+i*.12,.32,'sine',.07))}}catch(e){}}
/* after an exercise is solved: hint button is replaced by a button to the next item */
function tmGo(p){let on=0;if(p.it.k=='x'){const L=LV[p.lv],n=L[L.indexOf(p.it)+1],ls=p.i==p.it.s.length-1;on=!!p.sd&&(!ls||!!n);g('tkn').classList.toggle('tkg',!!on)}g('tmw').classList.toggle('xd',!!on)}
/* soft click: menu button, levels button, and the levels list */
function tmK(){if(!sn)return;try{ac=ac||new(window.AudioContext||window.webkitAudioContext)();if(ac.state==='suspended')ac.resume();const t=ac.currentTime,o=ac.createOscillator(),v=ac.createGain();o.type='sine';o.frequency.setValueAtTime(620,t);o.frequency.exponentialRampToValueAtTime(980,t+.06);v.gain.setValueAtTime(.0001,t);v.gain.linearRampToValueAtTime(.07,t+.006);v.gain.exponentialRampToValueAtTime(.0001,t+.11);o.connect(v);v.connect(ac.destination);o.start(t);o.stop(t+.13)}catch(e){}}
/* power button: short power-down / power-up sound */
function pwZ(){if(!sn)return;try{ac=ac||new(window.AudioContext||window.webkitAudioContext)();if(ac.state==='suspended')ac.resume();const t=ac.currentTime,n=(a,b,s,d,ty,vl)=>{const o=ac.createOscillator(),v=ac.createGain();o.type=ty;o.frequency.setValueAtTime(a,t+s);o.frequency.exponentialRampToValueAtTime(b,t+s+d);v.gain.setValueAtTime(.0001,t+s);v.gain.linearRampToValueAtTime(vl,t+s+.01);v.gain.exponentialRampToValueAtTime(.0001,t+s+d);o.connect(v);v.connect(ac.destination);o.start(t+s);o.stop(t+s+d+.02)};n(900,120,0,.28,'sawtooth',.04);n(300,700,.3,.16,'triangle',.06);n(700,1100,.4,.14,'sine',.05)}catch(e){}}
g('pwr').addEventListener('click',pwZ);
/* Training Mode: Power also leaves the current lesson and returns to the main screen, where TKE Bot asks to pick a level */
g('pwr').addEventListener('click',()=>{if(!TM)return;tmEnd();tkLn(0);TV=0;const d=g('tkd');d.classList.remove('go');g('tmw').classList.remove('ls','qz','qn','hx','cv','fin','xd');mo(false);tmX();tmG();scrollTo({top:0,behavior:'smooth'})});
mn.addEventListener('click',tmK);g('tklv').addEventListener('click',tmK);
g('tmv').addEventListener('click',e=>{const b=e.target.closest('button');if(b&&!b.disabled)tmK()});
tmS();
fz(+LS('m86f')||100);setLang(LS('m86l')||'en');
ui();

let ip2;const tin=g('tin'),std=['standalone','fullscreen','minimal-ui','window-controls-overlay'].some(m=>matchMedia('(display-mode: '+m+')').matches)||navigator.standalone,ios=/iphone|ipad|ipod/i.test(navigator.userAgent)||(navigator.platform==='MacIntel'&&navigator.maxTouchPoints>1);
addEventListener('beforeinstallprompt',e=>{e.preventDefault();if(std)return;ip2=e;tin.hidden=false});
addEventListener('appinstalled',()=>{tin.hidden=true;ip2=null});
if(ios&&!std)tin.hidden=false;
tin.onclick=async()=>{const p=ip2;if(p){ip2=null;try{await p.prompt();await p.userChoice}catch(e){}tin.hidden=true}else alert(LG=='ar'?'اضغط زر المشاركة ثم "إضافة إلى الشاشة الرئيسية"':'Tap the Share button, then "Add to Home Screen"')};
if('serviceWorker' in navigator&&location.protocol.indexOf('http')==0)addEventListener('load',()=>navigator.serviceWorker.register('sw.js').catch(()=>{}));
})();
;
(()=>{const H=document.documentElement,$=i=>document.getElementById(i),hm=$('home'),tt=$('ttm'),T=hm.querySelector('.tr'),tr=()=>H.dataset.mode=='training';
tt.tabIndex=-1;tt.setAttribute('aria-hidden','true');
const P=['M0 18H22L28 24H60L66 18H100','M0 40H12L18 46H44L50 52H100','M0 70H30L36 64H70L76 70H100','M0 88H48L54 82H100','M12 0V30L18 36V100','M88 0V55L82 61V100'];
T.innerHTML=P.map((d,i)=>'<path d="'+d+'"/><path class=c pathLength=100 style="animation-delay:-'+i*1.3+'s" d="'+d+'"/>').join('');
const tx=()=>{const a=H.lang=='ar';hm.dir=a?'rtl':'ltr';hm.querySelectorAll('[data-e]').forEach(e=>e.textContent=a?e.dataset.a:e.dataset.e);$('hml').textContent=a?'English':'العربية';$('hmb').querySelector('.hml').textContent=a?'الرئيسية':'Home'};
new MutationObserver(tx).observe(H,{attributes:true,attributeFilter:['lang']});tx();
const lt=()=>H.classList.contains('lite'),bt=()=>{if(lt())return;hm.classList.add('bt');setTimeout(()=>hm.classList.remove('bt'),2400)};
hm.querySelectorAll('.chip').forEach((c,i)=>c.style.setProperty('--i',i));let r1=0,r2=0,cwT=0;
let hT=0;const stop=()=>{cancelAnimationFrame(r1);cancelAnimationFrame(r2);clearTimeout(cwT)};
const show=()=>{stop();clearTimeout(hT);hm.querySelectorAll('.sel').forEach(e=>e.classList.remove('sel'));hm.classList.remove('off','in','bt','ci','cw');hm.hidden=false;H.classList.add('hm');hm.scrollTop=0;void hm.offsetWidth;hm.classList.add('in');
/* frame 1: background + title + text only. frame 2 (two real rAFs, not a timer): the 4 cards fade in, 40ms apart (30ms on lite) */
r1=requestAnimationFrame(()=>{r2=requestAnimationFrame(()=>{hm.classList.add('ci','cw');cwT=setTimeout(()=>hm.classList.remove('cw'),(lt()?30:40)*4+300)})});
clearTimeout(show.t);show.t=setTimeout(()=>{hm.classList.remove('in');bt()},lt()?320:760)};
const hide=ms=>{stop();H.classList.remove('hm');hm.classList.add('off');hm.classList.remove('cw');clearTimeout(hT);hT=setTimeout(()=>{hm.hidden=true},ms)};
const vw=document.querySelectorAll('.card.asm,.card.lg');vw.forEach(c=>c.addEventListener('toggle',()=>{if(H.dataset.view&&!c.open&&c.offsetParent!==null)c.open=true}));
const go=(k,c)=>{c.classList.add('sel');setTimeout(()=>{const sw=k=='asm'?false:(k=='edu')!=tr();
const ap=()=>{const v=(k=='asm'||k=='lab')?k:'';if(v)H.dataset.view=v;else delete H.dataset.view;
document.querySelectorAll('.card.asm,.card.lg').forEach(e=>{e.open=v?e.classList.contains(v=='asm'?'asm':'lg'):false});
if(v=='asm'){const l=document.querySelectorAll('.card.gd')[2];if(l)l.open=true}};
/* perf: the heavy view switch runs once, early, while the home screen still covers the page (the overlay circle is a compositor animation and keeps running smoothly); the mid-animation callback then only hides the home */
const pre=()=>{if(!pre.d){pre.d=1;ap()}};
if((k=='asm'||k=='lab')&&(H.dataset.view!=k||sw)&&window.tmoView&&(!sw||window.tmoMode)){const r=c.getBoundingClientRect();if(window.tmoView(k,r.left+r.width/2,r.top+r.height/2,()=>{if(sw)window.tmoMode();pre();hide(0);scrollTo(0,0)})){if(!sw&&!H.classList.contains('lite'))setTimeout(pre,120);return}}
if((k=='kit'||k=='edu')&&!sw&&H.dataset.view&&window.tmoView){const r=c.getBoundingClientRect();if(window.tmoView(k=='kit'?'out':'in',r.left+r.width/2,r.top+r.height/2,()=>{pre();hide(0);scrollTo(0,0)})){if(!H.classList.contains('lite'))setTimeout(pre,120);return}}
if(sw)tt.click();ap();
hide(sw?0:360);setTimeout(()=>scrollTo(0,0),60)},240)};
hm.querySelectorAll('.chip').forEach(c=>{c.onclick=()=>go(c.dataset.go,c);const st=(p,v)=>c.style.setProperty(p,v);
c.onpointermove=e=>{if(lt())return;const r=c.getBoundingClientRect(),x=(e.clientX-r.left)/r.width,y=(e.clientY-r.top)/r.height;st('--mx',x*100+'%');st('--my',y*100+'%');if(e.pointerType=='mouse'){st('--ry',(x-.5)*8+'deg');st('--rx',(.5-y)*6+'deg')}};
c.onpointerleave=()=>{st('--rx','0deg');st('--ry','0deg')}});
$('hmb').onclick=show;$('hml').onclick=()=>$('tlg').click();$('hth').onclick=()=>$('tth').click();H.classList.add('hm');bt()})();
;
/* MEM-HEADER-SYNC: ADDR row follows the memory's horizontal scroll */
(function(){var m=document.getElementById('mem'),h=document.getElementById('mh');if(!m||!h)return;
function sync(){var sb=m.offsetWidth-m.clientWidth-m.clientLeft*2;h.style.paddingRight=(6+Math.max(0,sb))+'px';h.scrollLeft=m.scrollLeft}
m.addEventListener('scroll',function(){h.scrollLeft=m.scrollLeft},{passive:true});
if(window.ResizeObserver)new ResizeObserver(sync).observe(m);
if(window.MutationObserver)new MutationObserver(sync).observe(m,{childList:true});
sync()})();
;
(()=>{const B=document.getElementById('tbl'),bt=document.getElementById('tbtn'),W=document.getElementById('tmw');if(!B||!bt||!W)return;
/* tablesInTests: keep false to hide the table button in final tests */
const TB_CFG={tablesInTests:false};
const TP={REG:'reg',MOD:'mod',RM:'rm',DW:'dw',HEX:'hex',ALG:'alg'};
let cur=null;
const tabs=()=>B.querySelectorAll('.tbt button');
const tokens=(tags,pre)=>(tags||[]).filter(t=>typeof t==='string'&&t.startsWith(pre)).map(t=>t.slice(pre.length).toUpperCase());
const showTab=t=>{const k=TP[t];if(!k)return;tabs().forEach(x=>x.setAttribute('aria-selected',String(x.dataset.t===k)));B.querySelectorAll('.tbp').forEach(p=>p.classList.toggle('on',p.dataset.p===k));drawFrames();mark()};
const openPanel=t=>{B.hidden=false;bt.setAttribute('aria-expanded','true');if(t)showTab(t);drawFrames()};
let FR=[];
/* one orange frame around a whole row / column (measured from the cells, zoom-safe offsets); redrawn whenever the panel is shown or resized */
const drawFrames=()=>{B.querySelectorAll('.tbfr').forEach(e=>e.remove());if(B.hidden)return;
 FR.forEach(e=>{let pn,cs,row;
  if(Array.isArray(e)){const[tb,rw,col]=e;row=rw;pn=B.querySelector('.tbp[data-p="'+tb+'"]');if(!pn||!pn.classList.contains('on'))return;const t=pn.querySelector('table');
   const rows=row==='H'?[t.tHead.rows[0]]:row==='*'?[...t.rows]:[...t.tBodies[0].rows].filter(r=>r.cells[0].textContent.trim()===row);
   cs=col==='*'?rows.flatMap(r=>[...r.cells]):rows.map(r=>r&&r.cells[+col]).filter(Boolean)}
  else{pn=e.pn;if(!pn.classList.contains('on'))return;cs=e.cs}
  if(!cs.length)return;const t=pn.querySelector('table');
  let l=1e9,tp=1e9,rg=0,bt=0;cs.forEach(c=>{l=Math.min(l,c.offsetLeft);tp=Math.min(tp,c.offsetTop);rg=Math.max(rg,c.offsetLeft+c.offsetWidth);bt=Math.max(bt,c.offsetTop+c.offsetHeight)});
  const d=document.createElement('i');d.className='tbfr';d.style.cssText='left:'+(t.offsetLeft+l)+'px;top:'+(t.offsetTop+tp)+'px;width:'+(rg-l)+'px;height:'+(bt-tp)+'px';
  if(pn.dataset.p==='dw'&&row==='W')d.style.borderColor='#3ddc97';pn.appendChild(d)})};
const light=(regs,only)=>{FR=[];B.querySelectorAll('.tbfr').forEach(e=>e.remove());B.querySelectorAll('.tbhl').forEach(e=>e.classList.remove('tbhl'));regs.forEach(r=>B.querySelectorAll((only?'.tbp[data-p="'+only+'"] ':'')+'[data-r="'+r+'"]').forEach(e=>e.classList.add('tbhl')))};
const shut=()=>{hideTip();W.classList.remove('tb3');B.hidden=true;bt.setAttribute('aria-expanded','false');light([]);cur=null};
/* auto-show: on by default. Holding the Tables button for 0.8 s hides the table and turns auto-show off (saved);
   a normal press on the button opens the table and turns auto-show back on */
let auto=true,lp=0,lt=0;try{auto=localStorage.getItem('m86tb')!=='0'}catch(e){}
const setAuto=v=>{auto=v;bt.classList.toggle('off',!v);bt.title=v?'':(LGx()?'الجداول معطلة - اضغط لتفعيلها':'Tables off - tap to turn on');try{localStorage.setItem('m86tb',v?'1':'0')}catch(e){}};
bt.style.userSelect=bt.style.webkitUserSelect=bt.style.webkitTouchCallout='none';
const LGx=()=>document.documentElement.lang=='ar';
const lpStop=()=>{clearTimeout(lt);bt.classList.remove('lpd')};
setAuto(auto);
bt.addEventListener('pointerdown',e=>{if(e.pointerType==='mouse'&&e.button!==0)return;lp=0;lpStop();if(!auto){lp=1;openPanel(cur&&cur.tab);setAuto(true);return}bt.classList.add('lpd');lt=setTimeout(()=>{lp=1;bt.classList.remove('lpd');B.hidden=true;bt.setAttribute('aria-expanded','false');setAuto(false)},800)});
['pointerup','pointerleave','pointercancel'].forEach(n=>bt.addEventListener(n,lpStop));
['pointerup','pointercancel'].forEach(n=>bt.addEventListener(n,()=>setTimeout(()=>{lp=0},0)));
bt.addEventListener('contextmenu',e=>e.preventDefault());
/* one-time tip (shown once per device): how to hide the tables */
let tipT=0;const hideTip=()=>{clearTimeout(tipT);const d=document.getElementById('tbtip');if(d)d.classList.remove('on')};
const tip=()=>{let s=null;try{s=localStorage.getItem('m86tbh')}catch(e){}if(s||!auto||B.hidden)return;let d=document.getElementById('tbtip');if(!d){d=document.createElement('div');d.id='tbtip';d.setAttribute('role','status');B.insertBefore(d,B.firstChild)}
 d.textContent=LGx()?'تلميح: اضغط مطولاً على زر «الجداول» لإخفاء هذا الجدول.':'Tip: press and hold the Tables button to hide this table.';d.dir=LGx()?'rtl':'ltr';d.classList.add('on');try{localStorage.setItem('m86tbh','1')}catch(e){}clearTimeout(tipT);tipT=setTimeout(hideTip,7000)};
bt.addEventListener('pointerdown',hideTip);
bt.onclick=()=>{if(lp){lp=0;return}const o=B.hidden;B.hidden=!o;bt.setAttribute('aria-expanded',String(o));if(o){setAuto(true);drawFrames()}};
tabs().forEach(b=>b.onclick=()=>showTab(Object.keys(TP).find(k=>TP[k]===b.dataset.t)));
/* a small dot on a tab that has a highlight while another tab is on screen */
const mark=()=>{B.querySelectorAll('.tbp').forEach(pn=>{const k=pn.dataset.p,has=!!pn.querySelector('.tbhl')||FR.some(e=>Array.isArray(e)?e[0]===k:e.pn===pn),b=[...tabs()].find(x=>x.dataset.t===k);if(b)b.classList.toggle('hv',has&&!pn.classList.contains('on'))})};
const parseGs=tags=>(tags||[]).filter(t=>typeof t==='string'&&t.slice(0,2)==='g:').map(t=>t.slice(2).split(':'));
/* explicit g:<table>:<row>:<col> tags (row = code | H header | *, col = index | *): a whole row/column gets one frame, a single cell is framed on its own */
const applyGs=gs=>{gs.forEach(([tb,row,col])=>{const pn=B.querySelector('.tbp[data-p="'+tb+'"]');if(!pn)return;
  if(tb==='hex'){FR.push({pn,cs:[...pn.querySelectorAll('[data-x="'+row+'"]')]});return}
  const rows=row==='H'?[pn.querySelector('thead tr')]:row==='*'?[...pn.querySelectorAll('tr')]:[...pn.querySelectorAll('tbody tr')].filter(r=>r.cells[0].textContent.trim()===row);
  if(col==='*'||row==='*')FR.push([tb,row,col]);
  else rows.forEach(r=>{if(r&&r.cells[+col])r.cells[+col].classList.add('tbhl')})})};
/* called at every step: level 3 only; exercises keep the panel closed and dark until Hint; concepts/examples open the tab and light the named registers */
window.tbSt=(tags,kind,lv,txt)=>{if(lv!=3){shut();return}
 if(kind=='q'&&!TB_CFG.tablesInTests){shut();return}
 W.classList.add('tb3');const tab=tokens(tags,'t:')[0]||null;
 if(kind=='x'){cur={tab,h:tokens(tags,'h:'),gs:parseGs(tags)};light([]);mark();return}
 cur={tab,h:[]};
 /* the REG table lights exactly the registers the step names (AL, AH, BX...), never their 16-bit parent: names are read from the step text */
 const shownP=(B.querySelector('.tbp.on')||{}).dataset,eff=tab?TP[tab]:(shownP&&shownP.p),gs=parseGs(tags),
 own=gs.some(x=>x[0]===eff);
 /* explicit g:<table>:<row>:<col> tags (row = code | H header | *, col = index | *) light the exact row / column / cell the step talks about; without them the names found in the text are lit */
 light(!own&&eff==='reg'?[...new Set(((txt||'').match(/\b(?:AX|BX|CX|DX|SP|BP|SI|DI|AL|BL|CL|DL|AH|BH|CH|DH)\b/g))||[])]:[]);
 applyGs(gs); drawFrames();
 if(tab){if(auto)openPanel(tab);else showTab(tab)}tip();
 mark()};
/* exercise hint: opens the first named table, lights the registers, and for memory operands also frames the MOD and R/M rows (the tabs that hold them get a dot) */
window.tbHint=st=>{if(!cur)return;if(auto)openPanel(cur.tab);else if(cur.tab)showTab(cur.tab);if(st===1){light([]);drawFrames();mark();return}const gs=cur.gs||[];light(cur.h,gs.some(x=>x[0]==='rm')?'reg':'');applyGs(gs);drawFrames();mark()};
/* leaving a lesson (level = 0) closes everything */
window.tbHL=(_,lv)=>{if(!lv){shut();window.boHide&&boHide()}};
addEventListener('resize',drawFrames);if(window.ResizeObserver)new ResizeObserver(drawFrames).observe(B);
})();
;
(()=>{const D=document.getElementById('dsp');if(!D)return;
const box=document.createElement('div');box.id='bo';box.setAttribute('aria-label','Instruction bits');D.insertAdjacentElement('afterend',box);
const RN={0:['AL','CL','DL','BL','AH','CH','DH','BH'],1:['AX','CX','DX','BX','SP','BP','SI','DI']};
const EA=['BX+SI','BX+DI','BP+SI','BP+DI','SI','DI','BP','BX'];
const hx=v=>v.toString(16).toUpperCase().padStart(2,'0');
const f=(n,bits,w,c,m)=>({n,bits,w,c,m});
/* decodes the MOV family from its bytes; every bit gets a name and a meaning */
function decode(bs){if(!bs.length)return null;const b=bs[0],rows=[];let res='',dl='';
 if((b&0xFC)===0x88){const Dd=(b>>1)&1,W=b&1;
  rows.push({v:b,f:[f('opcode',b>>2,6,'op','MOV'),f('D',Dd,1,'d',Dd?'to REG':'from REG'),f('W',W,1,'w',W?'word':'byte')]});
  if(bs.length<2)return null;const m=bs[1],MOD=m>>6,R=(m>>3)&7,RM=m&7;
  rows.push({v:m,f:[f('MOD',MOD,2,'mod',['no disp','+ 8-bit disp','+ 16-bit disp','register'][MOD]),f('REG',R,3,'reg',RN[W][R]),f('R/M',RM,3,'rm',MOD==3?RN[W][RM]:(MOD==0&&RM==6?'direct':'['+EA[RM]+(MOD==1?'+D8':MOD==2?'+D16':'')+']'))]});
  const nd=MOD==1?1:(MOD==2||(MOD==0&&RM==6))?2:0;let k=2;
  for(let i=0;i<nd;i++,k++){if(bs[k]===undefined)return null;rows.push({v:bs[k],f:[f(nd==2?(i?'disp hi':'disp lo'):'disp',bs[k],8,'dsp',MOD==0?'address':MOD==1?'added, 8-bit':'added, 16-bit')]})}
  const dv=nd==1?bs[2]:nd==2?(bs[2]|(bs[3]<<8)):null,hv=(v,w)=>v.toString(16).toUpperCase().padStart(w,'0');
  const reg=RN[W][R],addr=MOD==0&&RM==6?'['+hv(dv,4)+'H]':'['+EA[RM]+(dv!==null?'+'+hv(dv,nd==1?2:4)+'H':'')+']',rm=MOD==3?RN[W][RM]:addr;
  res=Dd?'MOV '+reg+','+rm:'MOV '+rm+','+reg;dl=dv===null?'':(MOD==0&&RM==6)?'['+hv(dv,4)+'H]':'+'+hv(dv,nd==1?2:4)+'H';
 } else if((b&0xF0)===0xB0){const W=(b>>3)&1,R=b&7;
  rows.push({v:b,f:[f('opcode',0xB,4,'op','MOV imm'),f('W',W,1,'w',W?'word':'byte'),f('REG',R,3,'reg',RN[W][R])]});
  const n=W?2:1;for(let i=0;i<n;i++){if(bs[1+i]===undefined)return null;rows.push({v:bs[1+i],f:[f(n==2?(i?'imm hi':'imm lo'):'imm',bs[1+i],8,'dsp','value')]})}
  const iv=W?(bs[1]|(bs[2]<<8)):bs[1];dl=iv.toString(16).toUpperCase().padStart(W?4:2,'0')+'H';res='MOV '+RN[W][R]+','+dl;
 } else return null;
 return {rows,res,dl};}
/* one bit as a small 7-segment digit: 1 lights segments b,c; 0 lights all but g */
const SEG={a:'x=2 y=0 w=6 h=2',b:'x=8 y=2 w=2 h=5',c:'x=8 y=9 w=2 h=5',d:'x=2 y=14 w=6 h=2',e:'x=0 y=9 w=2 h=5',f:'x=0 y=2 w=2 h=5',g:'x=2 y=7 w=6 h=2'};
const sev=bit=>{const on=bit?'bc':'abcdef';return '<svg class=sd viewBox="0 0 10 16" aria-hidden=true>'+Object.keys(SEG).map(k=>{const p=SEG[k].split(' ').reduce((o,t)=>{const[q,v]=t.split('=');o[q]=v;return o},{});return '<rect class="'+(on.includes(k)?'l':'o')+'" x="'+p.x+'" y="'+p.y+'" width="'+p.w+'" height="'+p.h+'"/>'}).join('')+'</svg>'};
const fieldHTML=x=>{let d='';for(let i=x.w-1;i>=0;i--)d+=sev((x.bits>>i)&1);return '<div class="fg '+x.c+'"><div class=fd>'+d+'</div><div class=fl>'+x.n+'</div><div class=fm>'+x.m+'</div></div>'};
const chip=r=>{const x=r.f[0];return '<span class="ch '+x.c+'"><i>'+x.n+'</i><b>'+hx(x.bits)+'</b></span>'};
const byteRow=r=>{const x=r.f[0];let d='';for(let i=x.w-1;i>=0;i--)d+=sev((x.bits>>i)&1);return '<div class="br '+x.c+'"><i>'+x.n+'</i><div class=fd>'+d+'</div><b>'+hx(x.bits)+'</b></div>'};
/* displacement / immediate bytes: no labels, no bits, just the stored bytes as hex, low first: 00 + 05 */
const isD=r=>/^(disp|imm)/.test(r.f[0].n);
const dispLine=(rs,dl)=>'<div class=bd>'+rs.map(r=>'<b>'+hx(r.v)+'</b>').join('<span>+</span>')+(dl?'<span>=</span><b class=bdv>'+dl+'</b>':'')+'</div>';
const colHTML=(t,r)=>'<div class=bc><div class=bt><span>'+t+'</span><b>'+hx(r.v)+'</b></div><div class=bg>'+r.f.map(fieldHTML).join('')+'</div></div>';
/* opcode byte on the left, operand byte (MOD-REG-R/M, or the immediate value) on the right, side by side; extra disp bytes + the decoded instruction in a thin strip below */
function layout(d){const rows=d.rows,L=rows[0];let right,ex;
 if(rows[1]&&rows[1].f[0].n==='MOD'){right=colHTML('OPERAND',rows[1]);ex=rows.slice(2)}
 else{right='<div class=bc><div class=bt><span>OPERAND</span></div><div class="bg bv">'+(rows.length>1?dispLine(rows.slice(1),d.dl):'<i>-</i>')+'</div></div>';ex=[]}
 const dr=ex.filter(isD);
 return '<div class=bw>'+colHTML('OPCODE',L)+right+'</div><div class=bf>'+(dr.length?dispLine(dr,d.dl):'')+'<span class=bres>'+d.res+'</span></div>'}
/* box sits exactly over the display; the display grows just enough so nothing needs scrolling */
/* the panel covers the 7-segment display AND the ADDRESS/DATA DISPLAY labels under it, without moving anything else; if the content is taller it is scaled down to fit */
function place(){if(!box.classList.contains('on'))return;const lb=document.querySelector('.kit .lb'),top=D.offsetTop,w=D.offsetWidth,avail=(lb?lb.offsetTop+lb.offsetHeight:top+D.offsetHeight)-top,inn=box.firstElementChild;if(!inn)return;
 box.style.top=top+'px';box.style.left=D.offsetLeft+'px';box.style.width=w+'px';box.style.height=avail+'px';
 inn.style.transform='';inn.style.width=(w-14)+'px';
 const need=inn.offsetHeight,room=avail-12,k=need>room?Math.max(.5,room/need):1;
 if(k<1){inn.style.width=((w-14)/k)+'px';inn.style.transform='scale('+k+')';inn.style.transformOrigin='0 0'}}
window.boSt=(tags,kind)=>{const t=(tags||[]).find(x=>typeof x==='string'&&x.startsWith('b:'));
 if(!t||(kind!=='c'&&kind!=='e')){boHide();return}
 const bs=t.slice(2).split('-').map(h=>parseInt(h,16));const d=decode(bs);if(!d){boHide();return}
 box.innerHTML='<div id=boi>'+layout(d)+'</div>';D.classList.add('bx');box.classList.add('on');place()};
window.boMc=el=>{box.innerHTML='';const w=document.createElement('div');w.id='boi';w.appendChild(el);box.appendChild(w);D.classList.add('bx');box.classList.add('on');place()};
window.boHide=()=>{box.classList.remove('on');box.innerHTML='';D.classList.remove('bx')};
if(window.ResizeObserver)new ResizeObserver(place).observe(D);addEventListener('resize',place);
})();
;
/* TABLES-BESIDE-KIT: on wide screens (>=820px, same breakpoint as the two-column layout) the tables panel moves to the top of the right column, next to the trainer kit; on narrow screens it returns between the board and the keys */
(function(){const B=document.getElementById('tbl'),K=document.getElementById('keys'),A=document.querySelector('main>aside');if(!B||!K||!A)return;
const mq=matchMedia('(min-width:820px)'),put=()=>{if(mq.matches){if(B.parentNode!==A)A.insertBefore(B,A.firstChild)}else if(B.parentNode!==K.parentNode)K.parentNode.insertBefore(B,K);
document.documentElement.classList.toggle('tbs',mq.matches);dispatchEvent(new Event('resize'))};
mq.addEventListener?mq.addEventListener('change',put):mq.addListener(put);put()})();
