document.getElementById("tke-splash").onclick=function(){this.style.display="none"};

const $=i=>document.getElementById(i),hx=(n,l)=>(n>>>0).toString(16).toUpperCase().padStart(l,'0');
const M=new Uint8Array(1<<20),r=new Uint16Array(8),s=new Uint16Array(4);
let ip=0x2000,F=2,ov,rp,md,rg,rm,ea,sg,op,q,led=0,run=0,ex='',vw=0,st='i',cmd='',buf='',adr=0x2000,ri=0,note='';
const io=new Uint8Array(65536);let bp=-1,bpk=0,wi=0,wv=[],tm='',pt=0,ci=0,mm=0;
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
const stop=(m,e)=>{run=0;ex=e||'HALt';note=m};
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
function int(n){const vi=rw(n*4),vc=rw(n*4+2);if(!vi&&!vc){if(n==3){run=0;st='i';cmd='';buf='';ex=' CC ';note='Program halted (CC)\nREG registers | GO run again';return}return stop('INT '+n+' executed - stopped')}push(F);push(s[1]);push(ip);F&=~768;ip=vi;s[1]=vc}
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
 else if(st=='i'){a=vw?hx(ip,4):'8086';d=vw?'  '+hx(M[A(s[1],ip)],2):' uP '}
 else if(st=='addr'){a=buf?buf.padStart(4):'----';d='    ';n=cmd=='GO'?'GO: type the address\nNEXT, then TTY to run':cmd+': type the address\nthen NEXT'}
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
 const pa=A(s[1],ip);let hl=pa,bs=pa,h='';
 if(st=='addr')bs=adr;else if(st=='data'||st=='dmp')hl=bs=adr;else if(st=='cmp')hl=bs=wv[0]+ci;
 bs&=1048560;
 for(let i=0;i<128;i++){const p=bs+i;if(i%16==0)h+=(i?'\n':'')+hx(p,5)+': ';h+=(p==hl?'<b>'+hx(M[p],2)+'</b>':hx(M[p],2))+' '}
 $('mem').innerHTML=h}
function reset(){run=0;r.fill(0);s.fill(0);r[4]=0x3FFE;ip=0x2000;F=2;led=0;io.fill(0);wv=[];wi=0;tm='';st='i';cmd='';buf='';ex='';vw=0;note=MON;ui()}
function go(){run=1;(function t(){if(run){for(let i=0;i<40000&&run;i++)step();ui();if(run)setTimeout(t,0)}})()}
function cm(){if(!buf)return;const x=parseInt(buf,16);if(st=='data')cmd=='EW'?ww(adr,x):wb(adr,x);else if(st=='regv')rset(ri,x);buf=''}
function key(k){
 if(k=='RESET')return reset();
 if(run)return;
 vw=0;ex='';tm='';const isHex=typeof k=='number';if(ext(k,isHex))return;

 if(k=='BS'){buf=buf.slice(0,-1);return ui()}

 // 1. TTY / . Key Handling
 if(k=='.'){
  if(st=='data'){
   cm();st='i';buf='';cmd='';note='Saved. '+MON;
  }else if(st=='gor'){
   ip=adr&65535;buf='';cmd='';st='i';go();return;
  }else if(st=='addr'&&cmd=='GO'){
   /* address must be confirmed with NEXT before TTY runs it */
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
  note='GO: type the address\nNEXT, then TTY to run';
  return ui();
 }

 // Check for Key 2 pressed when Buffer is already full (4 hex digits) -> Treat as GO
 if(isHex&&k==2&&(st=='rdy'||st=='i')&&buf.length>=4){
  cmd='GO';st='addr';
  note='GO: type the address\nNEXT, then TTY to run';
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
const done=(m,c)=>{st='i';cmd='';buf='';wv=[];wi=0;ex=c||'';note=m+'\n'+MK};
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
 b.forEach((e,i)=>wb(a+i,e));adr=a;ip=a&65535;s[1]=0;st='i';cmd='';buf='';ex='';vw=0;run=0;note=(typeof t=='string'?t+'\n':'')+'Loaded '+b.length+' bytes at '+hx(a,4)+'\nRun: GO, '+hx(a,4)+', NEXT, TTY';ui()}
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
reset();

(()=>{const g=i=>document.getElementById(i),t=g('asm'),l=g('ln'),i=g('asi');
const S=['; Sum of 1..10  ->  [2100h] and port 80h','        ORG  2000h','        MOV  AX, 0','        MOV  CX, 10','AGAIN:  ADD  AX, CX','        LOOP AGAIN','        MOV  [2100h], AX','        OUT  80h, AL','        INT  3',''].join('\n');
const u=()=>{const n=t.value.split('\n').length;l.textContent=Array.from({length:n},(_,k)=>k+1).join('\n');i.textContent=n+' lines \u00b7 '+t.value.length+' chars';l.scrollTop=t.scrollTop};
t.addEventListener('input',u);t.addEventListener('scroll',()=>{l.scrollTop=t.scrollTop});
t.addEventListener('keydown',e=>{if(e.key==='Tab'){e.preventDefault();t.setRangeText('\t',t.selectionStart,t.selectionEnd,'end');u()}});
g('asl').onclick=()=>{t.value=S;u()};
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
g('asm').addEventListener('keydown',e=>{if((e.ctrlKey||e.metaKey)&&e.key=='Enter'){e.preventDefault();doAsm(1)}});
const SAMP=[['; Sum of 1..10  ->  [2100h] and port 80h','        ORG  2000h','        MOV  AX, 0','        MOV  CX, 10','AGAIN:  ADD  AX, CX','        LOOP AGAIN','        MOV  [2100h], AX','        OUT  80h, AL','        INT  3',''].join('\n'),['; Running light on the 8 LEDs (port 80h)','        ORG  2000h','        MOV  AL, 1','SHOW:   OUT  80h, AL','        MOV  CX, 0FFFFh','DELAY:  LOOP DELAY','        ROL  AL, 1','        JMP  SHOW',''].join('\n')];
let si=0;g('asl').onclick=()=>{si=(si+1)%2;const t=g('asm');t.value=SAMP[si];t.dispatchEvent(new Event('input'))};
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
mn.onclick=e=>{e.stopPropagation();mo(mp.hidden)};document.addEventListener('click',e=>{if(!tb.contains(e.target))mo(false)});
g('tth').onclick=()=>{const d=D.dataset.theme!='light';th(d?'light':'dark');thZ(d)};
g('tfz').onclick=()=>{g('tfw').hidden=!g('tfw').hidden};g('tfr').oninput=e=>fz(e.target.value);
g('tlg').onclick=()=>{setLang(LG=='ar'?'en':'ar');lgFx();lgZ()};
let ac,sn=LS('m86s')!=='0';const sl2=()=>tl();
const SV=p=>'<svg class=ic viewBox="0 0 24 24" aria-hidden=true>'+p+'</svg>',IT=SV('<path d="m5 8 6 6"/><path d="m4 14 6-6 2-3"/><path d="M2 5h12"/><path d="M7 2h1"/><path d="m22 22-5-10-5 10"/><path d="M14 18h6"/>'),IV=SV('<path d="M11 5 6 9H2v6h4l5 4z"/><path d="M15.5 8.5a5 5 0 0 1 0 7"/><path d="M19 5a10 10 0 0 1 0 14"/>'),IX=SV('<path d="M11 5 6 9H2v6h4l5 4z"/><path d="m22 9-6 6"/><path d="m16 9 6 6"/>'),FZ=v=>'<span class=fzW><span class=fzS><i>A</i><b>A</b></span><span class=fzP style="--p:'+Math.max(0,Math.min(100,(v-80)/.8))+'%">'+v+'%</span></span>';
const beep=(f,d)=>{if(!sn)return;try{ac=ac||new(window.AudioContext||window.webkitAudioContext)();if(ac.state==='suspended')ac.resume();const t=ac.currentTime,r=ac.sampleRate;
if(d>=.1){[[659,0],[988,.09]].forEach(([q,s])=>{const o=ac.createOscillator(),v=ac.createGain();o.frequency.value=q;v.gain.setValueAtTime(.0001,t+s);v.gain.linearRampToValueAtTime(.08,t+s+.005);v.gain.exponentialRampToValueAtTime(.0001,t+s+.3);o.connect(v);v.connect(ac.destination);o.start(t+s);o.stop(t+s+.32)});return}
const o=ac.createOscillator(),v=ac.createGain(),u=t+d+.02;o.type='triangle';o.frequency.value=1500;v.gain.setValueAtTime(.0001,t);v.gain.linearRampToValueAtTime(.05,t+.004);v.gain.exponentialRampToValueAtTime(.0001,u);o.connect(v);v.connect(ac.destination);o.start(t);o.stop(u+.01)}catch(e){}};
g('tsn').onclick=()=>{sn=!sn;LS('m86s',sn?'1':'0');sl2();beep(1300,.05)};
g('keys').addEventListener('click',e=>{if(e.target.closest('button'))beep(1300,.03)});
/* changed registers / flags / memory */
let pr=0;const AT=[
['Monitor Ready','الشاشة جاهزة'],['EB/EW edit | GO run | ST step | REG','EB/EW تعديل | GO تشغيل | ST خطوة | REG'],
['Running...','قيد التشغيل...'],['RESET stops it','RESET يوقفه'],['GO: type the address','GO: اكتب العنوان'],['NEXT, then TTY to run','NEXT ثم TTY للتشغيل'],
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
const u2=ui;ui=function(){u2();if(LG=='ar')arS();const t=performance.now(),hot=(k,v)=>{if(PV[k]!==undefined&&PV[k]!=v)TT[k]=t;PV[k]=v;const d=t-(TT[k]||-1e9);return d<W?d:-1};
 [...g('regs').children].forEach((e,i)=>{if(i<RN.length){const d=hot('r'+i,rget(i));if(d>=0)e.lastChild.style.animation=an(d)}});
 [...g('fl').children].forEach((e,i)=>{const d=hot('f'+i,F&FM[i]?1:0);if(d>=0)e.style.animation=an(d)});
 for(let i=0;i<262144;i++)if(M[i]!==SH[i]){SH[i]=M[i];TT['m'+i]=t;const j=RC.indexOf(i);if(j>=0)RC.splice(j,1);RC.unshift(i);RC.length>8&&RC.pop()}
 const m=g('mem');m.innerHTML=m.innerHTML.replace(/^([0-9A-F]{5}): (.*)$/gm,(z,a,x)=>{let i=0;return a+': '+x.replace(/(?:<b>)?[0-9A-F]{2}(?:<\/b>)? /g,y=>{const d=t-(TT['m'+(parseInt(a,16)+i++)]||-1e9);return d<W?'<i style="animation:'+an(d)+'">'+y.slice(0,-1)+'</i> ':y})});
 if(pr&&!run)beep(880,.15);pr=run};
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
['أول برنامج',`خزّن <b>B4 AA CC</b> عند 0500 ثم شغّله:<ol><li>في وضع الخمول اضغط <kbd>0</kbd> (EB).</li><li>اكتب <kbd>5</kbd><kbd>0</kbd><kbd>0</kbd> ثم <kbd>NEXT</kbd>.</li><li>أدخل <b>B4</b> ثم <b>AA</b> ثم <b>CC</b> مع <kbd>NEXT</kbd> بعد كل بايت، ثم اضغط <kbd>TTY</kbd>.</li><li>للتشغيل: <kbd>2</kbd> (GO)، اكتب 500، <kbd>NEXT</kbd>، ثم <kbd>TTY</kbd>.</li><li>يتوقف عند CC ويظهر AX = AA00 في بطاقة السجلات.</li></ol>`],
['تعديل الذاكرة (EB / EW)',`<ol><li><kbd>0</kbd> (EB) لتعديل البايتات و<kbd>7</kbd> (EW) لتعديل الكلمات 16 بت.</li><li>اكتب العنوان ثم <kbd>NEXT</kbd>.</li><li>اكتب قيمة ثم <kbd>NEXT</kbd> للحفظ والانتقال للعنوان التالي؛ <kbd>PRV</kbd> للحفظ والرجوع.</li><li><kbd>NEXT</kbd> دون كتابة يتصفح الذاكرة، و<kbd>TTY</kbd> يحفظ ويخرج.</li></ol>EW تخزّن البايت الأدنى أولاً (1234 تُحفظ 34 12).`],
['إدراج وحذف بايتات (INS / DEL)',`<ol><li>افتح بايتاً بـ EB أو EW ثم <kbd>NEXT</kbd> لعرض البيانات (يعملان في هذا الوضع فقط).</li><li><kbd>INS</kbd> يفتح فراغاً 00h ويزيح ما بعده للأعلى.</li><li><kbd>DEL</kbd> يحذف البايت الحالي ويزيح ما بعده للأسفل.</li></ol>إزاحات القفز والنداء لا تُصحَّح تلقائياً، فتحقق منها بعد التعديل.`],
['ملء ونسخ ومقارنة الكتل (FILL, MV, BC, VR)',`<ul><li><b>FILL</b> (مفتاح PRV في الخمول): SA البداية، EA النهاية، DAtA البايت. <kbd>NEXT</kbd> بعد القيمة الأخيرة ينفّذ.</li><li><b>MV</b> (<kbd>6</kbd>): نسخ كتلة (SA وEA وdESt)، والتداخل يُعالَج صحيحاً.</li><li><b>BC</b> (<kbd>C</kbd>) و<b>VR</b> (<kbd>E</kbd>): SA ثم EA ثم SA2 بداية الكتلة الثانية؛ عند أي اختلاف يتوقف الكيت ويعرض العنوان والبايتين.</li><li><kbd>PRV</kbd> يرجع خطوة و<kbd>TTY</kbd> يلغي دون تغيير الذاكرة، والنطاق الخاطئ يعرض Err.</li></ul>`],
['منافذ الإدخال والإخراج (IB, IW, OB, OW)',`<ul><li><b>IB</b> (<kbd>4</kbd>) و<b>IW</b> (<kbd>8</kbd>): اكتب عنوان المنفذ ثم <kbd>NEXT</kbd> لعرض قيمته.</li><li><b>OB</b> (<kbd>5</kbd>) و<b>OW</b> (<kbd>9</kbd>): اكتب المنفذ و<kbd>NEXT</kbd> ثم القيمة و<kbd>NEXT</kbd> للكتابة؛ <kbd>TTY</kbd> للخروج.</li><li>المنفذان 00h و80h هما الـ LEDs D7-D0، وكل منفذ آخر يحتفظ بآخر قيمة كُتبت ويقرؤها IN.</li></ul>`],
['المقاطعات ومفاتيح الوظائف (VCT, F1-F3)',`<ul><li><b>VCT</b>: اكتب رقم المتجه (00-FF) ثم <kbd>NEXT</kbd>؛ يحفظ FLAGS وCS وIP ثم ينتقل إلى المعالج.</li><li><b>F1</b> نقطة توقف: أدخل عنواناً فيتوقف GO قبله (brEA). <kbd>NEXT</kbd> فارغ يمسحها.</li><li><b>F2</b> تفريغ: يعرض 16 بايتاً، و<kbd>NEXT</kbd>/<kbd>PRV</kbd> يتحركان 16 بايتاً.</li><li><b>F3</b> ربط: رقم INT ثم عنوان المعالج لملء جدول المتجهات.</li></ul>`],
['تشغيل برنامج (GO)',`<ol><li>اضغط <kbd>2</kbd> (GO).</li><li>اكتب عنوان البداية ثم <kbd>NEXT</kbd>.</li><li>اضغط <kbd>TTY</kbd> للتشغيل.</li></ol>يتوقف البرنامج عند CC (INT 3) أو HLT، و<kbd>RESET</kbd> يوقفه في أي وقت.`],
['التنفيذ خطوة بخطوة (ST)',`<ol><li>حدّد البداية: <kbd>REG</kbd> ثم <kbd>C</kbd> (IP) ثم العنوان ثم <kbd>TTY</kbd> (قيمة IP بعد RESET هي 2000).</li><li>اضغط <kbd>3</kbd> (ST) لتنفيذ تعليمة واحدة.</li><li>كرر ST وراقب تغيّر بطاقة السجلات.</li></ol>`],
['السجلات (REG / ER)',`<ol><li>اضغط <kbd>REG</kbd> (أو <kbd>1</kbd> في وضع الخمول).</li><li>اضغط مفتاح السجل: 0 AX، 1 BX، 2 CX، 3 DX، 4 SP، 5 BP، 6 SI، 7 DI، 8 CS، 9 DS، A SS، B ES، C IP، D FL.</li><li>اكتب حتى 4 خانات لتغيير القيمة؛ <kbd>NEXT</kbd>/<kbd>PRV</kbd> للتنقل و<kbd>TTY</kbd> للحفظ والخروج.</li></ol>`],
['المفاتيح والشاشات',`<ul><li><b>الزرقاء</b>: RESET وREG وNEXT وPRV وTTY وB.S وINS وDEL وVCT وF1-F3.</li><li><b>السوداء</b>: أرقام 0-F، وفي الخمول تنفّذ الأوامر.</li><li><b>LEDs D7-D0</b>: آخر بايت كتبته تعليمة OUT.</li><li><b>لوحة المفاتيح</b>: 0-9 وA-F، Enter = NEXT، Backspace = B.S، - = PRV، . = TTY، G = GO، Esc = RESET، V = VCT.</li></ul>`],
['محرر Assembly',`<ol><li>اكتب كود 8086 وحدّد عنوان التحميل بـ ORG (مثل ORG 2000h).</li><li><b>تجميع</b> يترجم الكود ويحمّله في الذاكرة، ثم شغّله بـ GO.</li><li><b>تجميع وتشغيل</b> يفعل الاثنين (Ctrl+Enter)؛ أنهِ كودك بـ INT 3.</li><li>الأخطاء تظهر برقم السطر ويُظلَّل السطر بالأحمر؛ اضغط الخطأ للانتقال إليه.</li></ol>`],
['حل المشكلات',`<ul><li><b>مفتاح لا يعمل؟</b> راجع الشاشة الخضراء فهي توضح الوضع الحالي.</li><li><b>المفتاح الأسود يكتب رقماً:</b> الكيت ليس في الخمول، اضغط <kbd>RESET</kbd>.</li><li><b>TTY لا يشغّل البرنامج:</b> بعد GO اكتب العنوان واضغط <kbd>NEXT</kbd> أولاً.</li><li><b>البرنامج لا يتوقف:</b> أنهِه بـ CC (INT 3) أو اضغط <kbd>RESET</kbd>.</li></ul>`]];
function lgFx(){const e=document.querySelector('main'),ar=LG=='ar',rm=matchMedia('(prefers-reduced-motion:reduce)').matches,sg=ar?1:-1;
 if(!e.animate)return;
 if(lgFx.a)lgFx.a.forEach(x=>{try{x.cancel()}catch(_){}});
 const o=document.getElementById('lgo')||(()=>{const d=document.createElement('div');d.id='lgo';d.innerHTML='<i></i><b></b>';document.body.appendChild(d);return d})(),bd=o.querySelector('i'),pl=o.querySelector('b');
 pl.textContent=ar?'العربية':'English';pl.dir=ar?'rtl':'ltr';o.style.display='block';
 const E='cubic-bezier(.2,.7,.2,1)',A=[
  e.animate(rm?[{opacity:.2},{opacity:1}]:[{opacity:.15,transform:'translateX('+sg*28+'px) scale(.98)'},{opacity:1,transform:'none'}],{duration:rm?350:620,easing:E,delay:rm?0:120}),
  pl.animate(rm?[{opacity:0},{opacity:1,offset:.25},{opacity:1,offset:.7},{opacity:0}]:[{opacity:0,transform:'scale(.8)'},{opacity:1,transform:'scale(1)',offset:.25},{opacity:1,transform:'scale(1)',offset:.7},{opacity:0,transform:'scale(1.06)'}],{duration:rm?600:820,easing:'ease-out'})];
 if(!rm)A.push(bd.animate([{transform:'translateX('+(ar?'100vw':'-55vw')+')'},{transform:'translateX('+(ar?'-55vw':'100vw')+')'}],{duration:720,easing:'ease-in-out'}));
 else bd.style.display='none';
 lgFx.a=A;const done=()=>{if(lgFx.a===A){o.style.display='none';bd.style.display=''}};
 Promise.all(A.map(x=>x.finished)).then(done,()=>{})}
function setLang(l){LG=l;LS('m86l',l);D.lang=l;D.classList.toggle('ar',l=='ar');const a=l=='ar',o0=document.querySelector('#exs option');if(o0)o0.textContent=a?'أمثلة…':'Examples…';
 t.dataset.pe=t.dataset.pe||t.placeholder;t.placeholder=a?'; اكتب كود 8086 هنا':t.dataset.pe;
 document.querySelectorAll('.lg>details').forEach((d,i)=>{d.dataset.en=d.dataset.en||d.innerHTML;d.innerHTML=a?'<summary>'+AG[i][0]+'</summary><div>'+AG[i][1]+'</div>':d.dataset.en});tl();ui();tmLb()}
function tmLb(){if(!PL)return;const a=LG=='ar',q=PL.it.k=='q',kb=g('tkb');kb.textContent=a?'\u203A':'\u2039';kb.title=a?'خطوة للخلف':'Back one step';kb.setAttribute('aria-label',kb.title);g('tkn').textContent=q?'\u2713':(a?'\u2039':'\u203A');tmGo(PL)}
function tl(){const a=LG=='ar';document.querySelectorAll('[data-ar]').forEach(e=>{e.dataset.en=e.dataset.en||e.textContent;e.textContent=a?e.dataset.ar:e.dataset.en});
 g('tsn').innerHTML=(sn?IV:IX)+(sn?(a?'الصوت':'Sound'):(a?'صامت':'Muted'));g('tlg').innerHTML=IT+(a?'English':'العربية');
 g('tfz').innerHTML=FZ(g('tfr').value);g('tfz').title=(a?'حجم الخط ':'Text size ')+g('tfr').value+'%';tmL()}
[['#asr','تجميع وتشغيل'],['#asb','تجميع'],['#asc','نسخ'],['#ass','حفظ .asm'],['#asx','مسح'],['#ld','تحميل'],['#lc','مسح']].forEach(([q,a])=>document.querySelector(q).dataset.ar=a);
['السجلات','الذاكرة (RAM 00000–3FFFF)','تحميل برنامج','محرر Assembly','دليل المختبر'].forEach((a,i)=>document.querySelectorAll('.card.gd>summary')[i].dataset.ar=a);
/* Training Mode: top-centre toggle with a switch animation (state is saved; no animation on page load) */
let TM=LS('m86m')=='t',tmb=0,TO=+LS('m86p')||1,tmLg='',tmY=0,TV=0,PL=0,HLT=[],tmTy=0,DN={};try{DN=JSON.parse(LS('m86d')||'{}')||{}}catch(e){}const ttm=g('ttm'),tmo=g('tmo'),tmd=tmo.querySelector('.tmo-d');
function tmL(){const a=LG=='ar';ttm.querySelector('.tml').textContent=a?'تدريب':'Training';ttm.setAttribute('aria-label',a?'وضع التدريب':'Training Mode');ttm.title=TM?(a?'العودة إلى الوضع العادي':'Back to normal mode'):(a?'وضع التدريب':'Training Mode');tmX()}
function tmS(){if(!TM)tmEnd();D.dataset.mode=TM?'training':'normal';ttm.classList.toggle('on',TM);ttm.setAttribute('aria-pressed',TM);tmL()}
ttm.onclick=()=>{if(tmb)return;tmb=1;const a=LG=='ar',k=TM?'out':'in',bb=ttm.getBoundingClientRect(),x=bb.left+bb.width/2,y=bb.top+bb.height/2,w=innerWidth,h=innerHeight,sp=(p,q)=>tmo.style.setProperty(p,q);
 sp('--x',x+'px');sp('--y',y+'px');sp('--d',2*Math.ceil(Math.hypot(Math.max(x,w-x),Math.max(y,h-y)))+'px');
 tmo.dataset.k=k;tmo.dir=a?'rtl':'ltr';tmZ(k=='in');
 tmo.querySelector('.tmo-t').textContent=k=='in'?(a?'وضع التدريب':'Training Mode'):(a?'الوضع العادي':'Normal Mode');
 tmo.querySelector('.tmo-s').textContent=k=='in'?(a?'الوضع التعليمي مفعّل':'Educational mode is on'):(a?'العودة إلى الوضع القياسي':'Back to the standard kit');
 let f=0,t2;const flip=()=>{if(f)return;f=1;TM=!TM;LS('m86m',TM?'t':'n');tmS();document.dispatchEvent(new CustomEvent('m86:mode',{detail:{training:TM}}))},t1=setTimeout(flip,620),
 end=()=>{clearTimeout(t1);clearTimeout(t2);tmd.removeEventListener('animationend',end);flip();tmo.classList.remove('go');tmb=0;if(TM){tmLg=LG;tmG()}};
 tmo.classList.remove('go');void tmo.offsetWidth;tmo.classList.add('go');tmd.addEventListener('animationend',end);t2=setTimeout(end,2400)};
g('tq1').onclick=()=>g('tlg').click();
g('tq2').onclick=()=>g('tfz').click();
g('tq3').onclick=()=>{g('tsn').click();tmX()};
function tmX(){const a=LG=='ar',s=(e,t)=>{e.title=t;e.setAttribute('aria-label',t)};
 s(g('tq1'),a?'English':'العربية');s(g('tq2'),(a?'حجم الخط ':'Text size ')+g('tfr').value+'%');s(g('tq3'),sn?(a?'الصوت يعمل':'Sound on'):(a?'الصوت صامت':'Sound muted'));g('tq3').innerHTML=sn?IV:IX;g('tq1').innerHTML=IT;g('tq2').innerHTML=FZ(g('tfr').value);
 g('tklv').lastElementChild.textContent=a?'المستويات':'Levels';g('tklv').setAttribute('aria-label',a?'المستويات':'Levels');g('tmv').innerHTML=TV?tmI(a):Array.from({length:10},(_,i)=>{const n=i+1,o=n<=TO;return '<button type=button class="lv'+(o?' cur':'')+'" data-n='+n+(o?'':' disabled')+'><span class=n>'+n+'</span><span class=tx><b>'+(a?'المستوى ':'Level ')+n+'</b><i>'+(o?(n<TO?(a?'مكتمل':'Done'):(a?'ابدأ من هنا':'Start here')):(a?'مقفل':'Locked'))+'</i></span><span class=st>'+(o?(n<TO?'\u2713':'\u25B6'):'<svg class="ic" viewBox="0 0 24 24" aria-hidden="true"><rect x="5" y="10.5" width="14" height="10" rx="2.5"/><path d="M8.5 10.5V8a3.5 3.5 0 0 1 7 0v2.5"/><circle class="lf" cx="12" cy="15.5" r="1.3"/></svg>')+'</span></button>'}).join('');if(TM&&!tmb&&tmLg!=LG){tmLg=LG;PL?tmSt():tmG()}}
const TG={en:"Hi! I'm TKE Bot. Open the levels menu (\u2630) and pick the level that suits you. I'll help you step by step.",ar:'أهلاً! أنا TKE Bot. افتح قائمة المستويات (\u2630) واختر المستوى المناسب لك، وسأساعدك خطوة بخطوة.'};
/* welcome: the menu button (or the level list, once the menu is open) glows orange until a level is chosen */
function tmWg(){const w=!!tmW&&TM;mn.classList.toggle('tkw',w&&mp.hidden);g('tmv').classList.toggle('tkw',w&&!mp.hidden)}
function tmG(){g('tmw').classList.remove('fin');tmW=TV?0:1;tmWg();tmSay(TG[LG=='ar'?'ar':'en'])}
function tmSay(s,cb,f){clearInterval(tmY);tmTy=1;const t=g('tmt'),r=document.querySelector('.tmr'),c=Array.from(s);let i=f||0;t.textContent=c.slice(0,i).join('');t.classList.add('ty');r.classList.add('say');tmY=setInterval(()=>{t.textContent=c.slice(0,++i).join('');t.scrollTop=t.scrollHeight;if(i>=c.length){clearInterval(tmY);tmTy=0;t.classList.remove('ty');r.classList.remove('say');cb&&cb()}},32)}
window.tkeSay=tmSay;
const LV={
1:[{k:'c',t:['The 8086 chip','شريحة 8086'],s:[['The 8086 is a 40-pin processor that runs assembly programs.','معالج 8086 شريحة بـ40 رجلاً تنفذ برامج لغة التجميع.',''],['It works with the 8279, 8255 and 8087 chips for keyboard, display and I/O.','يعمل مع الشرائح 8279 و8255 و8087 للوحة المفاتيح والعرض والإدخال والإخراج.','']]},
{k:'c',t:['Keyboard','لوحة المفاتيح'],s:[['16 hex keys (0-F) enter addresses and data.','16 مفتاحاً سداسياً (0-F) لإدخال العناوين والبيانات.','0 1 2 3 4 5 6 7 8 9 A B C D E F'],['12 function keys edit, control and run, like RESET, INS, DEL, REG, NEXT and TTY.','12 مفتاحاً وظيفياً للتحرير والتحكم والتشغيل مثل RESET وINS وDEL وREG وNEXT وTTY.','FKEYS']]},
{k:'c',t:['Main commands','أهم الأوامر'],s:[['RESET restarts the kit and shows the sign-on message.','RESET يعيد تشغيل الكيت ويعرض رسالة البداية.','RESET'],['EB / EW examine a byte / word of memory. ER examines a register.','EB وEW لفحص بايت أو كلمة من الذاكرة، وER لفحص مسجّل.','EB EW ER'],['NEXT moves to the data field, then to the next address.','NEXT ينقلك إلى حقل البيانات ثم إلى العنوان التالي.','NEXT'],['GO runs a program: GO, address, NEXT, then TTY.','GO لتشغيل برنامج: GO ثم العنوان ثم NEXT ثم TTY.','GO NEXT TTY']]},
{k:'c',t:['Display and memory','الشاشة والذاكرة'],s:[['8 seven-segment digits: 4 show the address, 4 show the data, all in hex.','8 خانات سباعية: 4 للعنوان و4 للبيانات، كلها بالنظام السداسي.','DSP'],['RAM starts at 00000. At RESET the 8086 jumps to FFFF0, the monitor ROM.','الذاكرة RAM تبدأ من 00000، وعند RESET ينتقل المعالج إلى FFFF0 وهو برنامج المراقب.','']]},
{k:'c',t:['Registers','المسجلات'],s:[['Registers are small memory cells inside the 8086. General ones: AX accumulator, BX base, CX count, DX data.','المسجلات خلايا صغيرة داخل المعالج 8086. العامة منها: AX المجمّع وBX القاعدة وCX العدّاد وDX البيانات.','r:AX r:BX r:CX r:DX 0 1 2 3'],
['Pointers and indexes: SP stack pointer, BP base pointer, SI source index, DI destination index.','المؤشرات والفهارس: SP مؤشر المكدس وBP مؤشر القاعدة وSI فهرس المصدر وDI فهرس الوجهة.','r:SP r:BP r:SI r:DI 4 5 6 7'],
['Segment registers: CS code, DS data, SS stack, ES extra.','مسجلات المقاطع: CS الشيفرة وDS البيانات وSS المكدس وES الإضافي.','r:CS r:DS r:SS r:ES 8 9 A B'],
['Also IP, the instruction pointer, and FL, the flags.','ومعها IP مؤشر التعليمات وFL الأعلام.','r:IP r:FL C D'],
['Reach a register: press RESET, then ER, then the key labelled AX (key 0).','للوصول إلى مسجل: اضغط RESET ثم ER ثم المفتاح المكتوب عليه AX وهو 0.','r:AX'],
['You are inside AX. The data digits show its 4 hex digits. The left two are AH, the high byte.','أنت الآن داخل AX. خانات البيانات تعرض أرقامه الأربعة. الخانات على اليسار هي AH وهو البايت العلوي.','r:AX dh'],
['The right two digits are AL, the low byte. BX, CX and DX split the same way.','الخانات على اليمين هي AL وهو البايت السفلي. وBX وCX وDX تنقسم بالمثل.','r:AX r:BX r:CX r:DX dl'],
['Set it directly: type 1234, then NEXT to save it in AX.','لوضع قيمة مباشرة: اكتب 1234 ثم NEXT لحفظها في AX.','r:AX'],
['Press TTY to leave. AX = 1234, with no program or memory needed.','اضغط TTY للخروج. صار AX = 1234 دون برنامج ولا ذاكرة.','r:AX']]},
{k:'e',t:['Example 1: AABB into AX','مثال 1: وضع AABB في AX'],s:[['Goal: store AABB in register AX. Write the program in memory at 400.','الهدف: خزّن القيمة AABB في المسجل AX، بكتابة برنامج في الذاكرة عند العنوان 400.','r:AX'],['Step 1: switch the kit on, then press RESET.','1) شغّل الكيت ثم اضغط RESET.','RESET'],['Step 2: press EB, then type the address 400.','2) اضغط EB ثم اكتب العنوان 400.','EB 0 4'],['Step 3: press NEXT to open the data field.','3) اضغط NEXT لفتح حقل البيانات.','NEXT'],['Step 4: type B8, then NEXT. The address moves to 00401.','4) اكتب B8 ثم NEXT فينتقل العنوان إلى 00401.','B 8 NEXT'],['Step 5: type BB, NEXT, then AA, NEXT.','5) اكتب BB ثم NEXT ثم AA ثم NEXT.','B A NEXT'],['Step 6: type CC, then NEXT. The program is stored.','6) اكتب CC ثم NEXT فيُحفظ البرنامج.','F 4 NEXT'],['Step 7: press RESET, then GO, type 400 and press NEXT.','7) اضغط RESET ثم GO ثم اكتب 400 واضغط NEXT.','RESET GO 0 4 NEXT'],['Step 8: press TTY to run. AX now holds AABB.','8) اضغط TTY للتنفيذ فيصبح AX = AABB.','TTY r:AX']]},
{k:'e',t:['Example 2: 45h into AL','مثال 2: 45h في AL'],s:[['Goal: store 45h in register AL. Write the program in memory at 600.','الهدف: خزّن القيمة 45h في المسجل AL، بكتابة برنامج في الذاكرة عند العنوان 600.','r:AX'],['Step 1: press EB, type 600, then NEXT.','1) اضغط EB واكتب 600 ثم NEXT.','EB 6 0 0 NEXT'],['Step 2: type B0, NEXT, 45, NEXT, then CC, NEXT. The program is stored.','2) اكتب B0 ثم NEXT ثم 45 ثم NEXT ثم CC ثم NEXT فيُحفظ البرنامج.','B 0 NEXT 4 5 NEXT C C NEXT'],['Step 3: press RESET, GO, type 600, then NEXT.','3) اضغط RESET ثم GO ثم اكتب 600 ثم NEXT.','RESET GO 6 0 0 NEXT'],['Step 4: press TTY to run. AL = 45, the low half of AX.','4) اضغط TTY للتنفيذ فيصبح AL = 45.','TTY r:AX']]},
{k:'e',t:['Example 3: 6Ch into AH','مثال 3: 6Ch في AH'],s:[['Goal: store 6Ch in register AH. Write the program in memory at 500.','الهدف: خزّن القيمة 6Ch في المسجل AH، بكتابة برنامج في الذاكرة عند العنوان 500.','r:AX'],['Step 1: press EB, type 500, NEXT, then B4, NEXT.','1) اضغط EB واكتب 500 ثم NEXT ثم B4 ثم NEXT.','EB 5 0 0 NEXT B 4 NEXT'],['Step 2: type 6C, NEXT, then CC, NEXT. The program is stored.','2) اكتب 6C ثم NEXT ثم CC ثم NEXT فيُحفظ البرنامج.','6 C NEXT C C NEXT'],['Step 3: press RESET, GO, type 500, NEXT, then TTY. AH = 6C.','3) اضغط RESET ثم GO ثم اكتب 500 ثم NEXT ثم TTY فيصبح AH = 6C.','RESET GO 5 0 0 NEXT TTY r:AX']]},
{k:'x',t:['Exercise 1: AX values','تمرين 1: قيم AX'],s:[['Load DFA1 into AX, then run the program.','ضع DFA1 في AX ثم نفّذ البرنامج.','r:AX','Hint: B8 A1 DF CC.','تلميح: B8 A1 DF CC.','AX=DFA1'],['Now load 869B into AX the same way.','الآن ضع 869B في AX بنفس الطريقة.','r:AX','Hint: B8 9B 86 CC.','تلميح: B8 9B 86 CC.','AX=869B']]},
{k:'x',t:['Exercise 2: AL and AH','تمرين 2: AL وAH'],s:[['Load 7B into AL and 8F into AH, then run it.','ضع 7B في AL و8F في AH ثم نفّذه.','r:AX','Hint: B0 7B, B4 8F, then CC.','تلميح: B0 7B وB4 8F ثم CC.','AX=8F7B']]},
{k:'q',t:['Final test','الاختبار النهائي'],q:[['The kit has 16 hex keys and 12 function keys.','يحتوي الكيت على 16 مفتاحاً سداسياً و12 مفتاحاً وظيفياً.',true],['Registers are small, fast storage cells inside the CPU that temporarily hold data and addresses.','المسجلات (Registers) خلايا تخزين صغيرة وسريعة داخل المعالج تحتفظ مؤقتاً بالبيانات والعناوين.',true],['B8 BB AA loads AABB into AX.','الأمر B8 BB AA يضع AABB في AX.',true]]}],
2:[{k:'c',t:['16-bit and 8-bit','16 بت و8 بت'],s:[['Each 16-bit register splits into two 8-bit halves: AX = AH + AL.','كل مسجل 16 بت ينقسم إلى نصفين 8 بت: AX = AH + AL.','r:AX'],['The same for BX, CX and DX: the general-purpose registers.','وكذلك BX وCX وDX وهي المسجلات العامة.','r:BX r:CX r:DX']]},
{k:'c',t:['Register roles','وظائف المسجلات'],s:[['AX accumulator, BX base, CX count, DX data.','AX المجمّع وBX القاعدة وCX العدّاد وDX البيانات.','r:AX r:BX r:CX r:DX'],['SP, BP, SI, DI are pointers and indexes. IP points to the next instruction.','SP وBP وSI وDI مؤشرات وفهارس، وIP يشير للتعليمة التالية.','r:SP r:BP r:SI r:DI r:IP'],['CS, DS, SS, ES hold segment addresses.','CS وDS وSS وES تحمل عناوين المقاطع.','r:CS r:DS r:SS r:ES']]},
{k:'c',t:['Memory order','ترتيب الذاكرة'],s:[['A 16-bit value is stored low byte first: AB at 500 and 7D at 501 make 7DAB.','القيمة 16 بت تُخزّن بالبايت الأدنى أولاً: AB عند 500 و7D عند 501 تعطي 7DAB.','']]},
{k:'e',t:['Example 1: memory to CX to AX','مثال 1: من الذاكرة إلى CX ثم AX'],s:[['Goal: copy memory 500-501 into CX, then into AX. Data: AB at 500, 7D at 501.','الهدف: نسخ الذاكرة 500-501 إلى CX ثم AX. البيانات: AB عند 500 و7D عند 501.','r:CX r:AX'],['Step 1: press EB, type 500, press NEXT.','1) اضغط EB واكتب 500 ثم NEXT.','EB 0 5 NEXT'],['Step 2: type AB, NEXT, then 7D, NEXT. The data is stored.','2) اكتب AB ثم NEXT ثم 7D ثم NEXT فتُحفظ البيانات.','A B 7 D NEXT'],['Step 3: press RESET, then EB and type 700 to write the program.','3) اضغط RESET ثم EB واكتب 700 لكتابة البرنامج.','RESET EB 7 0'],['Step 4: NEXT, then 8B 0E 00 05 (MOV CX,[0500]), 8B C1 (MOV AX,CX), CC (INT 3), each followed by NEXT.','4) NEXT ثم 8B 0E 00 05 (MOV CX,[0500]) ثم 8B C1 (MOV AX,CX) ثم CC (INT 3) مع NEXT بعد كل بايت.','NEXT 8 B 0 E 5 C 1 F 4'],['Step 5: press RESET, GO, type 700, NEXT, then TTY.','5) اضغط RESET ثم GO ثم اكتب 700 ثم NEXT ثم TTY.','RESET GO 7 0 NEXT TTY'],['Result: CX and AX both hold 7DAB.','النتيجة: CX وAX يحملان 7DAB.','r:CX r:AX']]},
{k:'e',t:['Example 2: DL and DH','مثال 2: DL وDH'],s:[['Goal: DL = 8C and DH = [600] = AF, so DX = AF8C.','الهدف: DL = 8C وDH = [600] = AF فيصبح DX = AF8C.','r:DX'],['Step 1: first store AF at 600: EB, 600, NEXT, AF, NEXT.','1) خزّن AF أولاً عند 600: EB ثم 600 ثم NEXT ثم AF ثم NEXT.','r:DX'],['Step 2: press RESET, EB, 800, NEXT, then enter B2 8C (MOV DL,8C), each byte then NEXT.','2) اضغط RESET ثم EB و800 وNEXT، ثم أدخل B2 8C (MOV DL,8C) مع NEXT بعد كل بايت.',''],['Step 3: enter 8A 36 00 06 (MOV DH,[0600]), each byte then NEXT.','3) أدخل 8A 36 00 06 (MOV DH,[0600]) مع NEXT بعد كل بايت.',''],['Step 4: enter 8B C2 (MOV AX,DX) then CC, each byte then NEXT.','4) أدخل 8B C2 (MOV AX,DX) ثم CC مع NEXT بعد كل بايت.',''],['Step 5: run with RESET, GO, 800, NEXT, TTY. AX shows AF8C.','5) نفّذ بـ RESET ثم GO ثم 800 ثم NEXT ثم TTY فيظهر AX = AF8C.','r:AX']]},
{k:'e',t:['Example 3: BX to memory','مثال 3: من BX إلى الذاكرة'],s:[['Goal: BX = 943E, then store BX at 650.','الهدف: BX = 943E ثم تخزينه عند 650.','r:BX'],['Step 1: press EB, 400, NEXT, then enter BB 3E 94 (MOV BX,943E), each byte then NEXT.','1) اضغط EB و400 وNEXT، ثم أدخل BB 3E 94 (MOV BX,943E) مع NEXT بعد كل بايت.','r:BX'],['Step 2: enter 89 1E 50 06 (MOV [0650],BX) then CC, each byte then NEXT.','2) أدخل 89 1E 50 06 (MOV [0650],BX) ثم CC مع NEXT بعد كل بايت.','r:BX'],['Step 3: run with RESET, GO, 400, NEXT, TTY.','3) نفّذ بـ RESET ثم GO ثم 400 ثم NEXT ثم TTY.','r:BX'],['Step 4: check memory: EB, 650, NEXT. 3E is at 650 and 94 at 651.','4) افحص الذاكرة: EB ثم 650 ثم NEXT: ستجد 3E عند 650 و94 عند 651.','r:BX']]},
{k:'x',t:['Exercise: DX to AX','تمرين: DX إلى AX'],s:[['Make AX show 3C5A: put 5A in DL, 3C in DH, then copy DX to AX.','اجعل AX يعرض 3C5A: ضع 5A في DL و3C في DH ثم انسخ DX إلى AX.','r:DX r:AX','Hint: B2 5A, B6 3C, 8B C2, then CC.','تلميح: B2 5A وB6 3C و8B C2 ثم CC.','AX=3C5A']]},
{k:'q',t:['Final test','الاختبار النهائي'],q:[['AX is made of AH (high) and AL (low).','AX يتكوّن من AH (العلوي) وAL (السفلي).',true],['MOV AX,CX copies AX into CX.','الأمر MOV AX,CX ينسخ AX إلى CX.',false],['A 16-bit value is stored with its low byte at the lower address.','القيمة 16 بت تُخزّن بالبايت الأدنى في العنوان الأقل.',true]]}]};
function tmI(a){const L=LV[TV],kn={c:a?'مفهوم':'Concept',e:a?'مثال':'Example',x:a?'تمرين':'Exercise',q:a?'اختبار':'Test'};
 return '<button type=button class=lb>'+(a?'\u203A ':'\u2039 ')+(a?'المستوى ':'Level ')+TV+'</button>'+(L?L.map((m,i)=>'<button type=button class="lv li kd-'+m.k+(DN[TV+'.'+i]?' dn':'')+'" data-i='+i+'><span class=n>'+(i+1)+'</span><span class=tx><b>'+m.t[+a]+'</b><i>'+kn[m.k]+'</i></span><span class=st>\u25B6</span></button>').join(''):'<p class=tmz>'+(a?'المحتوى قريباً':'Coming soon')+'</p>')}
function tmAp(){document.querySelectorAll('.tkhl').forEach(e=>e.classList.remove('tkhl'));void document.body.offsetWidth;const m={EB:0,ER:1,GO:2,ST:3,EW:7,TTY:'.'};HLT.forEach(t=>{const e=t=='dh'?[...g('dsp').children].slice(4,6):t=='dl'?[...g('dsp').children].slice(6,8):t=='DSP'?[g('dsp')]:t=='FKEYS'?[...document.querySelectorAll('#keys .b')]:t.startsWith('r:')?[[...g('regs').children].find(x=>x.textContent.trim().split(' ')[0]==t.slice(2))]:[document.querySelector('#keys [data-k="'+(t in m?m[t]:/^[0-9A-F]$/.test(t)?parseInt(t,16):t)+'"]')];e.forEach(x=>x&&x.classList.add('tkhl'))})}
function tmHL(a){HLT=a;tmAp()}
new MutationObserver(tmAp).observe(g('regs'),{childList:true});
function tmEnd(){PL=0;tmW=0;HLT=[];tmAp();tmWg();g('tmw').classList.remove('ls','hx','fin','xd','qz');g('tkn').classList.remove('tkg')}
const SQ={'1.4.4':'RESET ER 0','1.4.7':'1 2 3 4 NEXT','1.4.8':'TTY','1.5.1':'RESET','1.5.2':'EB 4 0 0','1.5.3':'NEXT','1.5.4':'B 8 NEXT','1.5.5':'B B NEXT A A NEXT','1.5.6':'C C NEXT','1.5.7':'RESET GO 4 0 0 NEXT','1.5.8':'TTY','1.6.1':'EB 6 0 0 NEXT','1.6.2':'B 0 NEXT 4 5 NEXT C C NEXT','1.6.3':'RESET GO 6 0 0 NEXT','1.6.4':'TTY','1.7.1':'EB 5 0 0 NEXT B 4 NEXT','1.7.2':'6 C NEXT C C NEXT','1.7.3':'RESET GO 5 0 0 NEXT TTY','2.3.1':'EB 5 0 0 NEXT','2.3.2':'A B NEXT 7 D NEXT','2.3.3':'RESET EB 7 0 0','2.3.4':'NEXT 8 B NEXT 0 E NEXT 0 0 NEXT 0 5 NEXT 8 B NEXT C 1 NEXT C C NEXT','2.3.5':'RESET GO 7 0 0 NEXT TTY','2.4.1':'EB 6 0 0 NEXT A F NEXT','2.4.2':'RESET EB 8 0 0 NEXT B 2 NEXT 8 C NEXT','2.4.3':'8 A NEXT 3 6 NEXT 0 0 NEXT 0 6 NEXT','2.4.4':'8 B NEXT C 2 NEXT C C NEXT','2.4.5':'RESET GO 8 0 0 NEXT TTY','2.5.1':'EB 4 0 0 NEXT B B NEXT 3 E NEXT 9 4 NEXT','2.5.2':'8 9 NEXT 1 E NEXT 5 0 NEXT 0 6 NEXT C C NEXT','2.5.3':'RESET GO 4 0 0 NEXT TTY','2.5.4':'EB 6 5 0 NEXT'};
function tmKv(t){const m={EB:0,ER:1,GO:2,ST:3,EW:7,TTY:'.'};return String(t in m?m[t]:/^[0-9A-F]$/.test(t)?parseInt(t,16):t)}
function tmKp(v){const p=PL;if(!p||v==null)return;p.kp=1;if(p.ck)setTimeout(()=>tmGc(p),150);if(!p.sq||tmKv(p.sq[p.n])!==String(v))return;p.n++;const i0=p.i;if(p.n<p.sq.length)tmHL(p.rs.concat(p.sq[p.n]));else{tmHL(p.rs);p.sd=1;p.dd[p.i]=1;tmUl(p);if(p.i<p.it.s.length-1)setTimeout(()=>{if(PL===p&&p.i===i0&&p.i<p.it.s.length-1){p.i++;tmSt()}},450);else tmChk(p)}}
g('keys').addEventListener('click',e=>{const b=e.target.closest('button');if(b)tmKp(b.dataset.k)});
document.addEventListener('keydown',e=>{if(/^(TEXTAREA|INPUT)$/.test(e.target.tagName)||e.ctrlKey||e.metaKey||e.altKey)return;const c=e.key;tmKp(/^[0-9a-f]$/i.test(c)?String(parseInt(c,16)):{Enter:'NEXT',Backspace:'BS','-':'PRV','.':'.',Escape:'RESET',g:'2',G:'2',Insert:'INS','+':'INS',Delete:'DEL',v:'VCT',V:'VCT',F1:'F1',F2:'F2',F3:'F3'}[c])});
function tmP(it,lv){tmW=0;tmWg();PL={it:it,i:0,ok:0,lk:0,dd:{},lv:lv==null?TV:lv};g('tmw').classList.add('ls');(LG=='ar'&&PL.lv==1&&it.k=='c'&&it.t[0]=='Registers'?tmLn():tmSt());g('tmw').scrollIntoView({behavior:'smooth',block:'center'})}
/* Registers concept in Arabic: suggest English first (exact names), with an optional direct switch */
function tkLn(on){const d=g('tkln');if(d)d.classList.toggle('on',!!on);g('tmw').classList.toggle('ln',!!on)}
function tmLn(){const p=PL;p.ln=1;g('tmw').classList.remove('fin','hx','xd','qz');tmHL([]);
 tmSay('يُنصح باستخدام اللغة الإنجليزية لدقة الأسماء والفهم.\nهل تريد التحويل الآن؟');
 g('tkln').innerHTML='<button type=button id=tkle>'+IT+'English</button><button type=button id=tklk>متابعة بالعربية</button>';tkLn(1);
 g('tkc').textContent='';g('tkb').textContent='\u203A';g('tkn').textContent='\u2039';g('tkb').disabled=true;g('tkhint').disabled=true;g('tkn').disabled=false;g('tkn').classList.remove('tkg');
 g('tkle').onclick=()=>{if(PL!==p||!p.ln)return;p.ln=0;tkLn(0);g('tlg').click()};
 g('tklk').onclick=()=>{if(PL!==p||!p.ln)return;tmSt()}}
function tmSt(){tkLn(0);PL.ln=0;const a=LG=='ar'?1:0,p=PL,q=p.it.k=='q',z=q?p.it.q:p.it.s,s=z[p.i],L=LV[p.lv],j=L.indexOf(p.it),nx=!q&&!!L[j+1],ls=p.i==z.length-1;
 if(p.ls!==p.i){p.ls=p.i;p.n=0;p.dn=0;p.h=0;p.kp=0;p.sd=!!p.dd[p.i]}
 g('tmw').classList.remove('fin');
 const hn=p.it.k=='x'?(s[3+a]||''):'',hb=g('tkhint'),m=p.it.k=='x'&&/^(\w+)=([0-9A-F]+)$/i.exec(s[5]||'');p.ck=m?[m[1].toUpperCase(),parseInt(m[2],16),m[2].toUpperCase()]:0;
 g('tmw').classList.toggle('hx',p.it.k=='x');hb.innerHTML='<svg class="ic" viewBox="0 0 24 24" aria-hidden="true"><path d="M9.5 18.5h5M10.3 21.5h3.4"/><path class="bf" d="M12 2.8a6.2 6.2 0 0 0-3.7 11.2c.7.6 1.2 1.3 1.2 2.2v.3h5v-.3c0-.9.5-1.6 1.2-2.2A6.2 6.2 0 0 0 12 2.8z"/></svg>'+(a?'تلميح':'Hint');hb.disabled=true;
 tmSay(p.h&&hn?s[a]+'\n'+hn:s[a],()=>{tmChk(p);if(PL===p)hb.disabled=!hn||!!p.h||!!p.sd});
 const tk=q?[]:(s[2]||'').split(' ').filter(Boolean),sq=(p.it.k=='e'||p.it.k=='c')?SQ[p.lv+'.'+j+'.'+p.i]:0;p.sq=sq?sq.split(' '):0;p.rs=tk.filter(t=>t.startsWith('r:'));tmHL(sq?p.rs.concat(p.n<p.sq.length?[p.sq[p.n]]:[]):tk);g('tkc').textContent=(p.i+1)+'/'+z.length;
 g('tmw').classList.toggle('qz',q);g('tkp').textContent='\u2717';g('tkn').textContent=q?'\u2713':(a?'\u2039':'\u203A');g('tkp').disabled=false;const kb=g('tkb');kb.textContent=a?'\u203A':'\u2039';kb.disabled=p.i==0;kb.title=a?'خطوة للخلف':'Back one step';kb.setAttribute('aria-label',kb.title);tmUl(p);if(p.it.k!='x')g('tkn').classList.toggle('tkg',!!(p.dn&&ls&&nx))}
/* next stays locked while the step's required action (key sequence / exercise result) is not done */
function tmUl(p){if(PL!==p)return;tmGo(p);const q=p.it.k=='q',L=LV[p.lv],ls=p.i==(q?p.it.q:p.it.s).length-1,nx=!!L[L.indexOf(p.it)+1];g('tkn').disabled=!q&&(((p.sq||p.ck)&&!p.sd)||(ls&&!nx))}
/* exercise check: after a key press, look at the kit's registers for the requested result */
function tmGc(p){if(!p||PL!==p||!p.ck||p.sd||!p.kp)return;const c=p.ck,k=RN.indexOf(c[0]);if(k<0||rget(k)!==c[1])return;p.sd=1;p.dd[p.i]=1;g('tkhint').disabled=true;tmUl(p);const a=LG=='ar'?1:0,ls=p.i==p.it.s.length-1;tmSay((a?'صحيح! ':'Correct! ')+c[0]+' = '+c[2]+'.',()=>tmChk(p))}
new MutationObserver(()=>tmGc(PL)).observe(g('regs'),{childList:true});
/* exercise hint: appears only when the button is pressed */
g('tkhint').onclick=()=>{const p=PL;if(!p||p.it.k!='x'||p.h||tmTy)return;const a=LG=='ar'?1:0,s=p.it.s[p.i],h=s[3+a];if(!h)return;p.h=1;g('tkhint').disabled=true;tmSay(s[a]+'\n'+h,null,Array.from(s[a]).length)};
/* end of a concept / example: tiny check animation, orange in the list, next button glows */
function tmChk(p){if(PL!==p||p.dn||tmTy||p.it.k=='q'||p.i!=p.it.s.length-1||(p.sq&&p.n<p.sq.length)||(p.ck&&!p.sd))return;tmDone(p)}
function tmDone(p){p.dn=1;const k=p.it.k,L=LV[p.lv],j=L.indexOf(p.it);if(L[j+1]&&k!='x')g('tkn').classList.add('tkg');
 if(k=='c'||k=='e'){const d=g('tkd');d.classList.remove('go');void d.offsetWidth;d.classList.add('go')}
 const y=p.lv+'.'+j;if(!DN[y]){DN[y]=1;LS('m86d',JSON.stringify(DN));tmX()}}
function tmA(v){const p=PL,a=LG=='ar'?1:0,r=p.it.q[p.i][2],ok=r===v;p.lk=1;if(ok)p.ok++;tmSay(ok?(a?'صحيح!':'Correct!'):(a?'ليس تماماً. الإجابة: '+(r?'صح':'خطأ'):'Not quite. The answer is '+(r?'True':'False')+'.'));
 setTimeout(()=>{if(PL!==p)return;p.lk=0;if(++p.i<p.it.q.length)tmSt();else tmPass(p)},1800)}
function tmPass(p){const a=LG=='ar'?1:0,n=TV;DN[p.lv+'.'+LV[p.lv].indexOf(p.it)]=1;LS('m86d',JSON.stringify(DN));TO=Math.max(TO,n+1);LS('m86p',TO);thZ(true);tmEnd();TV=0;tmSay(a?'أحسنت! نتيجتك '+p.ok+'/'+p.it.q.length+'. أنهيت المستوى '+n+' وفُتح المستوى التالي.':'Well done! Score '+p.ok+'/'+p.it.q.length+'. Level '+n+' done, next level unlocked.');g('tmw').classList.add('fin');tmX()}
/* Levels button: opens the level list so a new level can be chosen */
g('tklv').onclick=e=>{e.stopPropagation();g('tmw').classList.remove('fin');TV=0;tmW=1;tmX();mo(true)};
g('tkp').onclick=()=>{const p=PL;if(!p||p.lk)return;if(p.it.k=='q')return tmA(false)};
g('tkb').onclick=()=>{const p=PL;if(!p||p.lk||p.it.k=='q')return;if(p.i>0){p.i--;tmSt()}};
g('tkn').onclick=()=>{const p=PL;if(!p||p.lk)return;if(p.ln)return tmSt();if(p.it.k=='q')return tmA(true);if(p.i<p.it.s.length-1){p.i++;tmSt()}else{const L=LV[p.lv],n=L[L.indexOf(p.it)+1];if(n)tmP(n,p.lv)}};
g('tmv').onclick=e=>{const b=e.target.closest('button');if(!b||b.disabled)return;tmW=0;tmWg();if(b.classList.contains('lb')){TV=0;setTimeout(tmX,0)}else if(b.classList.contains('li')){mo(false);tmP(LV[TV][+b.dataset.i])}else{TV=+b.dataset.n;setTimeout(tmX,0)}};
function thZ(day){if(!sn)return;try{ac=ac||new(window.AudioContext||window.webkitAudioContext)();if(ac.state==='suspended')ac.resume();const t=ac.currentTime,n=(f,s,d,ty,vl)=>{const o=ac.createOscillator(),v=ac.createGain();o.type=ty;o.frequency.value=f;v.gain.setValueAtTime(.0001,t+s);v.gain.linearRampToValueAtTime(vl,t+s+.015);v.gain.exponentialRampToValueAtTime(.0001,t+s+d);o.connect(v);v.connect(ac.destination);o.start(t+s);o.stop(t+s+d+.02)};
 (day?[784,988,1319,1568]:[587,466,349,262]).forEach((f,i)=>{n(f,i*.075,.35,day?'sine':'triangle',day?.06:.07);if(day)n(f*2,i*.075,.18,'sine',.02)})}catch(e){}}
function lgZ(){if(!sn)return;try{ac=ac||new(window.AudioContext||window.webkitAudioContext)();if(ac.state==='suspended')ac.resume();const t=ac.currentTime,ar=LG=='ar',n=(a,b,s,d,ty,vl)=>{const o=ac.createOscillator(),v=ac.createGain();o.type=ty;o.frequency.setValueAtTime(a,t+s);o.frequency.exponentialRampToValueAtTime(b,t+s+d);v.gain.setValueAtTime(.0001,t+s);v.gain.linearRampToValueAtTime(vl,t+s+.02);v.gain.exponentialRampToValueAtTime(.0001,t+s+d);o.connect(v);v.connect(ac.destination);o.start(t+s);o.stop(t+s+d+.02)};
 if(ar){n(1100,300,0,.32,'triangle',.05);[784,587].forEach((f,i)=>n(f,f,.16+i*.1,.28,'sine',.07))}else{n(300,1100,0,.32,'triangle',.05);[587,784].forEach((f,i)=>n(f,f,.16+i*.1,.28,'sine',.07))}}catch(e){}}
function tmZ(up){if(!sn)return;try{ac=ac||new(window.AudioContext||window.webkitAudioContext)();if(ac.state==='suspended')ac.resume();const t=ac.currentTime,n=(a,b,s,d,ty,vl)=>{const o=ac.createOscillator(),v=ac.createGain();o.type=ty;o.frequency.setValueAtTime(a,t+s);o.frequency.exponentialRampToValueAtTime(b,t+s+d);v.gain.setValueAtTime(.0001,t+s);v.gain.linearRampToValueAtTime(vl,t+s+.03);v.gain.exponentialRampToValueAtTime(.0001,t+s+d);o.connect(v);v.connect(ac.destination);o.start(t+s);o.stop(t+s+d+.02)};
 up?n(200,900,0,.55,'triangle',.06):n(900,200,0,.55,'triangle',.06);(up?[659,880,1319]:[1319,880,523]).forEach((q,i)=>n(q,q,.5+i*.12,.32,'sine',.07))}catch(e){}}
/* after an exercise is solved: hint button is replaced by a button to the next item */
function tmGo(p){let on=0;if(p.it.k=='x'){const L=LV[p.lv],n=L[L.indexOf(p.it)+1],a=LG=='ar',ls=p.i==p.it.s.length-1;on=!!p.sd&&(!ls||!!n);g('tkn').classList.toggle('tkg',!!on)}g('tmw').classList.toggle('xd',!!on)}
/* soft click: menu button, levels button, and the levels list */
function tmK(){if(!sn)return;try{ac=ac||new(window.AudioContext||window.webkitAudioContext)();if(ac.state==='suspended')ac.resume();const t=ac.currentTime,o=ac.createOscillator(),v=ac.createGain();o.type='sine';o.frequency.setValueAtTime(620,t);o.frequency.exponentialRampToValueAtTime(980,t+.06);v.gain.setValueAtTime(.0001,t);v.gain.linearRampToValueAtTime(.07,t+.006);v.gain.exponentialRampToValueAtTime(.0001,t+.11);o.connect(v);v.connect(ac.destination);o.start(t);o.stop(t+.13)}catch(e){}}
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
