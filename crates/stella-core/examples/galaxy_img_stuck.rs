//! What is img0's force STUCK on after its 1 forcing? Dump the raw
//! final_ray's KAM focus spine + look for an omitted strict-op atom
//! (add/mul/div/neg/eq/lt/isnil — the §58/§60 prim_stars punt) in head
//! position vs a genuinely lazily-non-normalising objective term.
use stella_core::galaxy::{self, eval_forced, readback_ray};
use stella_core::galaxy_decode::{decode, pretty};
use stella_core::term::{self, TermData, TermId};
fn cst(n:&str)->TermId{term::mk_app_str(n,vec![])}
fn ap(f:TermId,x:TermId)->TermId{term::mk_app_str("a",vec![f,x])}
fn as_cons(t:TermId)->Option<(TermId,TermId)>{let TermData::App(s,a)=term::get(t) else{return None};if s.name.as_str()!="a"||a.len()!=2{return None}let TermData::App(s2,a2)=term::get(a[0]) else{return None};if s2.name.as_str()!="a"||a2.len()!=2{return None}match term::get(a2[0]){TermData::App(s3,a3) if a3.is_empty()&&s3.name.as_str()=="cons"=>Some((a2[1],a[1])),_=>None}}
fn hd(t:TermId)->String{match term::get(t){TermData::Var(_)=>"<var>".into(),TermData::App(s,a)=>format!("{}/{}",s.name.as_str(),a.len())}}
// leftmost spine of an `a`-application: a(a(a(H,_),_),_) → H + arg count
fn spine(mut t:TermId)->(TermId,usize){let mut n=0;loop{match term::get(t){TermData::App(s,a) if s.name.as_str()=="a"&&a.len()==2=>{t=a[0];n+=1;}_=>return (t,n)}}}
fn tree(t:TermId,d:usize,md:usize,o:&mut String){let p="  ".repeat(d);if d>=md{o.push_str(&format!("{p}{} …\n",hd(t)));return}match term::get(t){TermData::Var(_)=>o.push_str(&format!("{p}<var>\n")),TermData::App(s,a)=>{o.push_str(&format!("{p}{}/{}\n",s.name.as_str(),a.len()));for(i,&c)in a.iter().enumerate(){if i>=6{o.push_str(&format!("{p}  …(+{})\n",a.len()-6));break}tree(c,d+1,md,o);}}}}
fn main(){
 let src=std::fs::read_to_string("/Users/ember/dev/embershot/src/galaxy.txt").unwrap();
 let g=galaxy::parse(&src).unwrap(); let phi=galaxy::constellation(&g);
 let entry=galaxy::ref_atom(g.entry);
 let click=ap(ap(cst("cons"),stella_core::binarith::nat(0)),stella_core::binarith::nat(0));
 let mut t=ap(ap(entry,cst("nil")),click);
 for (_l,th) in [("triple",false),("after-flag",false),("after-state",true),("data",true)]{
   let f=eval_forced(&phi,t,2_000_000,100_000);
   let rb=readback_ray(f.final_ray.unwrap_or(f.value));
   let (h,tl)=as_cons(rb).unwrap(); t=if th{h}else{tl};
 }
 println!("img0 head={}",hd(t));
 let f=eval_forced(&phi,t,4_000_000,4); // stuck after ~1 forcing
 println!("after force: steps={} arith={} forc={} fullyRed={}",f.steps,f.arith_ops,f.forcings,f.fully_reduced);
 let raw=f.final_ray.unwrap_or(f.value);
 println!("RAW final_ray head={}",hd(raw));
 // raw = +P(st(M,π)); dig M and π
 if let TermData::App(s,a)=term::get(raw){ if a.len()==1 {
   if let TermData::App(s2,a2)=term::get(a[0]){ println!("  ray={}/{} inner={}/{}",s.name.as_str(),a.len(),s2.name.as_str(),a2.len());
     if s2.name.as_str()=="st"&&a2.len()==2{
       let (m,pi)=(a2[0],a2[1]);
       let (sh,sn)=spine(m);
       println!("  FOCUS M head={} | leftmost-spine head={} applied-to {} args",hd(m),hd(sh),sn);
       println!("  STACK π head={}",hd(pi));
       let strict=["add","mul","div","neg","eq","lt","isnil","sub","mod","car","cdr"];
       let shn=if let TermData::App(ss,_)=term::get(sh){ss.name.as_str().to_string()}else{"<var>".into()};
       println!("  ⇒ spine head {:?} {}", shn,
         if strict.contains(&shn.as_str()){"IS an omitted/strict prim → §58/§60 faithfulness gap"}else{"is NOT a strict prim → lazily-non-normalising objective term"});
       let mut o=String::new(); tree(m,0,8,&mut o); println!("FOCUS M tree:\n{o}");
       let mut o2=String::new(); tree(pi,0,5,&mut o2); println!("STACK π tree:\n{o2}");
     }}}}
 println!("decoded readback: {}",pretty(&decode(readback_ray(raw))));
}
