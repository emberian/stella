//! Disambiguator: does img0's force grow in FORCINGS (Θ(N) strict-driven →
//! KA2-on-forcing-layers) or does eval_forced spin non-productively when
//! blocked (orchestration artifact)? Ladder max_forcings with ample fuel.
use stella_core::galaxy::{self, eval_forced, readback_ray};
use stella_core::galaxy_decode::{decode, pretty};
use stella_core::term::{self, TermData, TermId};
fn cst(n:&str)->TermId{term::mk_app_str(n,vec![])}
fn ap(f:TermId,x:TermId)->TermId{term::mk_app_str("a",vec![f,x])}
fn as_cons(t:TermId)->Option<(TermId,TermId)>{let TermData::App(s,a)=term::get(t) else{return None};if s.name.as_str()!="a"||a.len()!=2{return None}let TermData::App(s2,a2)=term::get(a[0]) else{return None};if s2.name.as_str()!="a"||a2.len()!=2{return None}match term::get(a2[0]){TermData::App(s3,a3) if a3.is_empty()&&s3.name.as_str()=="cons"=>Some((a2[1],a[1])),_=>None}}
fn main(){
 let src=std::fs::read_to_string("/Users/ember/dev/embershot/src/galaxy.txt").unwrap();
 let g=galaxy::parse(&src).unwrap(); let phi=galaxy::constellation(&g);
 let entry=galaxy::ref_atom(g.entry);
 let click=ap(ap(cst("cons"),stella_core::binarith::nat(0)),stella_core::binarith::nat(0));
 let mut t=ap(ap(entry,cst("nil")),click);
 // triple→tail, after-flag→tail, after-state→HEAD(data), data→HEAD(img0)
 for (lbl,take_head) in [("triple",false),("after-flag",false),("after-state",true),("data",true)]{
   let f=eval_forced(&phi,t,2_000_000,100_000);
   let rb=readback_ray(f.final_ray.unwrap_or(f.value));
   let (h,tl)=as_cons(rb).unwrap_or_else(||panic!("{lbl} not cons"));
   t = if take_head { h } else { tl };
 }
 println!("img0 head={:?}", match term::get(t){TermData::App(s,a)=>format!("{}/{}",s.name.as_str(),a.len()),_=>"var".into()});
 for &mf in &[1usize,2,4,8,12,16,20,24,28,32,40,48,56,64,80,96,128,192,256]{
   let t0=std::time::Instant::now();
   let f=eval_forced(&phi,t,8_000_000,mf);
   let rb=readback_ray(f.final_ray.unwrap_or(f.value));
   println!("mf={mf:6} steps={:8} arith={:5} forc={:5} fullyRed={} secs={:.2} dec={}",
     f.steps,f.arith_ops,f.forcings,f.fully_reduced,t0.elapsed().as_secs_f64(),pretty(&decode(rb)));
   if f.fully_reduced {println!("*** fully_reduced=true at mf={mf} — data[0] image TERMINATES (depth bound found) ***");break;}
   if t0.elapsed().as_secs_f64()>50.0 {println!("(wall>50s at mf={mf} — divergent/too-deep; stop)");break;}
 }
}
