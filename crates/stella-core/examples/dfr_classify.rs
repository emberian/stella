//! Classify deterministic_functional_read: is the failure a WRONG answer
//! (real correctness bug ⇒ surface) or fuel-exhaustion None at the big
//! mul pairs (fuel/reference-cost-marginal ⇒ documented #[ignore], same
//! class as mul_table)? Prints the actual eval_nat returns.
use stella_core::binarith::eval_nat;
fn main() {
    const FUEL: usize = 20_000; // the test's FUEL
    for (a,b) in [(0u128,0u128),(1,0),(0,1),(5,6),(13,9),(31,1)] {
        let add = eval_nat("add", a, b, FUEL);
        let mul = eval_nat("mul", a, b, FUEL);
        let add_ok = add == Some(a+b);
        let mul_ok = mul == Some(a*b);
        println!("({a},{b}): add={add:?} want {} {} | mul={mul:?} want {} {}",
            a+b, if add_ok {"OK"} else {"<<DIFF"},
            a*b, if mul_ok {"OK"} else if mul.is_none() {"<<None=FUEL-EXHAUSTED (marginal, not wrong)"} else {"<<WRONG VALUE = REAL BUG"});
    }
}
