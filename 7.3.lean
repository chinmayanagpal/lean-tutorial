inductive pol
| const : nat → pol
| var   : nat → pol
| plus  : pol → pol → pol
| times : pol → pol → pol


def evaluate (x : pol) (f : ℕ → ℕ) : ℕ :=
begin
  induction x,
    case const : x { exact x }, 
    case var : x { exact f x }, 
    case plus : x1 x2 ex1 ex2 { exact ex1 + ex2 },
    case times : x1 x2 ex1 ex2 { exact ex1 * ex2 }
end

#reduce evaluate (pol.plus (pol.times (pol.var 1) (pol.var 1)) (pol.times (pol.var 1)
 (pol.const 2))) id
 
-- fuck!
