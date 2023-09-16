import data.nat.basic

inductive form 
| const : bool → form
| var   : ℕ → form
| and   : form → form → form
| or    : form → form → form

def evaluate (x : form) (f : ℕ → bool) : bool :=
begin
  induction x,
  case const : x { exact x },
  case var   : n { exact f n },
  case and   : f1 f2 ef1 ef2 { exact (ef1 && ef2) },
  case or    : f1 f2 ef1 ef2 { exact (ef1 || ef2) }
end

def complexity (x : form) : nat :=
begin
  induction x, 
  case const : x { exact 0},
  case var   : n { exact 0},
  case and   : f1 f2 cf1 cf2 { exact 1 + (max cf1 cf2) },
  case or    : f1 f2 cf1 cf2 { exact 1 + (max cf1 cf2) } 
end

def subst (x : form) (n : ℕ) (y : form) : form :=
begin
  induction x, 
  case const :   { exact form.const x },
  case var   : m { exact if m = n then y else form.var m},
  case and   : f1 f2 sf1 sf2  { exact form.and sf1 sf2 },
  case or    : f1 f2 sf1 sf2  { exact form.or sf1 sf2 }
end
