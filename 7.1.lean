namespace hidden
inductive nat : Type
| zero : nat
| succ : nat → nat

namespace nat

def add (m n : nat) : nat :=
nat.rec_on m n (λ (m : nat) (prev : nat), succ(prev))

def mul (m n : nat) : nat :=
nat.rec_on m zero (λ (m : nat) (prev : nat), (add prev n))

def pred (m : nat) : nat :=
nat.cases_on m zero (λ (m : nat), m)

def sub (m n : nat) : nat :=
nat.rec_on n m (λ (n : nat) (prev : nat), pred(prev))

def exp (m n : nat) : nat :=
nat.rec_on n zero.succ (λ (n : nat) (prev : nat), mul m prev)
end nat
end hidden
