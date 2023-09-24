  -- pp.all (Bool) (pretty printer) display coercions, implicit parameters, roof terms, fully qualified names, universes, and disable beta reduction and notation during pretty printing (default: false)
  
set_option pp.full_names false
namespace hidden

inductive nat 
| zero : nat
| succ : nat → nat

namespace nat

def add : nat → nat → nat
| m zero     := m
| m (succ n) := succ(add m n)

def mul : nat → nat → nat
| m zero     := zero
| m (succ n) := (add (mul m n) m)

def exp : nat → nat → nat
| m zero     := succ(zero)
| m (succ n) := (mul m (exp m n))

theorem add_zero (n : nat) : (add n zero) = n := by rw[add]
theorem add_succ (n m : nat) : (add n (succ m)) = succ (add n m) := by rw[add]

infix (name := add) ` + `:50 := add

theorem succ_add : ∀ (m n : nat),  (add (succ m) n) = succ (add m n) 
| m zero     := rfl
| m (succ n) := by { rw[add_succ, succ_add], refl}
-- blah blah
end nat
end hidden
