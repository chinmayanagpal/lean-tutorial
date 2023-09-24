import tactic.suggest
universe u
inductive vector (α : Type u) : nat → Type u
| nil {} : vector 0
| cons   : Π {n}, α → vector n → vector (n + 1)

namespace vector
local notation (name := cons) h :: t := cons h t

def head {α : Type*} : Π {n}, vector α (n+1) → α
| n (h :: t) := h

def tail {α : Type*} : Π {n}, vector α (n+1) → vector α n
| n (h :: t) := t

def append_aux {α : Type*} {m n: ℕ} (v₁: vector α m) (v₂ : vector α n) : (∀ l : ℕ, l = m + n → vector α l) :=
begin
induction v₁ with m head tail ih, 
  exact (λ (l) h : l = 0 + n, by { rw[nat.zero_add] at h, exact eq.rec_on (eq.symm h) v₂ }),
  intro l, intro h, 
  have tailv₂ : vector α (m + n), apply ih, refl, 
  rw [nat.add_right_comm] at h, 
  exact eq.rec_on (eq.symm h) cons head tailv₂
end

def append {α : Type*} {m n : ℕ} (v₁ : vector α m) (v₂ : vector α n) :  vector α (m + n):=
append_aux v₁ v₂ (m + n) rfl

end vector
