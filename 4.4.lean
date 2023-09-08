import data.nat.parity

#check even

def prime (n : ℕ) : Prop := 
let divides (a : ℕ) (b : ℕ) : Prop := (∃ q : ℕ, b = q * a) in
(∀ m : ℕ, ¬(m = 1 ∨ m = n) → ¬(divides m n))

def infinitely_many_primes : Prop := ∀ n : ℕ, ∃ p, p > n ∧ prime p

def Fermat_prime (n : ℕ) : Prop := 
(prime n) ∧ (∃ m: ℕ, n = 2^(2^m) + 1)

def infinitely_many_fermat_primes : Prop := ∀ n, ∃ m, Fermat_prime m ∧ m > n

def goldbach_conjecture : Prop := 
∀ n, n > 2 →  ∃ p q r : ℕ, prime p ∧ prime q ∧ n = p + q

def Goldbach's_weak_conjecture : Prop := 
∀ n, n > 5 → ∃ p q r : ℕ, prime p ∧ prime q ∧ prime r ∧ n = p + q + r

def Fermat's_last_theorem : Prop :=
¬ (∃ (a b c n : ℕ),  a > 0 ∧ b > 0 ∧ c > 0 ∧ n > 0 ∧ (a^n + b^n = c^n))
