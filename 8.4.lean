-- course of value recursion
-- a function f
-- a definition of f(0)
-- given a function that defines f on {0, ..., n - 1}, a definition of f(n)
import tactic.suggest
import data.nat.basic
import data.vector

open nat
open tactic 
-- open classical

def fix {β : Type} (f : (∀ n : ℕ, (∀ m : ℕ, m < n → β) → β)) (n : ℕ): β :=
begin
  have F : ∀ m : ℕ, m < n → β,
    induction n with n ih,
      intros m t, 
      have : ¬(m < 0), exact nat.not_lt_zero m, 
      contradiction,
    intros m t,
      -- i'm cheating. may god forgive me.
      by_cases m = n, 
        exact f n ih,
      have : m < n, exact array.push_back_idx t h,
      exact ih m this,
  exact f n F 
end

-- much easier
def fix' {β : Type} (f : (∀ n : ℕ, vector β n → β)) (n : ℕ): β :=
begin
  have v : vector β n,
    induction n with n ih,
      exact vector.nil, 
    exact vector.append ih (vector.cons (f n ih) vector.nil),
  exact f n v
end
