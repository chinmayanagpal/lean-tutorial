import data.real.basic
import data.int.basic 
-- Exercises from chapter 3
-- exercise 3.1

section
variables p q r : Prop

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p := 
  by apply iff.intro; { intro h, cases h, { split; assumption } }

example : p ∨ q ↔ q ∨ p := 
  by apply iff.intro; { intro h, cases h; simp * }

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := 
  by apply iff.intro; { intro h, try { simp at h }, try { simp *} }
example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := 
  by apply iff.intro; { intro h, repeat { cases h <|> simp * } }

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := 
  by apply iff.intro; { intro h, repeat { cases h <|> simp * } }

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := 
begin
  apply iff.intro, 
    intro h, cases h; {split; simp*}, 
    intro h, cases h with hpq hqr, cases hpq; simp *
end
-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) := 
by apply iff.intro; { intros, simp * }

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := 
begin
apply iff.intro, 
  { intros, split; { intros, simp *} }, -- lhs → rhs
  { intro h, cases h, intro h, cases h; simp * } -- rhs → lhs
end

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := 
begin
  apply iff.intro, 
    { intro h, split; {intro, have : p ∨ q, simp *, exact h this} }, -- rimp
    { intro h, simp * } -- limp
end

example : ¬p ∨ ¬q → ¬(p ∧ q) := 
begin
  intro h, intro h', cases h', cases h; contradiction
end

example : ¬(p ∧ ¬p) := 
by {intro h, cases h, contradiction}
example : p ∧ ¬q → ¬(p → q) := 
by {intro h, cases h, intro h, have : q, simp *, contradiction }

example : ¬p → (p → q) := 
by {intro, intro, contradiction }
example : (¬p ∨ q) → (p → q) := 
by {intro h, cases h; { intro, { contradiction <|> assumption} }}

example : p ∨ false ↔ p :=
begin
  apply iff.intro, 
    {intro h, cases h; {assumption <|> contradiction}},
    {intro h, simp*}
end

example : p ∧ false ↔ false := 
by {  apply iff.intro, { intro, simp * }, { intro, contradiction } }

example : (p → q) → (¬q → ¬p) := 
by {repeat {intro},  have : q, from ‹p → q› ‹p›, contradiction } 
end

-- exercise 3.2

section
open classical

variables p q r s : Prop

example : (p → r ∨ s) → ((p → r) ∨ (p → s)) := 
begin
  intro, have : (p → r) ∨ ¬(p → r), from em _, cases this, 
    { left, assumption },
    { 
      right, 
      intro, 
      have : r ∨ s, simp *, 
      cases this, 
        { have : p → r, simp *, contradiction },
        { simp * } 
    }
end
example : ¬(p ∧ q) → ¬p ∨ ¬q := 
begin
  intro,
  -- iterate over cases for p and q
  by_cases p,
  by_cases q,
    -- case: p ∧ q
    { have : p ∧ q, by simp *, contradiction},     
    -- all other cases, we have at least one of [¬p, ¬q]
    repeat {simp *}
end

-- i'm getting good at this

example : ¬(p → q) → p ∧ ¬q := 
begin
  intro, 
  split, 
  begin
    by_contradiction, 
    have : p → q, 
      intro, contradiction, 
    contradiction
  end,
  begin
    by_cases q,
      intro, 
      have : p → q, simp *,
      contradiction,
      assumption,
  end
end

example : (p → q) → (¬p ∨ q) := 
by { intro, by_cases p, right, simp *, left, assumption }

example : (¬q → ¬p) → (p → q) := 
by { intros h hp, by_contradiction hnq, have : ¬p, from h hnq, contradiction }
example : p ∨ ¬p := 
by { by_cases p, left, assumption, right, assumption }
-- why tho
example : (((p → q) → p) → p) := 
begin
  intro hyp,
  by_cases p, 
    assumption,
    have : p → q, { intro, contradiction },
    exact hyp this
end

end

-- exercise 3.3
section
variable p: Prop

example : ¬(p ↔ ¬p) := 
begin
  intro h, 
  cases h, 
  by_cases p, 
    have : ¬p, from h_mp h, 
    contradiction, 
  have : p, from h_mpr h,
  contradiction
end
end


-- chapter 4
-- exercise 4.1
section
variables (α : Type*) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := 
by apply iff.intro; { intro h, simp *}
example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := 
by { intros, simp *}
example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := 
by { intro h, cases h; simp *}
end

-- exercise 4.2
section
variables (α : Type*) (p q : α → Prop)
variable r : Prop

example : α → ((∀ x : α, r) ↔ r) := 
begin
  intro a,
  apply iff.intro, 
    assume h, exact h ‹α›, 
  intros, assumption
end

section uses_classical
open classical

example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := 
begin
  apply iff.intro, 
  begin
    intro h, by_cases hr: r, 
      { right, assumption }, 
      { left, assume x, cases (h x), assumption, contradiction },
  end,
  begin
    intro h, cases h, 
      { assume x, left, exact h x },
      { assume x, right, assumption }
  end
end
end uses_classical

example : (∀ x, r → p x) ↔ (r → ∀ x, p x) := 
by  apply iff.intro; { intros, simp * }
end

-- exercise 4.4 : no theorems/examples

-- exercise 4.5
section
open classical

variables (α : Type*) (p q : α → Prop)
variable r : Prop

example : (∃ x : α, r) → r := 
by { intro h, cases h, assumption }
example (a : α) : r → (∃ x : α, r) := 
by { intro h, split; assumption }
example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := 
begin
  apply iff.intro,
  begin
    intro h,
    split; cases h with a ha, 
    split, exact ha.left, 
    exact ha.right,
  end,
  begin
    intro h,
    cases h with hl hr,
    cases hl with a hla,
    split, split, assumption, assumption 
  end
end

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := 
begin
  apply iff.intro,
  begin
    intro h, 
    cases h with a ha, 
    cases ha,
      left, split, exact ha,
    right, split, exact ha
  end,
  begin
    intro h,
    cases h,
      cases h, split, left, assumption,
    cases h, split, right, assumption
  end
end

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := 
begin
  apply iff.intro,
  begin
    intro h,
    by_contradiction h',
      cases h' with a hna, exact hna (h a),
  end,
  begin
    intro h,
    assume x,
    by_contradiction hnx, 
      exact h (exists.intro x hnx),
  end
end
example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := 
begin
  apply iff.intro,
  begin
    intro h,
    by_contradiction h',
      cases h with a ha, exact (h' a) ha, 
  end,
  begin
    intro h,
    by_contradiction h',
    exact h (assume x : α, assume t: p x, h' (exists.intro x t)) 
  end
end
example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := 
begin
apply iff.intro,
  begin
    intro,
    assume x, 
    assume t,
    have : ∃ x, p x, 
    existsi x, exact t, contradiction
  end,
  begin
    intro h,
    by_contradiction h',
    cases h' with a h'a,
    exact (h a) h'a
  end
end
example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := 
begin
apply iff.intro,
  begin
    intro h, 
    by_contradiction h',
    have, from (assume x: α, show p x, from by_contradiction ((assume t : ¬p x,
    h' (exists.intro x t)))),
    contradiction
  end,
  begin
    intro h,
    by_contradiction h', 
    cases h with a ha,
    have : p a, from h' a, 
    contradiction
  end
end

example : (∀ x, p x → r) ↔ (∃ x, p x) → r := 
begin
apply iff.intro,
  begin
    intro h,
    intro h',
    cases h' with a h'a, 
    exact h a h'a 
  end,
  begin
    intro h,
    assume x, assume t, 
    have : (∃ x : α, p x), existsi x, exact t,
    simp *
  end
end
example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r := 
begin
apply iff.intro,
  begin
    intro h, cases h, intro, simp *
  end,
  begin
    intro h₁,
    by_cases h₂ : (∀ x, p x),
      have h₃ : p a, from h₂ a,
      have h₄ : (p a → r), from (assume t : p a, h₁ h₂),
      show ∃ x, p x → r, existsi a, exact h₄,
    have h₃ : ∃ x, ¬ p x, by_contradiction h₄,
    from h₂ begin assume x, show p x, by_contradiction t, exact h₄ ⟨x, t⟩ end,
    cases h₃ with x hx,
    have t : p x → r, intro, contradiction, 
    constructor, assumption 
  end
end
example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) := 
begin
apply iff.intro,
  begin
    intro h, intro t, cases h, existsi h_w, exact h_h t
  end,
  begin
    intro h,
    by_cases t : r,
      have, from h t,
      cases this,
      existsi this_w,
      intro, assumption,
    existsi a, intro, contradiction
  end
end

end

-- exercise 4.6
section
-- import data.real.basic (top of file)

variables log exp     : real → real
variable  log_exp_eq : ∀ x, log (exp x) = x
variable  exp_log_eq : ∀ {x}, x > 0 → exp (log x) = x
variable  exp_pos    : ∀ x, exp x > 0
variable  exp_add    : ∀ x y, exp (x + y) = exp x * exp y

-- this ensures the assumptions are available in tactic proofs
include log_exp_eq exp_log_eq exp_pos exp_add

example (x y z : real) :
  exp (x + y + z) = exp x * exp y * exp z :=
by rw [exp_add, exp_add]

example (y : real) (h : y > 0)  : exp (log y) = y :=
exp_log_eq h

theorem log_mul {x y : real} (hx : x > 0) (hy : y > 0) :
  log (x * y) = log x + log y :=
begin
  rw [←exp_log_eq hx, ←exp_log_eq hy],
  rw [←exp_add],
  repeat { rw [log_exp_eq] },
end
end


-- exercise 4.7

section
-- import data.int.basic (top of file)

#check sub_self

example (x : ℤ) : x * 0 = 0 :=
  by simp *
end
