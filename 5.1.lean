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
