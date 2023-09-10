-- Exercises from chapter 3
-- exercise 1

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
