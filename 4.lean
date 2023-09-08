open classical

variables (α : Type*) (p q : α → Prop)
variable r : Prop

example : (∃ x : α, r) → r := 
assume p : (∃ x : α, r), 
exists.elim p (assume x, assume h : r, h)

example (a : α) : r → (∃ x : α, r) := 
assume r,
⟨a, r⟩

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := 
have rimp : (∃ x, p x ∧ r) → (∃ x, p x) ∧ r, from 
assume h : (∃ x, p x ∧ r),
match h with ⟨w, hw⟩ :=
  ⟨⟨w, hw.left⟩, hw.right⟩
end,
have limp : (∃ x, p x) ∧ r → (∃ x, p x ∧ r), from 
assume h : (∃ x, p x) ∧ r,
match h.left with ⟨w, hw⟩ :=
  ⟨w, hw, h.right⟩
end,
iff.intro rimp limp

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := 
have rimp : (∃ x, p x ∨ q x) → (∃ x, p x) ∨ (∃ x, q x), from
assume rhs, 
match rhs with ⟨(w : α), (hw : p w ∨ q w)⟩ := 
  or.elim hw 
    (assume h : p w, or.intro_left (∃ x, q x) ⟨w, h⟩)
    (assume h : q w, or.intro_right (∃ x, p x) ⟨w, h⟩)
end,
have limp : (∃ x, p x) ∨ (∃ x, q x) → (∃ x, p x ∨ q x), from
assume lhs : (∃ x, p x) ∨ (∃ x, q x),
or.elim lhs
  (assume hp : (∃ x, p x), 
    match hp with ⟨w, hw⟩ := 
      show (∃ x,  p x ∨ q x), 
      from  ⟨w, or.intro_left (q w) hw⟩ 
    end)
  (assume hq : (∃ x, q x), 
    match hq with ⟨w, hw⟩ := 
      show (∃ x,  p x ∨ q x), 
      from  ⟨w, or.intro_right (p w) hw⟩ 
    end),
iff.intro rimp limp

-- this needs classical 
example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := sorry
example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := sorry
example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := sorry
example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := sorry

example : (∀ x, p x → r) ↔ (∃ x, p x) → r := 
have rimp : (∀ x, p x → r) → (∃ x, p x) → r, from
assume (h₁ : ∀ x, p x → r) (h₂ : ∃ x, p x),
match h₂ with ⟨w, h₃⟩ := 
  show r, from ((h₁ w) h₃)
end,
have limp : ((∃ x, p x) → r) → (∀ x, p x → r), from
assume (h₁ : (∃ x, p x) → r), 
assume x : α , 
assume h : p x, 
show r, from h₁ ⟨x, h⟩,
iff.intro rimp limp

section
open classical 

example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r := 
have rimp : (∃ x, p x → r) → (∀ x, p x) → r, from
assume (h₁ : ∃ x, p x → r) (h₂ : ∀ x, p x),
match h₁ with ⟨x, h₃⟩ := h₃ (h₂ x)
end,
suffices limp : ((∀ x, p x) → r) → (∃ x, p x → r), from iff.intro rimp limp,
assume h₁ : (∀ x, p x) → r, 
by_cases 
  (assume h₂ : (∀ x, p x),
    have h₃ : p a, from h₂ a,
    have h₄ : (p a → r), from (assume t : p a, h₁ h₂),
    show ∃ x, p x → r, from ⟨a, h₄⟩)
  (assume h₂ : ¬(∀ x, p x),
    have h₃ : ∃ x, ¬p x, from by_contradiction
    (assume h₄ : ¬(∃ x, ¬ p x),
    h₂ (assume x : α, 
       show p x, from
       by_contradiction 
         (assume t : ¬ p x,
           h₄ ⟨x, t⟩))),
    match h₃ with ⟨x, hx⟩ := 
      have t : (p x → r), from 
        (assume h : p x, false.elim (hx h)),
      ⟨x, t⟩
    end)
end

example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) := sorry
