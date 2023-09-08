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
section
open classical 
example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := 
have rimp : (∀ x, p x) →  ¬ (∃ x, ¬ p x), from
assume rhs : (∀ x, p x), 
assume h : (∃ x, ¬ p x),
match h with ⟨a, npa⟩ :=
  npa (rhs a)
end,
have limp : ¬(∃ x, ¬ p x) → (∀ x, p x), from
assume rhs : ¬(∃ x, ¬ p x),
assume x : α,
by_contradiction
  (assume npx : ¬ (p x),
    (rhs ⟨x, npx⟩)),
iff.intro rimp limp

example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := 
have rimp : (∃ x, p x) → ¬ (∀ x, ¬ p x), from 
assume rhs : (∃ x, p x), 
show ¬(∀ x, ¬ p x), from
by_contradiction
  (assume h : ¬¬ ∀ x, ¬ p x,
    have nnh : ∀ x, ¬ p x, from
      by_contradiction
        (assume nh : ¬ (∀ x, ¬ p x),
          h nh),
    match rhs with ⟨a, pa⟩ := 
      (nnh a) pa
    end),
have limp : ¬ (∀ x, ¬ p x) → (∃ x, p x), from 
(assume h : ¬ (∀ x, ¬ p x), show ∃ x, p x, from by_contradiction
  (assume t : ¬(∃ x, p x),
    have ∀ x, ¬ p x, from 
      (assume x, show ¬ p x, from
        by_contradiction
          (assume h : ¬ ¬ p x,
            have nnh : p x, from 
              by_contradiction
                (assume nh : ¬ p x, h nh),
            t ⟨x, nnh⟩)),
    h this)),
iff.intro rimp limp

example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := 
have rimp : (¬ ∃ x, p x) → (∀ x, ¬ p x), from 
assume (rhs : ¬ ∃ x, p x) (x : α) (h : p x), (rhs ⟨x, h⟩),
suffices limp : (∀ x, ¬ p x) → (¬ ∃ x, p x), from iff.intro rimp limp,
assume h : (∀ x, ¬ p x),
show ¬ ∃ x, p x, from 
by_cases
  (assume t : (∃ x, p x), 
    match t with ⟨a, pa⟩ := false.elim (h a pa) end)
  (assume t : ¬(∃ x, p x), t)

example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := 
suffices limp : (∃ x, ¬ p x) → (¬ ∀ x, p x), from 
suffices rimp : (¬ ∀ x, p x) → (∃ x, ¬ p x), from
iff.intro rimp limp,
assume rhs : (¬ ∀ x, p x),
by_contradiction
  (assume con : ¬ ∃ x, ¬ p x,
    have h: ∀ x, p x, from 
      (assume x : α,
        show p x, from by_contradiction
          (assume t : ¬ p x,
            con ⟨x, t⟩)),
    show false, from rhs h),
assume lhs : (∃ x, ¬ p x),
assume h: ∀ x, p x, 
match lhs with ⟨a, npa⟩ :=
  npa (h a)
end


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

example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) := 
have rimp : (∃ x, r → p x) → (r → ∃ x, p x), from 
assume h₁ : (∃ x, r → p x),
match h₁ with ⟨a, h⟩ :=
  (assume t : r, 
    have h₂ : p a, from h t,
    ⟨a, h₂⟩)
end,
have limp : (r → ∃ x, p x) → (∃ x, r → p x), from
assume rhs : (r → ∃ x, p x),
by_cases
  (assume h : r,
    match (rhs h) with ⟨a, pa⟩ :=
      have t : (r → p a), from (assume g : r, pa),
      show (∃ x, r → p x), from ⟨a, t⟩
    end)
  (assume nh : ¬r,
    suffices r → p a, from ⟨a, this⟩, 
    (assume h : r, false.elim (nh h))),
iff.intro rimp limp

end
