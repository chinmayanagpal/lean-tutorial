variables (α : Type*) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := 
  iff.intro 
    (assume : ∀ x, p x ∧ q x,
      ⟨(assume w, (this w).left), (assume w, (this w).right)⟩)
    (assume : (∀ x, p x) ∧ (∀ x, q x),
      (assume w, ⟨this.left w, this.right w⟩))
    
example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := 
assume : ∀ x, p x → q x,
assume : ∀ x, p x,
assume x,
(‹∀ x, p x → q x› x) (‹∀ x, p x› x)

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := 
assume : (∀ x, p x) ∨ (∀ x, q x),
or.elim this
  (assume : (∀ x, p x),
    (assume x, or.intro_left (q x) (this x)))
  (assume : (∀ x, q x),
    (assume x, or.intro_right (p x) (this x)))
