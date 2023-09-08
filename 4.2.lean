variables (α : Type*) (p q : α → Prop)
variable r : Prop

example : α → ((∀ x : α, r) ↔ r) := 
assume x : α, 
(iff.intro (assume h : (∀ x : α, r), h x)
           (assume h : r, assume x : α, h))

section
open classical
example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := 
iff.intro 
  (assume h,
    by_cases
      (assume : r,
        or.intro_right (∀ x, p x) this)
      (assume : ¬r,
        or.intro_left r (assume x, or.elim (h x) id (assume : r, false.elim (‹¬
        r› ‹r›)))))
  (assume h,
    or.elim h (assume : (∀ x, p x), (assume x, or.intro_left r (this x)))
              (assume : r, (assume x, or.intro_right (p x) this)))

end

example : (∀ x, r → p x) ↔ (r → ∀ x, p x) := 
iff.intro
  (assume h, assume r, assume x, 
    (h x) r)
  (assume h, assume x, assume r,
    ((h r) x))
