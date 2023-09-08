variables (men : Type*) (barber : men)
variable  (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) :
  false := 
  let p := shaves barber barber in 
  have hb : p ↔ ¬ p, from h barber,
  have ¬p,  from (assume t : p, (hb.elim_left t t)),
  have p, from hb.elim_right ‹¬p›,
  show false, from ‹¬p› ‹p›
