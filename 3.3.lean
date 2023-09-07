variable p: Prop

example : ¬(p ↔ ¬p) :=
assume h : p ↔ ¬p,
have rimp: p → p → false, from iff.elim_left h,
have limp: (p → false) → p, from iff.elim_right h,
have np : p → false, from (λ hp : p, rimp hp hp),
have hp : p, from limp np, 
show false, from rimp hp hp
-- whoa
