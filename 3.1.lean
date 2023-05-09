variables p q r : Prop

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p := 
  (let and_swap (a : Prop) (b : Prop) := 
    (assume hab : a ∧ b, 
      show b ∧ a, from and.intro hab.right hab.left) 
     in iff.intro (and_swap p q) (and_swap q p))

example : p ∨ q ↔ q ∨ p := 
have or_swap : Π (a b: Prop), a ∨ b → b ∨ a,
from λ (a b : Prop) (h : a ∨ b), 
        (or.elim h 
        (assume ha : a, or.intro_right b ha) 
        (assume hb : b, or.intro_left a hb)),
iff.intro (or_swap p q) (or_swap q p)

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := 
have rimp : (p ∧ q) ∧ r → p ∧ (q ∧ r), from 
assume hpq_r : ((p ∧ q) ∧ r),
        have hp : p, from (and.elim_left (and.elim_left hpq_r)),
        have hq : q, from (and.elim_right (and.elim_left hpq_r)),
        have hr : r, from (and.elim_right hpq_r),
        have hqr : q ∧ r, from (and.intro hq hr),
        show p ∧ (q ∧ r), from (and.intro hp hqr),
suffices limp : p ∧ (q ∧ r) → (p ∧ q) ∧ r, from iff.intro rimp limp,
assume hp_qr : (p ∧ (q ∧ r)),
        have hp : p, from (and.elim_left hp_qr),
        have hq : q, from (and.elim_left (and.elim_right hp_qr)),
        have hr : r, from (and.elim_right (and.elim_right hp_qr)),
        have hpq : p ∧ q, from (and.intro hp hq),
        show (p ∧ q) ∧ r, from (and.intro hpq hr)


example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := 
iff.intro 
(assume hpq_r : (p ∨ q) ∨ r,
  have hp : p → p ∨ (q ∨ r), from 
    (assume t : p, or.intro_left (q ∨ r) t),
  have hq : q → p ∨ (q ∨ r), from 
    (assume t : q, or.intro_right p (or.intro_left r t)),
  have hpq: p ∨ q → p ∨ (q ∨ r), from (assume t : p ∨ q, or.elim t hp hq),
  have hr : r → p ∨ (q ∨ r), from 
    (assume t : r, or.intro_right p (or.intro_right q t)),
  show p ∨ (q ∨ r), from or.elim hpq_r hpq hr)
(assume hp_qr : p ∨ (q ∨ r),
  have hp: p → (p ∨ q) ∨ r, from 
    (assume t : p, or.intro_left r (or.intro_left q t)),
  have hq: q → (p ∨ q) ∨ r, from
    (assume t : q, or.intro_left r (or.intro_right p t)),
  have hr: r → (p ∨ q) ∨ r, from
    (assume t : r, or.intro_right (p ∨ q) t),
  have hqr: (q ∨ r) → (p ∨ q) ∨ r, from 
    (assume t: q ∨ r, or.elim t hq hr),
  show (p ∨ q) ∨ r, from 
    (or.elim hp_qr hp hqr))

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := 
suffices rimp : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r), from 
-- this returns the main goal
suffices limp: _ , from iff.intro rimp limp, 
-- now we return limp, for the inner "suffices"
(assume hpq_pr : (p ∧ q) ∨ (p ∧ r),
  have hpq: p ∧ q → p ∧ (q ∨ r), from 
  assume t : p ∧ q, ⟨t.left, or.intro_left r t.right⟩,
  have hpr: p ∧ r → p ∧ (q ∨ r), from 
  assume t : p ∧ r, ⟨t.left, or.intro_right q t.right⟩,
  show p ∧ (q ∨ r), from or.elim hpq_pr hpq hpr),
-- now we prove return rimp, for the outer "suffices"
(assume hpqr : p ∧ (q ∨ r),
  have hqr : q ∨ r, from hpqr.right,
  have hp : p, from hpqr.left,
  have hq : q → (p ∧ q) ∨ (p ∧ r), from 
    assume t : q, or.intro_left _ ⟨hp, t⟩,
  have hr : r → (p ∧ q) ∨ (p ∧ r), from 
    assume t : r, or.intro_right _ ⟨hp, t⟩,
  or.elim hqr hq hr)


example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := 
have rimp : p ∨ (q ∧ r) → (p ∨ q) ∧ (p ∨ r), from
assume hp_qr : p ∨ (q ∧ r),
have hp : p → (p ∨ q) ∧ (p ∨ r), from
assume t : p, ⟨(or.intro_left q t), (or.intro_left r t)⟩,
have h_qr : (q ∧ r) → (p ∨ q) ∧ (p ∨ r), from
assume t : (q ∧ r), ⟨(or.intro_right p t.left), (or.intro_right p t.right)⟩,
or.elim hp_qr hp h_qr,
have limp : (p ∨ q) ∧ (p ∨ r) → p ∨ (q ∧ r), from
assume hpq_pr : (p ∨ q) ∧ (p ∨ r),
have hpq : p ∨ q, from hpq_pr.left,
have hqr : p ∨ r, from hpq_pr.right,
have hp  : p → p ∨ (q ∧ r), from assume t : p, or.intro_left _ t,
have hq  : q → p ∨ (q ∧ r), from assume t₁: q, or.elim hqr hp (assume t₂ : r, or.intro_right p
⟨t₁, t₂⟩),
show p ∨ (q ∧ r), from or.elim hpq hp hq,
iff.intro rimp limp

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) := 
have rimp : _, from 
assume hpqr: p → q → r,
show p ∧ q → r, from 
  (assume hpq: p ∧ q,
   have hp : p, from hpq.left,
   have hq : q, from hpq.right,
   show r, from hpqr hp hq),
have limp: _, from
assume hpqr : p ∧ q → r,
  (assume (hp: p) (hq: q), hpqr ⟨hp, hq⟩),
iff.intro rimp limp

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := 
have rimp : _, from
assume hpqr : (p ∨ q) → r,
have hp: p → r, from assume t: p, hpqr (or.intro_left _ t),
have hq: q → r, from assume t: q, hpqr (or.intro_right _ t),
show (p → r) ∧ (q → r), from ⟨hp, hq⟩,
have limp: _, from
assume hprqr : (p → r) ∧ (q → r),
assume hpq : p ∨ q,
or.elim hpq (hprqr.left) (hprqr.right),
iff.intro rimp limp

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := 
have rimp: _, from
assume hnpq : ¬(p ∨ q),
have hnp: ¬p, from 
assume t : p,
hnpq (or.intro_left q t),
have hnq: ¬q, from
assume t : q,
hnpq (or.intro_right p t),
show ¬p ∧ ¬q, from ⟨hnp, hnq⟩,
have limp: _, from
assume hnpnq : ¬p ∧ ¬q,
assume hpq: p ∨ q,
or.elim hpq hnpnq.left hnpnq.right,
iff.intro rimp limp

example : ¬p ∨ ¬q → ¬(p ∧ q) := 
assume t₁ : ¬p ∨ ¬q,
assume t₂ : p ∧ q,
have tp: ¬p → false, from (assume np: p → false, np t₂.left),
have tq: ¬q → false, from (assume nq: q → false, nq t₂.right),
or.elim t₁ tp tq

example : ¬(p ∧ ¬p) := 
assume t : p ∧ ¬p,
t.right t.left 

example : p ∧ ¬q → ¬(p → q) :=
assume t₁ : p ∧ ¬q,
assume t₂ : p → q,
t₁.right (t₂ t₁.left)

example : ¬p → (p → q) :=
assume np : ¬p,
assume hp : p,
show q, from absurd hp np

example : (¬p ∨ q) → (p → q) :=
assume h : ¬p ∨ q,
assume t : p,
or.elim h
  (assume np: ¬p,
    show q, from absurd t np)
  id

example : p ∨ false ↔ p := 
iff.intro 
  (assume t : p ∨ false, or.elim t id false.elim)
  (assume t : p, or.intro_left false t)

example : p ∧ false ↔ false := 
iff.intro
  (assume t : p ∧ false, t.right)
  (assume t : false, false.elim t)

example : (p → q) → (¬q → ¬p) := 
assume hpq : p → q, 
assume nq: ¬q,
show ¬p, from (assume hp : p, absurd (hpq hp) nq)
