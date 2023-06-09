open classical

variables p q r s : Prop

example : (p → r ∨ s) → ((p → r) ∨ (p → s)) := 
assume h : p → r ∨ s,
have empr : (p → r) ∨ ¬(p → r), from em (p → r),
have g : ¬(p → r) → (p → s), from 
assume npr : ¬(p → r),
assume hp : p,
have hrs: r ∨ s, from h hp,
by_contradiction
  (assume ns : ¬s,
    or.elim hrs (assume hr : r, npr (assume t : p, hr))
                (assume hs: s, ns hs)),
or.elim empr 
  (assume hpr : p → r, or.intro_left (p → s) hpr)
  (assume npr : ¬(p → r), or.intro_right (p → r) (g npr))
-- i have a headache  

example : ¬(p ∧ q) → ¬p ∨ ¬q := 
assume npq : ¬(p ∧ q),
by_cases 
  (assume h1: p, 
  or.intro_right (¬p) (assume h2: q, npq (⟨h1, h2⟩)))
  (assume h1: ¬p,
  or.intro_left (¬q) h1)

example : ¬(p → q) → p ∧ ¬q := 
assume npq : ¬(p → q),
-- proof by truth table (this is a bit fucked)
by_cases 
  (assume hp: p,
    by_cases
      (assume hq: q,
        false.elim (npq (assume t: p, hq)))
      (assume nq: ¬q,
        show p ∧ ¬ q, from ⟨hp, nq⟩))
  (assume np : ¬p,
    show p ∧ ¬q, from 
    false.elim (npq (show p → q, from (assume hp: p, show q, from false.elim (np hp)))))

example : (p → q) → (¬p ∨ q) := 
assume hpq : p → q,
have emp: p ∨ ¬p, from em p,
or.elim emp
  (assume hp: p, or.intro_right (¬p) (hpq hp))
  (assume np: ¬p, or.intro_left q np)

example : (¬q → ¬p) → (p → q) := 
assume h  : ¬q → ¬p,
assume hp : p,
by_cases
  (assume hq : q, hq)
  (assume nq: ¬q, false.elim ((h nq) hp))

example : p ∨ ¬p := em p

example : (((p → q) → p) → p) := 
assume h : ((p → q) → p),
by_contradiction
  (assume np : ¬p,
    have pq: p → q, from  (assume t : p, false.elim (np t)),
    show false, from np (h pq))
