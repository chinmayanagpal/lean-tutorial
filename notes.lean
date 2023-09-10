import data.nat.basic
import data.list.basic
section
variables x y z w : ℕ

example (h₁ : x = y) (h₂ : y = z) (h₃ : z = w) : x = w :=
begin
  apply eq.trans,
  assumption, -- solves x = ?m_1 with h₁
  apply eq.trans,
  assumption,  -- solve y = ?m_1 with h₂
  assumption
end 

end

section
example : ∀ a b c : ℕ, a = b → a = c → c = b := 
begin
  intros,
  apply eq.trans,
  apply eq.symm,
  repeat { assumption }
end 
end

section
example (y : ℕ) : (λ x : ℕ, 0) y = 0 :=
begin
  refl
end

example (x : ℕ) : x ≤ x :=
begin
  refl
end

example : ∀ a b c : ℕ, a = b → a = c → c = b :=
begin
  intros,
  transitivity,
  symmetry,
  assumption,
  assumption
end

example : ∃ a : ℕ, 5 = a :=
begin
  fapply exists.intro,
  exact 5,
  refl
end

example (a : ℕ) : a = a :=
begin
  revert a,
  intro y,
  reflexivity
end


example (x y : ℕ) (h : x = y) : y = x :=
begin
  revert h,
  intro h1,
  symmetry,
  assumption
end

example (x y : ℕ) (h : x = y) : y = x :=
begin
  revert x,
  intros,
  symmetry,
  assumption
end

example (x y : ℕ) (h : x = y) : y = x :=
begin
  revert x y,
  intros,
  symmetry,
  assumption
end
end


-- 5.3. More Tactics
section
example (p q : Prop) : p ∨ q → q ∨ p :=
begin
  intro h,
  cases h with hp hq,
  -- case hp : p
  right, exact hp,
  -- case hq : q
  left, exact hq
end


example (p q : Prop) : p ∧ q → q ∧ p :=
begin 
  intro h,
  cases h with hp hq,
  constructor, exact hq, exact hp
end
end

-- using these tactics, we can rewrite an example from a previous section more
-- easily
section
example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q ) ∨ (p ∧ r) :=
begin
  apply iff.intro,
  intro h,
    cases h with hp hqr,
    cases hqr with hq hr,
      left, constructor, repeat { assumption },
      right, constructor, repeat { assumption },
  intro h,
    cases h with hpq hpr,
      cases hpq with hp hq, 
        constructor, exact hp, left, exact hq,
      cases hpr with hp hr,
        constructor, exact hp, right, exact hr
end 

-- actually we can unpack any element of an inductively defined type with the
-- "cases" tactic, and left and right can be used for anything with exactly two
-- constructors. e.g. :

example (p q : ℕ → Prop) : (∃ x, p x) → ∃ x, p x ∨ q x :=
begin
  intro h,
  cases h with x px,
  existsi x, left, exact px
end


example (p q : ℕ → Prop) : (∃ x, p x ∧ q x) → ∃ x, q x ∧ p x :=
begin
  intro h,
  cases h with x hpq,
  cases hpq with hp hq,
  existsi x,
  split; assumption
end
end

section
universes u v

def swap_pair {α : Type u} {β : Type v} : α × β → β × α :=
begin
  intro p,
  cases p with ha hb,
  constructor, exact hb, exact ha
end

def swap_sum {α : Type u} {β : Type v} : α ⊕ β → β ⊕ α :=
begin
  intro p,
  cases p with ha hb,
    right, exact ha,
    left, exact hb
end

open nat

example (P : ℕ → Prop) (h₀ : P 0) (h₁ : ∀ n, P (succ n)) (m : ℕ) : P m :=
begin
  cases m with m',
    exact h₀,
  exact h₁ m'
end
end

-- contradiction tactic: searches for a contradiction amongst the hypotheses
section
example (p q : Prop) : p ∧ ¬ p → q :=
begin
  intro h,
  cases h,
  contradiction
end  
end
-- 5.4. structuring tactic proofs

-- long sections of instructions cna obscure hte structure of the argumnet
-- we descirbe some means that can give structure to such a style of proof

-- one : mix term and tactic style proofs, passing betwene the two freely
-- e.g. apply and exact can take have and show as inputs
section
example (p q r : Prop) : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) :=
begin
  intro h,
  exact
    have hp : p, from h.left,
    have hqr : q ∨ r, from h.right,
    show p ∧ q ∨ (p ∧ r), from
    begin
      cases hqr with hq hr,
        exact or.inl ⟨hp, hq⟩,
      exact or.inr ⟨hp, hr⟩
    end
end 


example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
begin
  apply iff.intro,
    intro h,
    cases h.right with hq hr,
      exact or.inl ⟨h.left, hq⟩,
    exact or.inr ⟨h.left, hr⟩,
  intro h,
  cases h with hpq hpr,
    exact ⟨hpq.left, or.inl hpq.right⟩,
  exact ⟨hpr.left, or.inr hpr.right⟩
end

-- show tactic checks the type of goal about to be solved without changing mode
-- from is a synonym for exact

example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
begin
  apply iff.intro,
    intro h,
    cases h.right with hq hr,
      show (p ∧ q) ∨ (p ∧ r),
        from or.inl ⟨h.left, hq⟩,
      show (p ∧ q) ∨ (p ∧ r),
        from or.inr ⟨h.left, hr⟩,
    intro h,
    cases h with hpq hpr,
      show p ∧ (q ∨ r),
        {cases hpq with hp hq, split, exact hp, left, exact hq},
      show p ∧ (q ∨ r),
        {cases hpr with hp hr, split, exact hp, right, exact hr}
end
end
-- show can be used to redefine goals
section
example (n : ℕ) : n + 1 = nat.succ n :=
begin
  show nat.succ n = nat.succ n,
  reflexivity
end


-- show can be used to select goals out of order, as shown in the following two
-- examples
example (p q : Prop) : p ∧ q → q ∧ p :=
begin
  intro h,
  cases h with hp hq,
  split,
  show q, from hq,
  show p, from hp
end

example (p q : Prop) : p ∧ q → q ∧ p :=
begin
  intro h,
  cases h with hp hq,
  split,
  show p, from hp,
  show q, from hq
end

example (p q r : Prop) : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) :=
begin
  intro h,
  cases h with hp hqr,
  show (p ∧ q) ∨ (p ∧ r),
  cases hqr with hq hr,
    -- case hq : q
    have hpq : p ∧ q, 
      from and.intro hp hq,
    left, exact hpq,
  -- case hr : r
  have hpr : p ∧ r,
    from and.intro hp hr,
  right, exact hpr
end

-- can omit "from" and stay in tactic mode (no "apply", which is what from is)

example (p q r : Prop) : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) :=
begin
  intro h,
  cases h with hp hqr,
  show (p ∧ q) ∨ (p ∧ r),
  cases hqr with hq hr,
    -- case hq : q
    have hpq : p ∧ q,
      split; assumption,
    left, exact hpq,
  -- case hr : r
  have hpr : p ∧ r,
    split; assumption,
  right, exact hpr
end

-- can omit label in "have" tactic

example (p q r : Prop) : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) :=
begin
  intro h,
  cases h with hp hqr,
  show (p ∧ q) ∨ (p ∧ r),
  cases hqr with hq hr,
    -- case hq : q
    have : p ∧ q,
      split; assumption,
    left, exact this,
  have : p ∧ r,
    split; assumption,
  right, exact this
end

-- also can have "have" tactic with ":=" token, having the same efect as "from":

example (p q r : Prop) : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) :=
begin
  intro h,
  have hp : p := h.left,
  have hqr : q ∨ r := h.right,
  show (p ∧ q) ∨ (p ∧ r),
  cases hqr with hq hr,
    exact or.inl ⟨hp, hq⟩,
  exact or.inr ⟨hp, hr⟩
end
end
-- there is also a let tactic, allows us to introduce local definitions asw
section
example : ∃ x, x + 2 = 8 :=
begin
  let a : ℕ := 3 * 2,
  existsi a,
  reflexivity
end

-- can nest begin and end
example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
begin
  apply iff.intro,
  begin
    intro h,
    cases h.right with hq hr,
    -- case hq : q
    begin
      show (p ∧ q) ∨ (p ∧ r),
        exact or.inl ⟨h.left, hq⟩
    end,
    -- case hr : r
    show (p ∧ q) ∨ (p ∧ r),
      exact or.inr ⟨h.left, hr⟩
 end,
 intro h,
 cases h with hpq hpr,
 -- case hpq : p ∧ q
 begin
   show p ∧ (q ∨ r),
     exact ⟨hpq.left, or.inl hpq.right⟩
 end,
 -- case hpr: p ∧ r
 show p ∧ (q ∨ r),
   exact ⟨hpr.left, or.inr hpr.right⟩
end
-- can achieve the same thing using {} but only within outer pair of begin/end
-- block
example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
begin
  apply iff.intro,
  { intro h,
    cases h.right with hq hr,
    -- case hq : q
    { show (p ∧ q) ∨ (p ∧ r),
        exact or.inl ⟨h.left, hq⟩ },
    -- case hr : r
    show (p ∧ q) ∨ (p ∧ r),
      exact or.inr ⟨h.left, hr⟩ },
 intro h,
 cases h with hpq hpr,
 -- case hpq : p ∧ q
 { show p ∧ (q ∨ r),
     exact ⟨hpq.left, or.inl hpq.right⟩ },
 -- case hpr: p ∧ r
 show p ∧ (q ∨ r),
   exact ⟨hpr.left, or.inr hpr.right⟩
end

-- tactic combinators combine tactics to form new ones. sequencing combinator is
-- implicit in thecommas that appear in a begin/end block

example (p q : Prop) (hp : p) : p ∨ q :=
begin left, assumption end

-- or :

example (p q : Prop) (hp : p) : p ∨ q :=
by { left, assumption }

-- { .. } above is a single tactic which first applies left and then applies
-- assumption

-- in an expression t₁; t₂, the semicolon provides a /parallel/ version of the
-- sequencing operation. t₁ is applied to the current goal, and t₂ is applied to
-- /all/ resulting subgoals

example (p q : Prop) (hp : p) (hq : q) : p ∧ q :=
begin
  split; assumption
end
end
-- "orelse" tactic, denoted <|>, applies a tactic, and then if that doesn't
-- work, it backtracks and applies another
section
example (p q : Prop) (hp : p) : p ∨ q :=
-- left branch succeeds
by { left, assumption } <|> { right, assumption }


example (p q : Prop) (hq : q) : p ∨ q :=
-- right branch succeeds
by { left, assumption } <|> { right, assumption }

-- important: repeat
example (p q r : Prop) (hp : p) : p ∨ q ∨ r :=
by repeat { {left, assumption} <|> right <|> assumption }

example (p q r : Prop) (hq : q) : p ∨ q ∨ r :=
by repeat { {left, assumption} <|> right <|> assumption }

example (p q r : Prop) (hr : r) : p ∨ q ∨ r :=
by repeat { {left, assumption} <|> right <|> assumption }
end
-- tactics can be defined and then applied later on
section
meta def my_tac : tactic unit :=
`[ repeat { {left, assumption} <|> right <|> assumption } ]


example (p q r : Prop) (hp : p) : p ∨ q ∨ r :=
by my_tac

example (p q r : Prop) (hq : q) : p ∨ q ∨ r :=
by my_tac

example (p q r : Prop) (hr : r) : p ∨ q ∨ r :=
by my_tac
end
/- tactics can fail. indeed, it is the "failure" state that causes <|> to
backtrack and try the next tactic.

"try" combinator tries to build a tactic that always succeeds: 
try t executes t and reports success, even if t fails
it is equivalent to t <|> skip, where "skip" is a tactic that does nothing
-/
section
example (p q r : Prop) (hp : p) (hq : q) (hr : r) :
p ∧ q ∧ r :=
by split; try {split}; assumption

-- warning: "repeat {try t}" loops forever, since try t never fails.

-- one alternative to semicolons is the "all_goals" tactic

example (p q r : Prop) (hp : p) (hq : q) (hr : r) : p ∧ q ∧ r :=
begin
  split,
  -- succeeds if each application succeeds (hence the try, since it should not
  -- succeed in proving p)
  all_goals { try {split} },
  all_goals { assumption }
end

-- alternatively, any_goals
example (p q r : Prop) (hp : p) (hq : q) (hr : r) : p ∧ q ∧ r :=
begin
  split,
  -- tries split on all of them, and succeeds if at leat one goal succeeds
  any_goals { split },
  any_goals { assumption }
end


example (p q r : Prop) (hp : p) (hq : q) (hr : r) :
  p ∧ ((p ∧ q) ∧ r) ∧ (q ∧ r ∧ p) :=
begin
  repeat { any_goals {split }},
  all_goals { assumption }
end

example (p q r : Prop) (hp : p) (hq : q) (hr : r) :
  p ∧ ((p ∧ q) ∧ r) ∧ (q ∧ r ∧ p) :=
by repeat { any_goals {split <|> assumption} }
end

-- combinators focus and solve1 are opposites focus t ensures that t only
-- affects the current goal. so focus { all_goals {t} } does the same thing as
-- t. solve1 t is similar, but it fails unless t solves the goal entirely. the
-- "done" tactic directs the flow of control by succeeding if there are no goals
-- to be solved


-- 5.6. Rewriting

-- rewrite t, where t asserts some equality. t can be a hypthesis h : x = y, or
-- a general lemma, e.g. add_comm : ∀ x y, x + y = y = x, in which rewrite tries
-- to find substantiations of x and y; it can also be a compound term that
-- asserts a concrete or general equation. 

section
variables (f : ℕ → ℕ) (k : ℕ)

example (h₁ : f 0 = 0) (h₂ : k = 0) : f k = 0 :=
begin
  rw h₂,
  rw h₁
end 
end

-- can also rewrite with a compound expression

example (x y : ℕ) (p : ℕ → Prop) (q : Prop) (h : q → x = y) (h' : p y) (hq : q)
: p x :=
by { rw (h hq), assumption }

-- rw [t_1, ..., t_n] is shorthand for rewrite t_1, ..., rewrite t_n

section
variables (f : ℕ → ℕ) (a b k : ℕ)

example (h₁ : f 0 = 0) (h₂ : k = 0) : f k = 0 :=
by rw [h₂, h₁]

-- ←t instructs rw to use t backwards

example (h₁ : a = b) (h₂ : f a = 0) : f b = 0 :=
begin
  rw [←h₁, h₂]
end
end

-- sometimes the lhs of an identity can match more than one subterm in the goal
-- pattern, so rewrite chooses the first match. but you can specify arguments to
-- the hypotheses supplied to rw
example (a b c : ℕ) : a + b + c = a + c + b :=
begin
  rw [add_assoc, add_comm b, ←add_assoc]
end


-- by default, rewrite tactic only affects the goal. otherwise we can also ask
-- it to rewrite a given hypothesis h:
section
variables (f : ℕ → ℕ) (a : ℕ)

example (h : a + 0 = 0) : f a = f 0 :=
by { rw add_zero at h, rw h }

-- can also rewrite other terms
end
section
def tuple (α : Type*) (n : ℕ) := { l : list α // list.length l = n }

variables {α : Type*} {n : ℕ}

example (h : n = 0) (t : tuple α n) : tuple α 0 :=
begin
  rewrite h at t,
  exact t
end
end
-- 5.7 Using the simplifier


-- rewrite : "surgical tool" for manipulating a goal
-- simplifier : more powerful form of automation. identities that are tagged
-- with [simp] attribute are used to iteratively rewrite subterms in an expression

-- examples w natural numbers:
section
-- import data.nat.basic (done at top of file)
variables (x y z: ℕ) (p : ℕ → Prop)

variable (h : p (x * y))

example : (x + 0) * (0 + y * 1 + z * 0) = x * y :=
by simp

include h
example : p ((x + 0) * (0 + y * 1 + z * 0)) :=
by { simp, assumption }
end

-- examples with lists:
section
-- import data.list.basic (done at top of file)
variable {α : Type*}

open list

example (xs : list ℕ) :
  reverse (xs ++ [1, 2, 3]) = [3, 2, 1] ++ reverse xs :=
by simp

example (xs ys : list α) : 
  length (reverse (xs ++ ys)) = length xs + length ys :=
by simp [add_comm]
end

-- as with rw, can use "at" keyword to simplify a hypothesis

section 
variables (w x y z : ℕ) (p : ℕ → Prop)
example (h : p ((x + 0) * (0 + y * 1 + z * 0))) : p (x * y) :=
by { simp at h, assumption }

-- supports asterisks ("wildcard")

local attribute [simp] mul_comm mul_assoc mul_left_comm
local attribute [simp] add_assoc add_comm add_left_comm

example (h : p (x * y + z * w * x)) : p (x * w * z + y * x) :=
by { simp at *, assumption }

example (h₁ : p (1 * x + y)) (h₂ : p (x * z * 1)) : p (y + 0 + x) ∧ p (z * x) :=
by { simp at *, split; assumption }

example : x * y + z * w * x = x * w * z + y * x :=
by simp

-- things like commutativity might seem problematic, since repeatd application
-- causes looping. but the simplifier detects identities that permute their
-- arguments, and uses a technique known as ordered rewriting: this means that
-- there is an internal ordering of terms, and the identity is only applied if
-- the ordering is decreased. e.g. x + w + y is simplified to e.g. w + x + y but
-- not vice versa because the alphabetical order has lower ordering. 
end


-- this works similarly in algebraic structures like ringso

-- you can sen dsimp a list of facts to use, including genral lemmas, local
-- hypotheses, definitions to unfold, and compound expresisons. it doesn not
-- recognise the ←t syntax that rewrite does, so you need to use eq.symm
-- explicitly for an identity in the other direction
section
def f (m n : ℕ) : ℕ := m + n + m

example {m n : ℕ} (h : n = 1) (h' : 0 = m) : (f m n) = n :=
by simp [h, h'.symm, f]
end

section 
variables (f : ℕ → ℕ) (k : ℕ)

-- common: using local hypotheses
example (h₁ : f 0 = 0) (h₂ : k = 0) : f k = 0 :=
by simp [h₁, h₂]

-- use all local hypotheses, using *
-- this is different from simplifying all local hypotheses, using "simp at *"
example (h₁ : f 0 = 0) (h₂ : k = 0) : f k = 0 :=
by simp *

example (u w x y z : ℕ) (h₁ : x = y + z) (h₂ : w = u + x) : w = z + y + u :=
by simp[*, add_assoc, add_comm, add_left_comm]
end

-- it also does propositional rewriting (when they aren't hypotheses, but in the
-- goal) e.g. given a proof of p, the simplifier rewrites p ∧ q to q, and p ∨ q
-- to true, which is proved trivially
section
variables (p q r : Prop) 
example (hp : p) : p ∧ q ↔ q :=
by simp *

example (hp : p) : p ∨ q :=
by simp*
end

-- next example sipmlifies all hypotheses, and uses them to prove a goal

section
variables ( u w x x' y y' z : ℕ) (p : ℕ → Prop)

example (h₁ : x + 0 = x') (h₂ : y + 0 = y') :
  x + y + 0 = x' + y' := 
by { simp at *, simp * }
--  "simp at *" simplifies hypotheses. "simp *" simplifies the goal
end


-- simplifier's capabilities can grow as a library develops. e.g. suppose we
-- define a list operation that symmetrises its input by appending its reversal

section
-- import data.list.basic (top of file)
open list

variables {α : Type*} (x y z : α) (xs ys zs : list α)

def mk_symm (xs : list α) := xs ++ reverse xs

namespace worse
theorem reverse_mk_symm (xs : list α) :
  reverse (mk_symm xs) = mk_symm xs :=
by { unfold mk_symm, simp }
end worse
-- or, better:
namespace better
theorem reverse_mk_symm (xs : list α) :
  reverse (mk_symm xs) = mk_symm xs :=
by simp [mk_symm]

-- we can use this theorem to prove new results: 

example (xs ys : list ℕ) :
  reverse (xs ++ mk_symm ys) = mk_symm ys ++ reverse xs :=
by simp [reverse_mk_symm]

example (xs ys : list ℕ) (p : list ℕ → Prop)
  (h: p (reverse (xs ++ mk_symm ys))) : 
p (mk_symm ys ++ reverse xs)  :=
by simp [reverse_mk_symm] at h; assumption
end better
-- best: tag it as [simp] forever
namespace short
@[simp] theorem reverse_mk_symm (xs: list α) :
  reverse (mk_symm xs) = mk_symm xs :=
by simp [mk_symm]
end short

-- the above is short for 
namespace above
attribute [simp] 
theorem reverse_mk_symm (xs : list α) :
  reverse (mk_symm xs) = mk_symm xs :=
by simp [mk_symm]
end above

-- alternatively,

theorem reverse_mk_symm (xs : list α) :
  reverse (mk_symm xs) = mk_symm xs :=
by simp [mk_symm]
namespace below
attribute [simp] reverse_mk_symm
end below

example (xs ys : list ℕ) :
  reverse (xs ++ mk_symm ys) = mk_symm ys ++ reverse xs :=
by simp

example (xs ys : list ℕ) (p : list ℕ → Prop)
    (h : p (reverse (xs ++ (mk_symm ys)))) :
  p (mk_symm ys ++ reverse xs) :=
by simp at h; assumption
-- we can limit the scope of an attribute to the current file
local attribute [simp] reverse_mk_symm

-- can make own sets of simplifier rules, for special sitches


run_cmd mk_simp_attr `my_simps
-- this makes a new attribute [my_simps] 

attribute [my_simps] reverse_mk_symm

example (xs ys : list ℕ) :
  reverse (xs ++ mk_symm ys) = mk_symm ys ++ reverse xs :=
by simp with my_simps
-- adds all my_simps tagged thoerems to the list of theorems marked with [simp]
-- before applying simp

example (xs ys : list ℕ) (p : list ℕ → Prop)
  (h : p (reverse (xs ++ (mk_symm ys)))) :
    p (mk_symm ys ++ reverse xs) :=
by simp with my_simps at h; assumption

-- various simp options -- giving explicit list of rules, using at to specify
-- the location,a nd using "with" to add additional simplifier rules, can be
-- combined, but the order they are listed in is rigid (see docs for simp to see
-- this order)


-- additional modifiers that are useful. "simp without t" filters t and removes
-- it from the set of simplificatoin rules. "simp only" excludes all defaults. 
