-- enumerated type, where the constructors are just labels

inductive weekday : Type
| sunday : weekday
| monday : weekday
| tuesday : weekday
| wednesday : weekday
| thursday : weekday
| friday : weekday
| saturday : weekday


#check weekday.sunday

open weekday
#check sunday

def f (day : weekday) : ℕ := 
  weekday.rec_on (by assumption) 7 6 5 4 3 2 1
#reduce f monday 

-- operations for boolean types

namespace hidden

inductive bool: Type
| ff : bool
| tt : bool

end hidden

def bool_and (b1 : bool) (b2 : bool) : bool :=
  bool.cases_on b1 ff b2 

def bool_or (b1 : bool) (b2 : bool) : bool :=
  bool.cases_on b1 b2 tt

def bool_imp (b1 : bool) (b2 : bool) : bool :=
  bool.cases_on b1 tt b2 

def bool_iff (b1 : bool) (b2 : bool) : bool :=
  b1 = b2 
  
def bool_not (b1 : bool) : bool :=
  bool.cases_on b1 tt ff
  

-- 7.2 Constructors with Arguments

-- more general than enumerated types,

universes u v
namespace hidden

inductive prod (α : Type u) (β : Type v) 
| mk : α → β → prod

-- sum type α ⊕ β (~ disjoint union)
inductive sum (α : Type u) (β : Type v)
| inl : α → sum
| inr : β → sum

-- to define a function on prod α β, we have to assume the input is of the form
-- prod.mk a b, and we have to specify the output, in terms of a and b. 

end hidden

def fst {α : Type u} {β : Type v} (p : α × β) : α :=
prod.rec_on p (λ (a : α) (b : β), a)

def prod_example (p : bool × ℕ) : ℕ :=
prod.rec_on p (λ b n, cond b (2 * n) (2 * n + 1))

#reduce prod_example (tt, 3)
#reduce prod_example (ff, 3)
-- by contrast, sum has two constructors, inl and inr, for "insert left" and
-- "insert right"

def sum_example (s : ℕ ⊕ ℕ) : ℕ :=
sum.cases_on s (λ n, 2 * n ) (λ n, 2 * n + 1)

#reduce sum_example (sum.inl 3)
#reduce sum_example (sum.inr 3)

-- types α and β are arguments for prod as well as for the constructor prod.mk,
-- but these are inferr-able for the latter, and lean automatically makes them
-- implicit

-- prod has one constructor with multiple arguments and is purely conjunctive.
-- constructor with multiple args introduces conjunctive information,
-- from prod.mk a b : prod α β, we can extract both a and b. 

-- we can have named arguments, as with function definitions

namespace hidden
inductive prod (α : Type u) (β : Type v)
| mk (fst : α) (snd : β) : prod


inductive sum (α : Type u) (β : Type v)
| inl {} (a : α) : sum
| inr {} (b : β) : sum

-- these definitions are essentially the same ones as earlier
-- the {} annotates the parameters α and β. 
end hidden


-- prod has one constructor, thus is purely conjunctive. it simply packs the
-- arguments into a single piece of data, where the type of subsequent arguments
-- can depend on the type of the initial argument. we can also think of such a
-- type as a "record" or a "structure" 

namespace hidden
structure prod (α β : Type*) :=
mk :: (fst : α) (snd : β)
end hidden

-- this introduces the inductive type, its constructor, eliminators (rec,
-- rec_on), and the projections fst and snd

structure color := (red : nat) (green : nat) (blue : nat)

-- this uses mk as a default

def yellow := color.mk 255 255 0
#reduce color.red yellow
-- taking a projection

structure Semigroup := 
(carrier : Type u) (mul : carrier → carrier → carrier) (mul_assoc: ∀ a b c, mul
(mul a b) c = mul a (mul b c))
-- this is basically a tuple with named indices
-- also subsequent types depend on the initial type, so this would be a Pi type
#check Semigroup.mk


-- sigma types are inductive
namespace hidden
inductive sigma {α : Type u} {β : α → Type v}
| dpair : Π a : α, β a → sigma
-- so if the object is a Sigma-type, its constructor is a Pi-type
end hidden

-- no such thing as partial function in semantics of dependent type theory
-- every function f : α → β  or f : (Π x : α, β (x)) is assumed to have a value
-- at every input

namespace hidden

-- basically like a union of α with a placeholder type
inductive option (α : Type*)
| none {} : option
| some : α → option
-- thus f : α → option β is a partial function from α to β .

inductive inhabited (α : Type*)
| mk : α → inhabited 

-- an element of inhabited α is a witness to the fact that there is an element
-- of α. it is an example of a type class; lean can be instructed if suitable
-- base types are inhabited, then construced types are inhabited on that basis
end hidden

-- 7.3 inductively defined propositions

namespace hidden
inductive false : Prop

-- we can introduce true but not false
-- because true is true, so it can be inhabited
inductive true : Prop
| intro : true

inductive and (a b : Prop) : Prop
| intro : a → b → and

inductive or (a b : Prop) : Prop
| intro_left : a → or
| intro_right : b → or

inductive Exists {α : Type*} (q : α → Prop) : Prop
| intro : ∀ (a : α) , q a → Exists


-- false, true, and, and or are analogous to definitions of empty, unit, prod,
-- and sum

-- first group yields elements of Prop, and second group yields elements of Type
-- u for some u. similarly, ∃ x : α, p is a prop-valued variiant of Σ x : α, p. 

inductive subtype {α : Sort u} (p : α → Prop) : Sort u 
| mk : Π x : α, p x → subtype

-- this is a Type, not a Prop! but it is otherwise similar to exists 
end hidden

-- notation { x : α // p x} is a syntactic sugar for subtype (λ x : α, p x). it
-- is modeled after subset notation in set theory. 


-- 7.4 Defining the natural numbers
namespace hidden
inductive nat : Type
| zero : nat
| succ : nat → nat
end hidden

-- every natural number is either zero, or the successor of a natural
-- number. nat is the "smallest" type with these constructors, meaning
-- that it is exhaustively and freely generated by starting with zero
-- and applying succ repeatedly. succ could have fixed points though?
-- what if succ (zero) = zero? isn't {zero} the smallest type?

#check @nat.cases_on 
#check @nat.rec_on

-- thus non-enumerated types have difference between rec_on and
-- cases_on; i.e. that rec_on provides the value of the function on the
-- input of the constructor as an argument (e.g. λ n, add_m_n below) vs
-- just hthe input of the constructor (would be just λ n)


-- Π {C : nat → Type*} (n : nat), C nat.zero → (Π (a : nat), C a →
-- C(nat.succ a)) → C n

-- here, motive nat.zero is some type : Sort u_1
-- thus it expects a term of that type. this is the type of output of
-- the overall expression if given the input zero. 
-- imilarly otive n and motive (nat.succ n) are also some types
-- if the function is NOT of dependent type, motive is a constant function

-- here n is the Major Premise
-- and the successor lambdas are Minor Premises


-- e.g. Addition on natural numbers

namespace hidden
namespace nat
def add (m n : nat) : nat :=
nat.rec_on n m (λ k add_m_k, nat.succ add_m_k)
#reduce add (succ zero) (succ (succ zero))

instance : has_zero nat := has_zero.mk zero
instance : has_add nat := has_add.mk add

theorem add_zero (m : nat) : m + 0 = m := rfl
theorem add_succ (m n : nat) : m + succ n = succ (m + n) := rfl
-- had_zero and has_add are inductive types ? instance command explained
-- in chapter 10
end nat
end hidden
open nat

theorem zero_add1 (n : ℕ) : 0 + n = n :=
nat.rec_on n 
  (show 0 + 0 = 0, from rfl)
  (assume n, assume ih : 0 + n = n, 
    show 0 + succ n = succ n, from
      calc 0 + succ n = succ (0 + n) : rfl
      -- 0 + succ n is defined to be succ (0 + n
                  ... = succ n : by rw ih)

theorem zero_add2 (n : ℕ) : 0 + n = n :=
nat.rec_on n rfl (λ n ih, by rw [add_succ, ih])


theorem zero_add3 (n : ℕ) : 0 + n = n :=
nat.rec_on n rfl (λ n ih, by simp only [add_succ, ih])

theorem add_assoc (m n k : ℕ) : m + n + k = m + (n + k) :=
nat.rec_on k 
  (show m + n + 0 = m + (n + 0), from rfl)
  (assume k,
    assume ih : m + n + k = m + (n + k),
    show m + n + succ k = m + (n + succ k), from
      calc
      m + n + succ k = succ (m + n + k)   : rfl
                 ... = succ (m + (n + k)) : by rw ih
                 ... = m + succ (n + k)   : rfl
                 ... = m + (n + succ k)   : rfl)
                 
theorem add_assoc' (m n k : ℕ) : m + n + k = m + (n + k) :=
nat.rec_on k rfl (λ k ih, by simp only [add_succ, ih])

theorem succ_add (m n : ℕ) : succ m + n = succ (m + n) :=
nat.rec_on n
  (show succ m + 0 = succ (m + 0), from rfl)
  (assume n,
    assume ih : succ(m) + n = succ(m + n),
    show succ m + succ n = succ (m + succ n), from 
      calc 
        succ m + succ n = succ (succ m + n )    : rfl
                    ... = succ (succ (m + n))   : by rw ih
                    ... = succ(m + succ n)      : rfl)

theorem add_comm (m n : ℕ) : m + n = n + m :=
nat.rec_on n
  (show m + 0 = 0 + m, by rw [nat.zero_add, nat.add_zero])
  (assume n, assume ih : m + n = n + m,
    calc 
      m + succ n = succ (m + n) : rfl
             ... = succ (n + m) : by rw ih
             ... = succ n + m   : by rw [nat.succ_add])

theorem add_assoc'' (m n k : ℕ) : m + n + k = m + (n + k) :=
nat.rec_on k rfl (λ k ih, by simp only [add_succ, ih])

-- 7.5 Other Recursive Data Types

namespace hidden
inductive list (α : Type*)
| nil {} : list
| cons : α → list → list

namespace list

variable {α : Type*}

notation (name := cons) h :: t := cons h t

def append (s t : list α) : list α :=
list.rec_on s t (λ (x : α) (s_tail : list α) (append_s_tail_t : list α), x :: append_s_tail_t)

notation (name := append) s ++ t := append s t

theorem nil_append (t : list α) : nil ++ t = t := rfl

theorem cons_append (x : α) (s t : list α) : x::s ++ t = x::(s ++ t) := rfl

-- notation (name := list) `[` l:(foldr `,` (h t, cons h t) nil) `]` := l

end list
end hidden
namespace meow'
variable {α : Type*}

inductive binary_tree
| leaf : binary_tree
| node : binary_tree → binary_tree → binary_tree
end meow'

inductive cbtree
| leaf : cbtree
| sup : (ℕ → cbtree) → cbtree 

namespace cbtree

def succ (t : cbtree) : cbtree :=
 sup (λ n, t)
 
def omega : cbtree :=
sup (λ n, nat.rec_on n leaf (λ n t, succ t))
 
end cbtree

-- 7.6 Tactics for Inductive Types

-- cases tactic works for inductively defined types
-- it decomposes elements in terms of each of the possible constructors

open nat
variable p : ℕ → Prop

example (hz : p 0) (s : ∀ n, p (succ n)) : ∀ n, p n :=
begin
  intro n,
  cases n with predn,
  -- case: n = 0
  exact hz,
  -- case: n = succ(predn) for predn : ℕ
  exact s predn
end

example (n : ℕ) (h : n ≠ 0) : succ (pred n) = n :=
begin
  cases n with m,
  { contradiction },
  refl
end

def f' (n : ℕ) : ℕ :=
begin
  cases n, exact 3, exact 7
end

example : f' 0 = 3 := rfl
example : f' 5 = 7 := rfl

namespace meow
def tuple (α : Type*) (n : ℕ) := { l : list α // list.length l = n }

variables {α : Type*} {n : ℕ}

def f {n : ℕ} (t : tuple α n) : ℕ :=
begin
  cases n, exact 3, exact 7
end

def my_tuple : tuple ℕ 3 := ⟨[0, 1, 2], rfl⟩

example : f my_tuple = 7 := rfl
end meow

namespace foobar
inductive foo : Type
| bar1 : ℕ → ℕ → foo
| bar2 : ℕ → ℕ → ℕ → foo

def silly (x : foo) : ℕ :=
begin
  cases x with a b c d e,
  exact b,
  exact e
end

-- "with" keyword confusing. so instead we have: 

def silly' (x : foo) : ℕ :=
begin
  cases x,
    case bar1 : a b
      { exact b },
    case bar2 : c d e
      { exact e }
end

-- can also match in other order:
def silly'' (x : foo) : ℕ :=
begin
  cases x,
    case bar2 : c d e
      { exact e },
    case bar1 : a b
      { exact b }
end
end foobar
-- can split on general expression of an inductive type

example (hz : p 0) (hs : ∀ n, p (succ n)) (m k : ℕ) : p (m + 3 * k) :=
begin
  -- like saying generalize : m + 3 * k = n, cases n
  cases m + 3 * k,
  { exact hz },
  apply hs
end


example (hz : p 0) (hs : ∀ n, p (succ n)) (m k : ℕ) : p (m + 3 * k) :=
begin
  generalize : m + 3 * k = n, 
  -- this replaces m + 3 * k in the goal but not hypothesis
  -- to generalise in hypotheses, revert, generalise, intro
  cases n,
  { exact hz },
  apply hs
end


example (p : Prop) (m n : ℕ)
  (h₁ : m < n → p) (h₂ : m ≥ n → p) : p :=
begin
  cases lt_or_ge m n with hlt hge,
  -- this uses "have" to put the expression into the environment
  exact h₁ hlt,
  exact h₂ hge
end

-- this is functionally equivalent to:

example (p : Prop) (m n : ℕ)
  (h₁ : m < n → p) (h₂ : m ≥ n → p) : p :=
begin
  have h : m < n ∨ m ≥ n, from lt_or_ge m n,
  cases h with hlt hge,
    exact h₁ hlt,
  exact h₂ hge
end

#check nat.sub_self

#check decidable.em

example (m n : ℕ) : m - n = 0 ∨ m ≠ n :=
begin
  cases decidable.em (m = n) with heq hne,
  { rw heq,
    left, exact nat.sub_self n },
  right, exact hne
end

namespace new
def f (m k : ℕ) : ℕ :=
begin
  cases m - k, exact 3, exact 7
end

example : f 10 2 = 7 := rfl
example : f 5 7 = 3 := rfl
end new

-- induction tactic lets you carry out proofs by induction

theorem zero_add (n : ℕ) : 0 + n = n :=
begin
  induction n with n ih,
    refl,
  rw [add_succ, ih]
end

theorem zero_add' (n : ℕ) : 0 + n = n :=
begin
  induction n,
  case zero : { refl },
  case succ : n ih { rw [add_succ, ih]}
end

#check add_succ

theorem succ_add'' (m n : ℕ) : succ m + n = succ (m + n) :=
begin
  induction n,
  case zero : { refl },
  case succ : n ih { rw [add_succ, add_succ, ih] }
end

theorem add_comm' (m n : ℕ) : m + n = n + m :=
begin
  induction n,
  case zero : { rw zero_add, refl },
  case succ : n ih { rw [add_succ, ih, succ_add] }
  -- name before colon is the constructor of associated type name after
  -- can appear in any order; colon can be omitted if there are no
  -- parameters to name (e.g. in zero). one liners follow:
end

theorem zero_add'' (n : ℕ) : 0 + n = n := 
by induction n; simp only [*, nat.add_zero, nat.add_succ]


theorem decidable_em (m n : ℕ) : m = n ∨ m ≠ n :=
begin
  induction n with n ih,
  induction m with m ih,
  { left, refl },
  { cases ih, right, sorry  },
  sorry
end

-- one last tactic: injection tactic
-- the constructors are injective since we assume each term of a type
-- has exactly one way to construct it from the constructors.

open nat
example (m n k : ℕ) (h : succ (succ m) = succ (succ n)) : 
n + k = m + k :=
begin
  injection h with h',
  injection h' with h'',
  rw h''
end

-- inductive families

-- α is behind
inductive vector (α : Type u) : nat → Type u
| nil {} : vector zero
| cons {n : ℕ} (a : α) (v : vector n) : vector (succ n)


namespace hidden
inductive eq {α : Sort u} (a : α) : α → Prop
| refl [] : eq a
set_option pp.all true
variable α : Sort u
variables a b : α
variable f : α → Sort u
variable t : f a
#check @eq.rec_on.{u u} 
-- thus refl is of type eq a a
-- the first a is implicit
-- only way to constructo a proof of eq a x is to use reflexivity

@[elab_as_eliminator]
theorem subst {α : Type u} {a b : α} {p : α → Prop} 
  (h₁ : eq a b) (h₂ : p a) : p b :=
eq.rec h₂ h₁ 

theorem trans {α : Type u} {a b c : α}
  (h₁ : eq a b) (h₂ : eq b c) : eq a c :=
-- motive: (λ x : α, (t : x = c))
-- first input is of type a = b
-- second input is of type motive b 
-- output is of type motive a
eq.rec_on h₂ h₁ 

theorem congr {α β : Type u} {a b : α} (f : α → β)
  (h : eq a b) : eq (f a) (f b) :=
eq.rec_on h (eq.refl (f a))
end hidden

-- 7.8 Axiomatic Details
mutual inductive even, odd
with even : ℕ → Prop
| even_zero : even 0 
-- thus even_zero is a proof that 0 is even
-- even_zero is an term of type even 0, which is a term of type Prop 
| even_succ : ∀ n, odd n → even (n + 1)  
-- even_succ is a proof of the proposition  (∀ n, n + 1 is even if n is odd)
-- this proposition is a Pi-type as per uzhe
with odd : ℕ → Prop
| odd_succ : ∀ n, even n → odd (n + 1)
-- like even

-- universe u

namespace hidden
mutual inductive tree, list_tree (α : Type u)
with tree : Type u
| node : α → list_tree → tree
with list_tree : Type u
| nil {} : list_tree
| cons   : tree → list_tree → list_tree
end hidden

-- this is inconvenient because list_tree is an isomorphic type to list tree,
-- which already exists. but lean lets us do this: 

inductive tree (α : Type u)
| mk : α → list tree → tree
-- this is a nested inductive type. this is compiled down to the inductive type
-- described above, which is compiled down to an ordinary inductive type. it
-- builds the appropriate isomorphisms (between list_tree α and list (tree α),
-- and defines constructors of tree in terms of the isomorphism
