-- 8.1 pattern matching
namespace one
open nat

def sub1 : ℕ → ℕ 
| zero     := zero
| (succ x) := x

def is_zero : ℕ → Prop
| zero     := true
| (succ x) := false

example : sub1 0 = 0 := rfl
example (x : ℕ) : sub1 (succ x) = x := rfl

example : is_zero 0 = true := rfl
example (x : ℕ) : is_zero (succ x) = false := rfl


example : sub1 7 = 6 := rfl
example (x : ℕ) : ¬ is_zero (x + 3) := not_false
end one

-- alternatively, we can use a more familiar notation
namespace two
open nat
def sub1 : ℕ → ℕ 
| 0 := 0
| (x + 1) := x

def is_zero : ℕ → Prop 
| 0 := true
| (x + 1) := false
end two

-- pattern matching works with any inductive type, such as products and option
-- types

namespace three
universes u v
variables {α : Type u} {β : Type v}

def swap_pair : α × β → β × α 
| (a, b) := (b, a)

def foo : ℕ × ℕ → ℕ
| (m, n) := m + n

def bar : option ℕ → ℕ 
| (some n) := n + 1
| none := 0

def bnot : bool → bool
| tt := ff
| ff := tt

theorem bnot_bnot : ∀ (b : bool), bnot (bnot b) = b
| tt := rfl
| ff := rfl
end three

-- can de-struct inductively defined propositions

namespace three
example (p q : Prop) : p ∧ q → q ∧ p 
| ⟨h₁, h₂⟩ := ⟨h₂, h₁⟩

example (p q : Prop) : p ∨ q → q ∨ p
| (or.inl hp) := or.inr hp
| (or.inr hq) := or.inl hq
end three

-- so far we used pattern matching to carry out a single case distinction

namespace four
open nat

def sub2 : ℕ → ℕ 
-- first splits cases based on whether input is of the form zero or succ x 
| zero            := 0
-- then splits based on whether x is of the form zero or succ a
| (succ zero)     := 0
| (succ (succ a)) := a

-- we can also use more familiar symbols
def sub2' : ℕ → ℕ 
| 0       := 0
| 1       := 0
| (a + 2) := a

-- now these hold definitionally
example : sub2' 0 = 0 := rfl
example : sub2' 1 = 0 := rfl
example (a : nat) : sub2'(a + 2) = a := rfl

example : sub2' 5 = 3 := rfl

#print sub2'._main 

-- more examples of nested pattern matching
example {α : Type*} (p q : α → Prop) :
(∃ x, p x ∨ q x) → (∃ x, p x) ∨ (∃ x, q x)
| (exists.intro x (or.inl px)) := or.inl (exists.intro x px)
| (exists.intro x (or.inr qx)) := or.inr (exists.intro x qx)

def foo : ℕ × ℕ → ℕ
| (0, n) := 0
| (m + 1, 0) := 1
| (m + 1, n + 1) := 2
 
-- perhaps this is better than the previous foo:

def foo' : ℕ → ℕ → ℕ 
| 0       n       := 0
| (m + 1) 0       := 1
| (m + 1) (n + 1) := 2

-- another example

def bar : list ℕ → list ℕ → ℕ
| []       []       := 0
| (a :: l) []       := a
| []       (b :: m) := b
| (a :: l) (b :: m) := a + b

def band : bool → bool → bool 
| tt a := a
| ff _ := ff
-- _ is wildcard

def bor : bool → bool → bool
| tt _ := tt
| ff a := a

def {u} cond {α : Type u} : bool → α → α → α 
| tt x y := x
| ff x y := y

-- parameters placed before the : are not matched
def tail1 {α : Type*} : list α → list α 
| []      := []
| (h :: t) := t

-- if placed after, they are matched
def tail2 : Π {α : Type*}, list α → list α 
| α []    := []
| α (h :: t) := t
end four

-- 8.2 : wildcards and overlapping patterns

-- if two patterns overlap, then the first is matched (like a switch-case
-- statement?)

namespace five
def foo : ℕ → ℕ → ℕ 
-- matches (0, 0), and (0, anything > 0)
| 0 n := 0
-- matches (anything > 0, 0)
| m 0 := 1
-- matches (anything > 0, anything > 0)
| m n := 2


-- thus the following equations hold definitionally

variables m n : ℕ

example: foo 0       0       = 0 := rfl
example: foo 0       (n + 1) = 0 := rfl
example: foo (m + 1) 0       = 1 := rfl
example: foo (m + 1) (n + 1) = 2 := rfl

-- since we don't use the values of m and n, we can use wildcard patterns

def foo' : ℕ → ℕ → ℕ 
| 0 _ := 0
| _ 0 := 1
| _ _ := 2

example: foo' 0       0       = 0 := rfl
example: foo' 0       (n + 1) = 0 := rfl
example: foo' (m + 1) 0       = 1 := rfl
example: foo' (m + 1) (n + 1) = 2 := rfl
end five

-- some functional programming languages support /incomplete patterns/. in these
-- languages, the interpreter produces an excpetion or returns an arbitrary
-- value for incomplete cases. we can simulate the arbitrary value approach
-- using the inhabited type class. roughly, an element of inhabited α is a
-- witness to the fact that there is an element of α. 


-- there is an "arbitrary" type of any inhabited type

namespace six
def f1 : ℕ → ℕ → ℕ 
| 0 _ := 1
| _ 0 := 2
| _ _ := arbitrary ℕ 

variables a b : ℕ

example : f1 0     0     = 1 := rfl
example : f1 0     (a+1) = 1 := rfl
example : f1 (a+1) 0     = 2 := rfl
example : f1 (a+1) (b+1) = arbitrary nat := rfl

-- or: use option α 

def f2 : ℕ → ℕ → option ℕ
| 0 _ := some 1
| _ 0 := some 2
| _ _ := none

example : f2 0     0     = some 1 := rfl
example : f2 0     (a+1) = some 1 := rfl
example : f2 (a+1) 0     = some 2 := rfl
example : f2 (a+1) (b+1) = none   := rfl

-- if you leave out any cases, the equation compiler will tell you!

def bar : ℕ → list ℕ → bool → ℕ 
| 0      _         ff := 0
| 0      (b :: _)  _  := b
| 0      []        tt := 7
| (a+1)  []        ff := a
| (a+1)  []        tt := a + 1
| (a+1)  (b :: _)  _  := a + b


-- also does conditional (if-then-else) instead of cases in appropriate situations
def foo : char → ℕ 
| 'A' := 1
| 'B' := 2
| _   := 3

#print foo._main
end six


-- 8.3 Structural Recursion and Induction

/- equation compiler also supports recursive definitions. next three sections: 

   - structurally recursive definitions
   - well-founded recursive definitions
   - mutually recursive definitions 
generally it processes inputs of the form

def foo (a ; α) : Π (b : β), γ
| [patterns₁] := t₁
...
| [patternsₙ] := tₙ

a is a sequence of parameters
b is a sequence of arguments on which pattern matching takes place
γ is any type, which can depend on a and b

each line should contain the same number of patterns, one for each element of β
pattern is either a variable, a constructor applied to other patterns, or
an expression that normalises to something of that form

constructor appearance prompts case splits

in section 8.6 : "inaccessible terms", sometimes necessary to include explicit
terms in patterns. but we do not encounter these until section 8.6

t₁, ..., tₙ can make use of any of the parameters a, as well as any of the
variables that are introduced in corresponding patterns. but: also can 
have references to `foo`. 

this section: structural recursion, where argumetns to foo on the RHS are
subterms of the patterns on the LHS (i.e. arguments to constructors). idea is
that they are structurall smaller, so they  appear in the inductive type at an
earlier stage. 

examples: 
-/
namespace six 
open nat
def add : nat → nat → nat
| m zero     := m
| m (succ n) := succ (add m n)

local infix (name :=add) ` + ` := add

theorem add_zero (m : nat) : m + zero = m := rfl
theorem add_succ (m n : nat) : m + succ n = succ(m + n) := rfl

theorem zero_add : ∀ n, zero + n = n
| zero     := rfl
| (succ n) := congr_arg succ (zero_add n)

def mul : nat → nat → nat
| n zero     := zero
| n (succ m) := (mul n m) + n

/-
equation compiler tries to make sure that the defining equations hold
definitionally; i.e. we can use "refl" to prove them. 
however, sometimes they only hold propositionally: they are equational
theorems that must be applied explicitly. the equation compiler generates
such theorems internally. they are not meant to be used by the user; rather,
simp and rewrite are configured to use them where necessary. 
-/
end six

namespace seven
open nat
def add : nat → nat → nat
| m zero     := m
| m (succ n) := succ (add m n)

local infix (name :=add) ` + ` := add

theorem zero_add : ∀ n, zero + n = n 
| zero     := by simp [add]
| (succ n) := by simp [add, zero_add n]

/-
there is a `dsimp` tactic, that performs definitional reductions only. this 
can be used to carry out the first step. 
-/

theorem zero_add' : ∀ n, zero + n = n
| zero     := by dsimp [add]; reflexivity
| (succ n) := by dsimp[add]; rw [zero_add n]
end seven

/- 
as with definition by pattern matching, parameters to a structural 
recursion or induction may appear before the colon. such parameters
are simply added to the local context before the definition is
processed. e.g. the definition of addition may also be written
as follows:
-/
namespace eight
open nat
def add (m : ℕ) : ℕ → ℕ
| zero  := m
| (succ n) := succ (add n)
end eight


-- more interesting example of structural recursion is given by 
-- the fibonacci function `fib`

namespace nine
def fib : nat → nat
| 0 := 1
| 1 := 1
| (n+2) := fib (n+1) + fib(n)
-- bad recursive definition; for fib(n) it needs to calculate 
-- fib(n-1) and fib(n-2), and so on. this is bad. 

example : fib 0 = 1 := rfl
example : fib 1 = 1 := rfl
example (n : nat) : fib (n + 2) = fib (n + 1) + fib n := rfl

example : fib 7 = 21 := rfl
example : fib 7 = 21 := 
begin
  dsimp [fib], 
  refl 
end
end nine

namespace ten
def fib_aux : nat → nat × nat
| 0       := (0, 1)
| (n + 1) := let p := fib_aux n in (p.2, p.1 + p.2)
-- this stores both the current and the next answer;
-- thus the next one stores the .2 of the current, and so on
-- this has complexity linear in n 

def append {α : Type*} : list α → list α → list α
| []       l := l
| (h :: t) l := h :: append t l 

example: append [(1 : ℕ), 2, 3] [4, 5]  = [1, 2, 3, 4, 5] := rfl
end ten


-- 8.4: Well-founded recursion and induction
namespace eleven
universe u
variable α : Sort u
variable r : α → α → Prop

#check acc r
#check well_founded r
end eleven

-- given x, acc r x is equivalent to: 
-- ∀ y, r y x → acc r y 
-- in infix notation, if y `r` x, then acc r x implies acc r y. that is, 
-- if you think of r as denoting an order relation <, then acc r x says 
-- that x is accessible from below, in the sense that all its
-- predecessors are accessible from below. the statement that r is
-- well-founded, denoted `well_founded r`, is exactly the statement that
-- every element of th etype is accessible. 

-- at the end you have the r-minimum elements, which are vacuously
-- accessible from below, since they do not have any predecessors.

-- thus if there is no end to a chain of elements, then there is no place to
-- start building proofs of accessibility from (e.g. negative integers {-1, -2,
-- -3, ..} w.r.t the order relation <

-- thus if r is a well-founded relation on a type α, then we should have 
-- a principle of well-founded recursion on α, with respect to the
-- relation r. and the standard library defines well_founded.fix, which
-- serves exactly that purpose

namespace twelve
universes u v
variable α : Sort u
-- binary relation on α
variable r : α → α → Prop
-- the statement that all variables are accessible from below
variable h : well_founded r

variable C : α → Sort v
-- a function, given x : α, and given a C y for each y that precedes x, 
-- returns C x
variable F : Π x, (Π (y: α), r y x → C y) → C x

-- use F to define a function f, using our proof that r is well-founded
def f : Π (x : α) , C x := well_founded.fix h F


-- lean knows that the usual order < on the natural numbers is well-founded
-- it also knows some ways of constructing new well-founded orders from others,
-- e.g. using lexicographic order
end twelve

-- definition of division in standard library (in essence) is the following

namespace thirteen
open nat

def div_rec_lemma {x y : ℕ} : 0 < y ∧ y ≤ x → x - y < x :=
λ h, nat.sub_lt (lt_of_lt_of_le h.left h.right) h.left
-- don't look at this proof because it uses an equally obvious lemma 

-- given x, and given a division function for all predecessors of x, 
-- a definition of division of x by some variable
def div.F (x : ℕ) (f : Π x₁, x₁ < x → ℕ → ℕ)  (y : ℕ) : ℕ :=
if h : 0 < y ∧ y ≤ x then
  f (x - y) (div_rec_lemma h) y + 1
  -- use the division function by showing x - y is a predecessor of x
else
  zero
  
-- use recursion: because < is well-founded, we can recursively define 
-- "f" using F. 
def div := well_founded.fix lt_wf div.F
-- lt_wf is a proof of well_founded lt
end thirteen

namespace fourteen
def div : ℕ → ℕ → ℕ
| x y :=
  if h : 0 < y ∧ y ≤ x then
    have x - y < x, from nat.sub_lt (lt_of_lt_of_le h.left h.right) h.left,
  div (x - y) y + 1
  else 0
  
-- equation compiler first tries structural recursion
-- and if that fails, it tries well-founded recursion
-- it tries the lexicographic ordering on the pair (x, y). 
-- thus we have to tell it that x - y < x, to prompt it to
-- use the ordering <.
-- defining equation for div does /not/ hold definitionally, 
-- but it is available to rewrite and simp
-- simplifier will loop indefinitely, but rw applies it once

example (x y : nat) : div  x y = if 0 < y ∧ y ≤ x then div (x -y) y + 1 else 0
:= by { rw [div] }

example (x y : nat) (h : 0 < y ∧ y ≤ x) : 
div x y = div (x - y) y + 1  :=
by rw [div, if_pos h]
end fourteen

-- similar: converts natural number to binary expression.
-- we have to provide the equation compiler with evidence
-- that the recursive call is decreasing; which we do here
-- with a `sorry`. this does not prevent the bytecode evaluator from evaluating
-- the function successfully 

namespace fifteen
def nat_to_bin : ℕ → list ℕ 
| 0       := [0]
| 1       := [1]
| (n + 2) := 
  have (n + 2) / 2 < n + 2, from sorry,
    nat_to_bin ((n + 2) / 2) ++ [n % 2]

-- even thoguh we use sorry, we can still use the function 

#eval nat_to_bin 1234567
end fifteen
