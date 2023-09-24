-- relative paths: 

import .foo ..bar.baz

-- above command imports ./foo.lean and ../bar/baz.lean
-- importing is transitive

-- 6.2. More on Sections


-- variables by default only included as arguments of functions that refer to
-- them, but we can forcefully include them using "include" command

-- "omit" undoes includes 

-- variables : like saying x varies over natural numbers
-- parameter : like saying x is a fixed natural number in this section. 


section
parameters {α : Type*} (r : α → α → Prop)
parameter transr : ∀ {x y z}, r x y → r y z → r x z

variables {a b c d e : α}

theorem t1 (h₁ : r a b) (h₂ : r b c) (h₃ : r c d) : r a d :=
transr (transr h₁ h₂) h₃

theorem t2 (h₁ : r a b) (h₂ : r b c) (h₃ : r c d) (h₄ : r d e) : r a e :=
transr h₁ (t1 h₂ h₃ h₄)

-- it's like r and trans are constants here. i.e. t1 is an abbrev for t1 α r
-- transr 

#check t1
#check t2
end

-- now they the parameters are variables again 

#check t1

#check t2

-- identifiers are given hierarchical names like foo.bar.baz 
-- "namespace foo" prepends foo to every definition/theorem until end is
-- encountered, but  we can also do this:

def foo.bar : ℕ := 1

open foo

#check bar

#check foo.bar



-- 6.5 More on Implicit Arguments
-- if we have term t of the type Π {x : α}, β x, then curly brackets indicate x
-- is an implicit argument to t. i.e. t is replaced by @t _. to prevent this,
-- write @t.

-- implicit arguments are inserted eagerly. suppose we have
section
def f (x : ℕ) {y : ℕ} (z : ℕ) : ℕ  :=  sorry
#check f 
#check f 7 
-- it automatically inserts a placeholder for y, so only z is expected
end

-- instead: ⦃, ⦄ brackets

section
def f (x : ℕ) ⦃y : ℕ⦄ (z : ℕ) : ℕ  :=  sorry
#check f
#check f 7
#check f 7 3
end

namespace hidden
variables {α : Type*} (r : α → α → Prop)

definition reflexive : Prop := ∀ (a : α), r a a
definition symmetric : Prop := ∀ {a b : α}, r a b → r b a
definition transitive : Prop := ∀ {a b c : α}, r a b → r b c → r a c
definition euclidean : Prop := ∀ {a b c : α}, r a b → r a c → r b c


variable {r}

theorem th1 (reflr : reflexive r) (euclr : euclidean r) : symmetric r :=
assume a b : α, assume : r a b,
show r b a, from euclr this (reflr _)

theorem th2 (symmr : symmetric r) (euclr : euclidean r) : transitive r := sorry

namespace bad
theorem th3 (reflr : reflexive r) (euclr : euclidean r) :
  transitive r :=
th2 (th1 reflr euclr) euclr
end bad
-- here, euclr is expected to have type euclidean (something), since r
-- is inferred from the arguments by th1. however, euclr is expanded
-- from euclidean r, i.e. ∀ a b : α, r a b → r a c → ∀ b c to r
-- something1 something2 → r something1 something3 → r something2
-- something3 because lean eagerly inserts implicit arguments. 

namespace works
theorem th3 (reflr : reflexive r) (euclr : euclidean r) : transitive r
:=
@th2 _ _ (@th1 _ _ reflr @euclr) @euclr
#check th3
end works
-- now no implicit substitution is made, all types are inferred from reflr
end hidden

-- 6.7 Coercions

section coercions
variables m n : ℕ
variables i j : ℤ 

#check i + m
#check i + m + j 
#check i + m + n 

-- there is a funcition int.of_nat that embeds natural numbers into
-- integers and this is shown using the ↑ symbol. ascii: coe 

#check (coe m : ℤ)

-- when order is different, we need to insert the arrow manually, since
-- lean only parses forward, so it does not know the expected type until
-- it has parsed the earlier arguments

#check ↑m + i
-- this gives an error: 
end coercions

-- 6.8 Displaying Information
-- for types, use "check", and "@" to make everything explicit
#check eq
#check @eq 
#check eq.symm
#check @eq.symm

#print eq.symm

#check and
#check and.intro
#check @and
#check @and.intro
#print inductive and 
#print notation ∧  
#print inductive group

-- 6.9 Setting options
#check (λ x, x + 1) 1

set_option pp.beta true
#check (λ x, x + 1) 1
