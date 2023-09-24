namespace one
structure point (α : Type*) := 
mk ::  (x : α) (y : α) 

-- #print prefix point #reduce point.x (point.mk 10 20)
#reduce point.y (point.mk 10 20)

open point

example (α : Type*) (a b : α) : x (mk a b) = a := rfl
example (α : Type*) (a b : α) : y (mk a b) = b := rfl

def p := point.mk 10 20
#check p.x
#reduce p.x
#reduce p.y

-- if constructor is not provided, it is mk by default

-- object constructor notation

#check { point . x := 10, y := 20 }
#check { point . y := 20, x := 10 }
#check ({x := 10, y := 20} : point nat)

structure my_struct := 
mk :: {α : Type*} {β : Type*} (a : α) (b : β)

-- infers the value of fields
#check { my_struct . a := 10, b := true }

-- record update: creates a new object by modifying the fields in an old one

def q : point nat := { x := 1, y := 2} 

#reduce {y := 3, ..q}
#reduce {x := 4, ..q}


structure point3 (α : Type*) := mk :: (x : α) (y : α) (z : α)

def r : point3 nat := {x := 5, y := 5, z := 5}

def s : point3 nat := { x := 5, ..q, ..r}

#reduce s
end one
-- 9.3 Inheritance
namespace two

structure point (α : Type*) := mk :: (x : α) (y : α)
structure rgb_val := (red : nat) (green : nat) (blue : nat)

structure red_green_point (α : Type*) extends point α, rgb_val :=
(no_blue : blue = 0)

#print red_green_point 
end two
