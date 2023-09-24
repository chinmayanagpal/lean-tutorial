-- class 
namespace one

class inhabited (α : Type _) := (default : α)

-- the above is shorthand for: 
-- @[class] structure inhabited (α : Type _) := (default : α)

-- then we have some instances (illustrated w/ different ways of constructing)

instance Prop_inhabited : inhabited Prop := inhabited.mk true

instance bool_inhabited : inhabited bool := { default :=  tt }

instance nat_inhabited : inhabited nat := ⟨0⟩

instance unit_inhabited : inhabited unit := inhabited.mk ()

-- whenever elaborator is looking for a value to assign to an argument of type
-- inhabited α for some α, it can check the list. e.g. when looking for a member
-- of inhabited Prop, it'll find Prop_inhabited


-- finally: something that takes an element (s : inhabited α) and puts it to
-- good use

def default (α : Type*) [s : inhabited α] : α := @inhabited.default α s

-- whenever we write default α, we are writing default α ?s where ?s is found
-- out by the elaborator

#reduce default Prop

-- arbitrary is similar to "default", but it is marked irreducible to discourage
-- the elaborator from unfolding it. 
end one
