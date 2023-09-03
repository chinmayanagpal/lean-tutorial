-- Exercise 1
section
def double (x : ℕ) : ℕ := x + x 

def do_twice (f: ℕ → ℕ) (x : ℕ) := f (f x)

def Do_Twice (F: (ℕ → ℕ) → (ℕ → ℕ)) (f: ℕ → ℕ) (x: ℕ) := F (F f) x

#reduce do_twice double 2

#reduce Do_Twice do_twice double 2

def compose (α β γ : Type*) (g : β → γ) (f: α → β) (x : α) : γ := g (f x)

#check compose
 end

-- Exercise 2 
section
def curry (α β γ : Type*) (f : α × β → γ) : α -> β -> γ := λ (a : α) (b: β), f
(a, b)

def uncurry (α β γ : Type*) (f : α → β → γ) : α × β -> γ := λ (p : α × β), (f
p.1) p.2 
end

-- Exercise 3
universe u
constant vec : Type u → ℕ → Type u
constant vec_add : Π {α : Type u} {n : ℕ} , vec α n → vec α n → vec α n
constant vec_reverse : Π {α : Type u} {n : ℕ}, vec α n → vec α n

section
variable α : Type
variable n : ℕ 
variable x : vec α n

#check vec_add x x
#check @vec_add α n x x
#check @vec_reverse α n x
#check vec_reverse x
end
-- Exercise 4
constant matrix : Type u → ℕ → ℕ → Type u
constant matrix_multiply : Π {α : Type u} {m n : ℕ}, matrix α m n → matrix α m n →  matrix α m n 
constant matrix_add : Π {α : Type u} {m n : ℕ}, matrix α m n → matrix α m n →  matrix α m n 
constant matrix_apply : Π {α : Type u} {m n : ℕ}, matrix α m n → vec α n -> vec α m

section 
variable α : Type
variables m n : ℕ
variables A B : matrix α m n
variable x : vec α n

#check matrix_multiply A B
#check matrix_add A B
#check matrix_apply A x
end
