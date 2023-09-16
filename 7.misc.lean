universes u v w

namespace bool_ops
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
end bool_ops

namespace partial_comp
inductive option (α : Type*)
| none {} : option
| some : α → option

#print option 

def unoption {α : Type u} (a : option α) : option.cases_on a (option α) (λ a,
α) :=
option.cases_on a (option.none) (λ a: α, a)

def partial_comp {α : Type u} {β : Type v} {γ : Type w} (f : α → option β) (g :
β → option γ) : α → option γ :=
assume a : α,
show option γ, from 
  option.cases_on (f a) 
    option.none 
    (λ b : β, option.cases_on (g b) option.none (λ c : γ, option.some(c)))
end partial_comp

namespace show_inhab
inductive inhabited (α : Type*)
| mk : α → inhabited
end show_inhab

def thm1 : inhabited(bool) := inhabited.mk(tt)

def thm2 : inhabited(nat) := inhabited.mk(nat.zero)

def thm3 {α : Type u} {β : Type v} : inhabited(β) → inhabited(α → β) :=
assume b : inhabited (β),
inhabited.mk(assume a, inhabited.cases_on b id)

section
variable {α : Type*}
theorem append_nil (t : list α) : t ++ list.nil = t :=
list.rec_on t 
  rfl 
  (λ (x : α) (l : list α) (u : l ++ list.nil = l), 
    show x::l ++ list.nil = x::l, from
    calc 
      x::l ++ list.nil = x::(l ++ list.nil) : by refl
                   ... = x::l : by rw u)
theorem append_assoc (r s t : list α) :
  r ++ s ++ t = r ++ (s ++ t) := 
list.rec_on r rfl 
  (λ (head : α) (tail : list α) (p : tail ++ s ++ t = tail ++ (s ++ t)), 
    show head::tail ++ s ++ t = head::tail ++ (s ++ t), from
    calc (head::tail ++ s) ++ t = head::(tail ++ s) ++ t        : by refl
                            ... = head::((tail ++ s) ++ t)      : by refl
                            ... = head::(tail ++ (s ++ t))      : by rw p 
                            ... = head::tail ++ (s ++ t)        : by refl)
                            
def length : list α → nat :=
(λ l : list α, 
  list.rec_on l 0 
    (λ (head : α) (tail : list α) (length_tail : nat), 
      length_tail + 1))

theorem length_additive (s t : list α) : length(s) + length(t) = length(s ++ t)
:=
list.rec_on s 
   (have p : length(@list.nil α) = 0, from rfl, 
    show length (list.nil) + length (t) = length(t), by rewrite [p, nat.zero_add])
  (λ (h : α) (s : list α) (p: length(s) + length(t) = length(s ++ t)),
  calc
    length(h::s) + length(t) = length(s) + 1 + length(t)    : by refl
                         ... = length(s) + (1 + length(t))  : by rw [nat.add_assoc]
                         ... = length(s) + ((length t) + 1) : by rw (nat.add_comm (length t) 1)
                         ... = length(s) + length(t) + 1    : by rw [nat.add_assoc]
                         ... = length(s ++ t) + 1           : by rw [p]
                         ... = length(h::(s ++ t))          : by refl 
                         ... = length(h::s ++ t)            : by refl)
end
