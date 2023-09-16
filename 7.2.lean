def length {α : Type*} (l : list α) : nat :=
list.rec_on l 0 (λ (head : α) (tail : list α) (prev : nat), prev.succ) 

def reverse {α : Type*} (l : list α) : list α :=
list.rec_on l list.nil (λ (head : α) (tail : list α) (tailrev : list α), tailrev
++ [head])

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
                            
-- a
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
                         
-- b
theorem length_reverse (l : list α) : length(l) = length(reverse(l)) :=
  list.rec_on l rfl 
  (λ (h : α) (t : list α) (ih : length(t) = length(reverse(t))), 
  show length(h :: t) = length(reverse (h :: t)), from
  calc length (h :: t) =  length(t) + 1 : by refl
                   ... = length(reverse(t)) + 1 : by rw ih
                   ... = length(reverse(t)) + length([h]) : by refl 
                   ... = length(reverse(t) ++ [h]) : by rw length_additive)
                   -- rest by refl
                   
-- c
theorem reverse_append (a b : list α) : reverse(a ++ b) = reverse(b) ++
reverse(a) :=
begin
  induction a with h tl ih, 
    have : list.nil ++ b = b, refl, 
    rw [this], 
    have : reverse list.nil = list.nil, refl,
    rw [this], 
    rw [append_nil], 
  have : reverse(h :: tl ++ b) = reverse(tl ++ b) ++ [h], refl, 
  rw [this, ih], 
  have : reverse (h :: tl) = reverse(tl) ++ [h], refl,
  rw [this, append_assoc], 
end 
