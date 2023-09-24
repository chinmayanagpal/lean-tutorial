namespace hidden
universe u
inductive list (α : Type u) : Type u
| nil {} : list 
| cons   : α → list → list

namespace list

variable {α : Type u}

def append : list α → list α → list α
| nil l := l
| (cons h₁ tl₁) l := (cons h₁ (append tl₁ l))

def reverse : list α → list α 
| nil := nil
| (cons h tl) := append (reverse tl) (cons h nil)

theorem append_nil : ∀ t : list α, append t nil = t
| nil         := rfl
| (cons h tl) := by { rw[append, append_nil tl] }

-- theorem nil_append : ∀ t : list α, append nil t = t
-- | nil          := rfl
-- | (cons h tl)  := by {rw[append]}

theorem append_assoc : ∀ l₁ l₂ l₃ : list α, (append l₁ (append l₂ l₃)) = (append
(append l₁ l₂) l₃) 
| nil l₂ l₃ := by repeat {rw[append]} 
| (cons h tl) l₂ l₃ := by {repeat {rw[append]}, rw[append_assoc tl l₂ l₃]}

theorem reverse_append : ∀ l₁ l₂ : list α, reverse (append l₁ l₂) =
append (reverse l₂) (reverse l₁) 
| nil l := by {rw[reverse, append, append_nil]}
| (cons h tl) l := by {rw[reverse, append, reverse, reverse_append tl, append_assoc] }

-- theorem reverse_cons : ∀ a : α, reverse (cons a nil) = (cons a nil) 

theorem reverse_reverse : ∀ l : list α, reverse (reverse l) = l 
| nil := rfl
| (cons h tl) := 
  begin 
    rw [reverse, reverse_append, reverse_reverse tl],
    repeat { rw [reverse] },
    repeat { rw [append] }
  end

end list
end hidden
