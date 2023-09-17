inductive even_odd : bool → ℕ → Prop
| even_zero : even_odd tt 0 
-- n and t below are constructor arguments
| even_succ (n : ℕ) (t : even_odd ff n) : even_odd tt (n + 1)
| odd_succ  (n : ℕ) (t : even_odd tt n) : even_odd ff (n + 1) 

#print even_odd
