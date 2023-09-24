import tactic.suggest
inductive aexpr : Type
| const: ℕ → aexpr
| var : ℕ → aexpr
| plus : aexpr → aexpr → aexpr
| times : aexpr → aexpr → aexpr

open aexpr

def sample_aexpr : aexpr :=
plus (times (var 0 ) (const 7)) (times (const 2) (var 1))

def aeval (v : ℕ → ℕ) : aexpr → ℕ 
| (const n)    := n
| (var n)      := v n
| (plus e₁ e₂)  := (aeval e₁) + (aeval e₂)
| (times e₁ e₂) := (aeval e₁) * (aeval e₂)

def sample_val : ℕ → ℕ
| 0 := 5
| 1 := 6
| _ := 0

def simp_const : aexpr →  aexpr
| (plus (const n) (const m))  := const (n + m)
| (times (const n) (const m)) := const (n * m)
| x                           := x

def fuse : aexpr → aexpr
| (const n) := const n
| (var n)   := var n
| (plus e₁ e₂) := simp_const (plus (fuse e₁) (fuse e₂))
| (times e₁ e₂) := simp_const (times (fuse e₁) (fuse e₂))

theorem simp_const_eq (v : ℕ → ℕ) : ∀ e : aexpr, aeval v (simp_const e) = aeval
v e 
| (const n) := rfl
| (var n)   := rfl
| (plus x y) := 
  match x with 
  | (const n)   := 
    match y with 
    | (const n)   := rfl
    | (var n)     := by { simp[simp_const] } 
    | (plus e₁ e₂) := by { simp[simp_const] } 
    | (times e₁ e₂):= by { simp[simp_const] } 
    end
  | (var n)     := by { simp[simp_const] } 
  | (plus e₁ e₂) := by { simp[simp_const] } 
  | (times e₁ e₂):= by { simp[simp_const] } 
  end
| (times x y) := 
  match x with 
  | (const n)   := 
    match y with 
    | (const n)   := rfl
    | (var n)     := by { simp[simp_const] } 
    | (plus e₁ e₂) := by { simp[simp_const] } 
    | (times e₁ e₂):= by { simp[simp_const] } 
    end
  | (var n)     := by { simp[simp_const] } 
  | (plus e₁ e₂) := by { simp[simp_const] } 
  | (times e₁ e₂):= by { simp[simp_const] } 
  end
  -- surely there's a nicer way to do the above
theorem fuse_eq (v : ℕ → ℕ) :
  ∀ e : aexpr, aeval v (fuse e) = aeval v e 
| (const n) := rfl
| (var m)   := rfl
| (plus e₁ e₂) := by {simp[fuse, simp_const_eq, aeval, fuse_eq]}
| (times e₁ e₂) := by {simp[fuse, simp_const_eq, aeval, fuse_eq]}
