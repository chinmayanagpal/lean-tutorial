import data.int.basic

#check sub_self

example (x : ℤ) : x * 0 = 0 :=
  calc 
    x * 0 = x * (1 - 1)         : by rw (sub_self (1 : ℤ))
      ... = 0                   : by rw [mul_sub, mul_one, sub_self]
