
inductive Vec (α : Type) : Nat → Type where
  | nil : Vec α 0
  | cons (a : α) {n : Nat} (v : Vec α n) : Vec α (n + 1)


#check (Vec.cons 5 (Vec.cons 4 (Vec.nil)) : Vec Nat 2)


def vappend : Vec a m → Vec a n → Vec a (n+m)
  | Vec.nil, ys => ys
  |(Vec.cons x xs), ys => Vec.cons x (vappend xs ys)

#check Nat.add


/-[1,2] ++ [3] = [1,2,3] -/
#eval vappend (Vec.cons 1 (Vec.cons 2 (Vec.nil))) (Vec.cons 3 (Vec.nil))
