
inductive Vec (α : Type) : Nat → Type u where
  | nil : Vec α 0
  | cons (a : α) {n : Nat} (v : Vec α n) : Vec α (n + 1)
