
inductive Vec (α : Type) : Nat → Type where
  | nil : Vec α 0
  | cons (a : α) {n : Nat} (v : Vec α n) : Vec α (n + 1)


#check (Vec.cons 5 (Vec.cons 4 (Vec.nil)) : Vec Nat 2)


def vappend : Vec a m → Vec a n → Vec a (n + m)
  | Vec.nil, ys => ys
  | Vec.cons x xs, ys => Vec.cons x (vappend xs ys)

/-[1,2] ++ [3] = [1,2,3] -/
#eval vappend (Vec.cons 1 (Vec.cons 2 (Vec.nil))) (Vec.cons 3 (Vec.nil))

theorem vappend_nil_cons (x : α) {n : Nat} (xs : Vec α n) :
    vappend .nil (Vec.cons x xs) = Vec.cons x (vappend .nil xs) := by
  rfl

/-
def vappend' : Vec a m → Vec a n → Vec a (m + n)
  | Vec.nil, ys => ys
  | Vec.cons x xs, ys => Vec.cons x (vappend xs ys)
-/


def vappend' : Vec a m → Vec a n → Vec a (m + n)
  | Vec.nil, ys => Eq.mpr (by simp) ys
  | Vec.cons x xs, ys => Eq.mpr (by grind) (Vec.cons x (vappend xs ys))

theorem vappend'_nil_cons (x : α) {n : Nat} (xs : Vec α n) :
    vappend' .nil (Vec.cons x xs) = Vec.cons x (vappend' .nil xs) := by
  try rfl
  sorry


set_option pp.proofs true
theorem mpr_cons
    {i j : Nat}
    (h : i = j)
    (x : α)
    (xs : Vec α j) :
    Eq.mpr
      (congrArg (fun k => Vec α (k + 1)) h)
      (Vec.cons x xs)
      =
    Vec.cons x
      (Eq.mpr (congrArg (Vec α) h) xs) := by
  cases h
  rfl

theorem vappend'_nil_cons' (x : α) {n : Nat} (xs : Vec α n) :
    vappend' .nil (Vec.cons x xs) = Vec.cons x (vappend' .nil xs) := by
    exact mpr_cons (show 0 + n = n by simp) x xs



def snoc : Vec a n → a → Vec a (n + 1)
| Vec.nil, y => Vec.cons y Vec.nil
| (Vec.cons x xs), y => Vec.cons x (snoc xs y)

def slowReverse : Vec a n → Vec a n
| Vec.nil => Vec.nil
| (Vec.cons x xs) => snoc (slowReverse xs) x


def revAcc : Vec a m → Vec a n → Vec a (n + m)
| Vec.nil, ys => ys
| (Vec.cons x xs), ys => Eq.mp (congrArg (Vec a) (by grind)) (revAcc xs (Vec.cons x ys))
