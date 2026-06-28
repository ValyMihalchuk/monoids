
inductive Vec (α : Type) : Nat → Type where
  | nil : Vec α 0
  | cons (a : α) {n : Nat} (v : Vec α n) : Vec α (n + 1)


#check (Vec.cons 5 (Vec.cons 4 (Vec.nil)) : Vec Nat 2)


def vappend : Vec a m → Vec a n → Vec a (n + m)
  | Vec.nil, ys => ys
  |(Vec.cons x xs), ys => Vec.cons x (vappend xs ys)

def vappend' : Vec a m → Vec a n → Vec a (m + n)
  | Vec.nil, ys => Eq.mpr (by simp) ys
  |(Vec.cons x xs), ys => Eq.mpr (by grind) (Vec.cons x (vappend xs ys))

theorem cons_cast_tail_mpr
    {i j : Nat}
    (h : i = j)
    (x : α)
    (xs : Vec α j) :
    Eq.mpr (congrArg (Vec α) (congrArg (fun k => k + 1) h)) (Vec.cons x xs)
      =
    Vec.cons x (Eq.mpr (congrArg (Vec α) h) xs) := by
  cases h
  rfl

theorem vappend_nil_cons (x : α) {n : Nat} (xs : Vec α n) :
    vappend .nil (Vec.cons x xs) = Vec.cons x (vappend .nil xs) := by
  unfold vappend
  rfl

theorem vappend'_nil_cons (x : α) {n : Nat} (xs : Vec α n) :
    vappend' .nil (Vec.cons x xs) = Vec.cons x (vappend' .nil xs) := by
  unfold vappend'
  calc
    Eq.mpr (by simp : Vec α (0 + (n + 1)) = Vec α (n + 1)) (Vec.cons x xs)
        = Eq.mpr
            (congrArg (Vec α) (congrArg (fun k => k + 1) (show 0 + n = n by simp)))
            (Vec.cons x xs) := by
            rfl
    _ = Vec.cons x (Eq.mpr (by simp : Vec α (0 + n) = Vec α n) xs) := by
            rw [cons_cast_tail_mpr (show 0 + n = n by simp) x xs]



theorem simple_painful
    {β : Type v}
    (observe : {k : Nat} → Vec α k → β)
    {n : Nat}
    (xs : Vec α n)
    (expected : β)
    (p : observe xs = expected) :
    observe (vappend' .nil xs) = expected :=
by
  induction xs generalizing observe expected with
  | nil =>
      simpa [vappend'] using p
  | cons x xs ih =>
      rw [vappend'_nil_cons]
      exact ih (fun {k} ys => observe (Vec.cons x ys)) expected p






theorem cons_cast_tail
    {i j : Nat}
    (h : i = j)
    (x : α)
    (xs : Vec α i) :
    Vec.cons x (Eq.mp (congrArg (Vec α) h) xs)
      =
    Eq.mp (congrArg (Vec α) (congrArg (fun k => k + 1) h)) (Vec.cons x xs) := by
  cases h
  rfl

#check Nat.add


/-[1,2] ++ [3] = [1,2,3] -/
#eval vappend (Vec.cons 1 (Vec.cons 2 (Vec.nil))) (Vec.cons 3 (Vec.nil))


def snoc : Vec a n → a → Vec a (n + 1)
| Vec.nil, y => Vec.cons y Vec.nil
| (Vec.cons x xs), y => Vec.cons x (snoc xs y)

def slowReverse : Vec a n → Vec a n
| Vec.nil => Vec.nil
| (Vec.cons x xs) => snoc (slowReverse xs) x


def revAcc : Vec a m → Vec a n → Vec a (n + m)
| Vec.nil, ys => ys
| (Vec.cons x xs), ys => by
                            rename_i m
                            have : n + (m + 1) = (n+1)+m := by grind
                            rw[this]
                            apply (revAcc xs (Vec.cons x ys))
--                              n✝         (n+1)
--   (n✝+1)         n            (n+1)+n✝
--                              n+(n✝+1)


theorem abc (n: Nat) (ys : Vec α n): vappend .nil ys =  Eq.mp (by grind) (vappend ys .nil) :=
by
  induction ys with
  | nil => rfl
  | cons x xs ih =>
      rename_i k
      simp [vappend] at ih ⊢
      calc
        Vec.cons x xs
            = Vec.cons x
                (Eq.mp (congrArg (Vec α) (show 0 + k = k by grind))
                  (vappend xs Vec.nil)) := by
              exact congrArg (Vec.cons x) ih
        _ = Eq.mp
              (congrArg (Vec α) (congrArg (fun t => t + 1) (show 0 + k = k by grind)))
              (Vec.cons x (vappend xs Vec.nil)) := by
              exact cons_cast_tail (show 0 + k = k by grind) x (vappend xs Vec.nil)
        _ = Eq.mp (by grind)
              (Vec.cons x (vappend xs Vec.nil)) := by
              congr





theorem reverseFoldl_preserves_observation
    {β : Type v}
    (observe : {k : Nat} → Vec α k → β)
    {n : Nat}
    (xs : Vec α n)
    (expected : β)
    (p : observe (revAcc .nil ys) = expected) :
    observe (revAcc ys .nil) = expected := by
  cases ys
  apply p
  simp[revAcc] at p
  simp[revAcc]
  simp[cast]
