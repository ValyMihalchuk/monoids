
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
def vappend'' : Vec a m → Vec a n → Vec a (m + n)
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
    unfold vappend'
    simp
    exact mpr_cons (show 0 + n = n by simp) x xs



def snoc : Vec a n → a → Vec a (n + 1)
| Vec.nil, y => Vec.cons y Vec.nil
| (Vec.cons x xs), y => Vec.cons x (snoc xs y)

def slowReverse : Vec a n → Vec a n
| Vec.nil => Vec.nil
| (Vec.cons x xs) => snoc (slowReverse xs) x


def revAccCast : Vec a m → Vec a n → Vec a (n + m)
| Vec.nil, acc => acc
| (Vec.cons x xs), acc => Eq.mp (congrArg (Vec a) (by grind)) (revAccCast xs (Vec.cons x acc))


def DNat := Nat → Nat

def denote (n : Nat) : DNat :=
  fun m => m + n

def reify (m : DNat) : Nat :=
  m 0

theorem reify_correct (n : Nat) : reify (denote n) = n := by
  simp [reify, denote]

def dzero : DNat :=
  fun x => x

def dplus (n m : DNat) : DNat :=
  fun x => m (n x)

theorem dzero_right (x : DNat) : reify x = reify (dplus x dzero) := by
  unfold reify dplus dzero
  rfl

theorem dzero_left (x : DNat) : reify x = reify (dplus dzero x) := by
  unfold reify dplus dzero
  rfl

theorem dplus_assoc (x y z : DNat) :
    reify (dplus x (dplus y z)) = reify (dplus (dplus x y) z) := by
  unfold reify dplus
  rfl

theorem dplus_correct (n m : Nat) :
    n + m = reify (dplus (denote n) (denote m)) := by
  simp [reify, dplus, denote]

def dsucc (m : DNat) : DNat :=
  fun n => m (n + 1)

def revAcc
    (m : DNat)
    (cons : {k : Nat} → a → Vec a (m k) → Vec a ((dsucc m) k)) :
    Vec a n → Vec a (reify m) → Vec a (m n)
  | Vec.nil, acc => acc
  | Vec.cons x xs, acc => revAcc (dsucc m) cons xs (cons x acc)

def vreverse (xs : Vec a n) : Vec a n :=
  revAcc dzero (fun x xs => Vec.cons x xs) xs Vec.nil

def dappend
    (m : DNat)
    (cons : {k : Nat} → a → Vec a (m k) → Vec a ((dsucc m) k)) :
    Vec a n → Vec a (reify m) → Vec a (m n)
  | Vec.nil, ys => ys
  | Vec.cons x xs, ys => cons x (dappend m cons xs ys)

theorem dappend_snoc
    (m : DNat)
    (cons : {k : Nat} → a → Vec a (m k) → Vec a ((dsucc m) k))
    (xs : Vec a n)
    (x : a)
    (ys : Vec a (reify m)) :
    dappend m cons (snoc xs x) ys =
      dappend (dsucc m) cons xs (cons x ys) := by
  induction xs with
  | nil =>
      rfl
  | cons z zs ih =>
      grind [snoc, dappend]

theorem revAcc_correct
    (m : DNat)
    (xs : Vec a n)
    (ys : Vec a (reify m))
    (cons : {k : Nat} → a → Vec a (m k) → Vec a ((dsucc m) k)) :
    revAcc m cons xs ys = dappend m cons (slowReverse xs) ys := by
  induction xs generalizing m with
  | nil =>
      rfl
  | cons x xs ih =>
      grind [revAcc, slowReverse, dappend_snoc]

theorem dappend_dzero_nil
    (xs : Vec a n) :
    dappend dzero (fun x xs => Vec.cons x xs) xs Vec.nil = xs := by
  induction xs with
  | nil =>
      rfl
  | cons x xs ih =>
      grind [dappend]

theorem vreverse_correct (xs : Vec a n) :
    vreverse xs = slowReverse xs := by
  unfold vreverse
  rw [revAcc_correct]
  exact dappend_dzero_nil (slowReverse xs)
