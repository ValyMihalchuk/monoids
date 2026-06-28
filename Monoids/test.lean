/-
Minimal Lean 4 example of proof clutter from dependent casts.

The casted reverse below is mathematically just `reverseSlow`, but it transports
the result across an equality of length indices. Later proofs have to eliminate
that equality proof before the obvious proof can be used.
-/

universe u v

/-- A tiny custom length-indexed vector type. -/
inductive Vec (α : Type u) : Nat → Type u where
  | nil  : Vec α 0
  | cons : α → Vec α n → Vec α (Nat.succ n)

namespace Vec

/-- Add one element at the end of a vector. -/
def snoc : Vec α n → α → Vec α (Nat.succ n)
  | nil, y => cons y nil
  | cons x xs, y => cons x (snoc xs y)

/-- A clean reverse, with no casts in its definition. -/
def reverseSlow : Vec α n → Vec α n
  | nil => nil
  | cons x xs => snoc (reverseSlow xs) x

/--
A deliberately painful reverse-like function.

It computes `reverseSlow xs : Vec α n`, then transports it to `Vec α m`
using the equality proof `h : n = m`. The cast is the `Eq.mp` line.
-/
def reversePainful {n m : Nat} (h : n = m) (xs : Vec α n) : Vec α m :=
  Eq.mp (congrArg (Vec α) h) (reverseSlow xs)

/--
A concrete nontrivial Nat-index instance: cast the reversed vector from length
`n + m` to length `m + n` using commutativity of addition.
-/
def reversePainfulAddComm {n m : Nat} (xs : Vec α (n + m)) : Vec α (m + n) :=
  reversePainful (Nat.add_comm n m) xs

/--
Main theorem.

Conceptually, this is simple: if some length-polymorphic observation of the
clean reverse is `expected`, then the same observation of the casted reverse is
also `expected`.

But after unfolding `reversePainful`, the goal contains a transport. The direct
proof `p` has the wrong type, `rfl` cannot erase the cast, and `simp` alone does
not finish the proof. We must pattern-match on `h`.
-/

set_option pp.proofs true
theorem reversePainful_preserves_observation
    {β : Type v}
    (observe : {k : Nat} → Vec α k → β)
    {n m : Nat}
    (h : n = m)
    (xs : Vec α n)
    (expected : β)
    (p : observe (reverseSlow xs) = expected) :
    observe (  Eq.mp (congrArg (Vec α) h) (reverseSlow xs) ) = expected := by

  -- The obvious proof has the wrong type while the cast is still present.
  fail_if_success exact p

  -- The theorem is not definitionally true after unfolding.
  fail_if_success rfl

  -- `simp` may simplify pieces, but it does not close the goal.
  fail_if_success
    simp
    done

  -- This is the paper's "pattern matching on the proof to reduce".

  simp

  cases h
  simp

/-!
The paper's repair is to stop asking ordinary `Nat` addition to line up with an
accumulating recursion. Instead, make the changing length part of the type of
the accumulator.

The following dependent left fold is the Lean version of the paper's fold:
in the recursive case the result family changes from `β` to
`fun k => β (Nat.succ k)`. This is the same "push the successor inward" trick
as the Cayley/difference representation of the index monoid.
-/

def foldlDep
    (β : Nat → Type v)
    (step : {k : Nat} → β k → α → β (Nat.succ k))
    (base : β 0) :
    {n : Nat} → Vec α n → β n
  | 0, nil => base
  | Nat.succ _, cons x xs =>
      foldlDep
        (fun k => β (Nat.succ k))
        (fun {_} acc y => step acc y)
        (step base x)
        xs

/--
Reverse via the indexed fold. There is no `Eq.mp`, no equality proof argument,
and no final coercion.
-/
def reverseFoldl : Vec α n → Vec α n :=
  foldlDep
    (fun k => Vec α k)
    (fun acc x => cons x acc)
    nil

theorem reverseFoldl_nil :
    reverseFoldl (α := α) nil = nil := by
  rfl

/--
The analogous observation theorem is now boring in the good way: there is no
casted vector in the goal and no proof `h : n = m` to eliminate.
-/
theorem reverseFoldl_preserves_observation
    {β : Type v}
    (observe : {k : Nat} → Vec α k → β)
    {n : Nat}
    (xs : Vec α n)
    (expected : β)
    (p : observe (reverseFoldl xs) = expected) :
    observe (reverseFoldl xs) = expected := by
  exact p

end Vec
