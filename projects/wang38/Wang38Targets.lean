import Std

/-!
Exact target vocabulary for Wang--Wang--Yu, EJC 30(1) (2023), P1.38,
Definitions 13 and 16, Conjecture 38. These are DEFINITIONS, not proofs of
Conjecture 38. The rank-one predicate below says that the column space has a
one-element basis over the residue field; it does not assume the desired
support bound. Only positive dimensions and odd prime moduli are used.
-/
namespace Wang38

abbrev IVector (n : Nat) := Fin n → Int
abbrev IMatrix (n : Nat) := Fin n → Fin n → Int
abbrev QMatrix (n : Nat) := Fin n → Fin n → Rat

def sumI {n : Nat} (v : IVector n) : Int := (List.ofFn v).sum

def sumQ {n : Nat} (v : Fin n → Rat) : Rat := (List.ofFn v).sum

def dotI {n : Nat} (v w : IVector n) : Int := sumI fun i => v i * w i

def OddPrime (p : Nat) : Prop :=
  2 ≤ p ∧ p % 2 = 1 ∧ ∀ d : Nat, d ∣ p → d = 1 ∨ d = p

def FullSupport {n : Nat} (p : Nat) (v : IVector n) : Prop :=
  ∀ i, v i % (p : Int) ≠ 0

def Admissible {n : Nat} (p : Nat) (v : IVector n) : Prop :=
  FullSupport p v ∧ sumI v % (p : Int) = 0 ∧ dotI v v % (p : Int) = 0

def Integral (q : Rat) : Prop := ∃ z : Int, q = (z : Rat)

def ClearsDenominators {n : Nat} (d : Nat) (Q : QMatrix n) : Prop :=
  ∀ i j, Integral ((d : Rat) * Q i j)

/-- `p` is the least positive common denominator, as in source page 5. -/
def ExactLevel {n : Nat} (p : Nat) (Q : QMatrix n) : Prop :=
  0 < p ∧ ClearsDenominators p Q ∧
  ∀ d : Nat, 0 < d → ClearsDenominators d Q → p ≤ d

def Orthogonal {n : Nat} (Q : QMatrix n) : Prop :=
  ∀ i j, sumQ (fun k => Q k i * Q k j) = if i = j then 1 else 0

def Regular {n : Nat} (Q : QMatrix n) : Prop :=
  ∀ i, sumQ (fun j => Q i j) = 1

def Numerator {n : Nat} (p : Nat) (Q : QMatrix n) (A : IMatrix n) : Prop :=
  ∀ i j, (A i j : Rat) = (p : Rat) * Q i j

/-- All columns belong to the residue line spanned by `v`. -/
def ColumnsInLine {n : Nat} (p : Nat) (v : IVector n) (A : IMatrix n) : Prop :=
  ∀ j, ∃ c : Int, ∀ i, A i j % (p : Int) = (c * v i) % (p : Int)

/-- Over a prime modulus, a nonzero matrix with all columns in a single
nonzero line has rank exactly one. The definition uses this basis form,
so it needs no imported matrix-rank library. -/
def RankOneMod {n : Nat} (p : Nat) (A : IMatrix n) : Prop :=
  (∃ i j, A i j % (p : Int) ≠ 0) ∧
  ∃ v : IVector n, (∃ i, v i % (p : Int) ≠ 0) ∧ ColumnsInLine p v A

/-- Definition 13, including regularity and the EXACT prime level. -/
def Primitive {n : Nat} (p : Nat) (Q : QMatrix n) : Prop :=
  Orthogonal Q ∧ Regular Q ∧ ExactLevel p Q ∧
  ∃ A : IMatrix n, Numerator p Q A ∧ RankOneMod p A

/-- Definitions 13 and 16 together. The same integral numerator is used
for the rank and generator tests. -/
def GeneratedPrimitive {n : Nat} (p : Nat) (v : IVector n) (Q : QMatrix n) : Prop :=
  Orthogonal Q ∧ Regular Q ∧ ExactLevel p Q ∧
  ∃ A : IMatrix n, Numerator p Q A ∧ RankOneMod p A ∧ ColumnsInLine p v A

/-- Full low-dimensional target. No declaration asserts this proposition. -/
def Conjecture38I : Prop :=
  ∀ p n : Nat, OddPrime p → 0 < n → n ≤ 8 →
  ∀ v : IVector n, Admissible p v →
  ∃ Q : QMatrix n, GeneratedPrimitive p v Q

/-- Full high-dimensional target. No declaration asserts this proposition. -/
def Conjecture38II : Prop :=
  ∀ p n : Nat, OddPrime p → 2 * p + 1 ≤ n →
  ∀ v : IVector n, Admissible p v →
  ¬ ∃ Q : QMatrix n, GeneratedPrimitive p v Q

theorem generated_is_primitive {p n : Nat} {v : IVector n} {Q : QMatrix n}
    (h : GeneratedPrimitive p v Q) : Primitive p Q := by
  rcases h with ⟨ho, hr, hl, A, ha, hk, _⟩
  exact ⟨ho, hr, hl, A, ha, hk⟩

/-- The one-dimensional low-rank case is vacuous: zero coordinate sum and
full support already contradict one another. This does not cover ranks 2--8. -/
theorem no_admissible_dimension_one (p : Nat) (v : IVector 1) :
    ¬ Admissible p v := by
  intro h
  have hn := h.1 (0 : Fin 1)
  have hs := h.2.1
  simp [sumI, List.ofFn_succ] at hs
  exact hn hs

theorem conjecture38I_dimension_one (p : Nat) (v : IVector 1)
    (h : Admissible p v) : ∃ Q : QMatrix 1, GeneratedPrimitive p v Q := by
  exact False.elim (no_admissible_dimension_one p v h)

#print axioms generated_is_primitive
#print axioms no_admissible_dimension_one
#print axioms conjecture38I_dimension_one

end Wang38
