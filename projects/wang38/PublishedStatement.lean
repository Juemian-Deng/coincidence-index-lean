import Wang38II
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
The public statement using Mathlib's actual finite-field matrix rank.
The final theorem below keeps every original hypothesis and every component
of Definitions 13 and 16. The modular rank is not an abstract surrogate.
-/
namespace Wang38

noncomputable def residueMatrix {p n : Nat} (A : IMatrix n) : Matrix (Fin n) (Fin n) (ZMod p) :=
  Matrix.of (fun i j => (A i j : ZMod p))

def PublishedGeneratedPrimitive {n : Nat} (p : Nat) (v : IVector n) (Q : QMatrix n) : Prop :=
  Orthogonal Q ∧ Regular Q ∧ ExactLevel p Q ∧
  ∃ A : IMatrix n, Numerator p Q A ∧
    (residueMatrix (p := p) A).rank = 1 ∧ ColumnsInLine p v A

/-- Literal public part (i). This remains an unproved proposition. -/
def PublishedConjecture38I : Prop :=
  ∀ p n : Nat, Nat.Prime p → p % 2 = 1 → 0 < n → n ≤ 8 →
  ∀ v : IVector n, Admissible p v →
  ∃ Q : QMatrix n, PublishedGeneratedPrimitive p v Q

/-- Literal public part (ii), now using Nat.Prime and Matrix.rank over ZMod p. -/
def PublishedConjecture38II : Prop :=
  ∀ p n : Nat, Nat.Prime p → p % 2 = 1 → 2*p+1 ≤ n →
  ∀ v : IVector n, Admissible p v →
  ¬ ∃ Q : QMatrix n, PublishedGeneratedPrimitive p v Q

theorem matrix_rank_one_nonzero {p n : Nat} (hp : OddPrime p) (A : IMatrix n)
    (hr : (residueMatrix (p := p) A).rank = 1) :
    ∃ i j, A i j % (p : Int) ≠ 0 := by
  classical
  let : Fact (Nat.Prime p) := ⟨oddPrime_isPrime hp⟩
  by_contra h
  push Not at h
  have hz : residueMatrix (p := p) A = 0 := by
    ext i j
    exact (intCast_mod_zero_iff p (A i j)).mpr (h i j)
  rw [hz, Matrix.rank_zero] at hr
  omega

theorem published_generated_implies_basis_generated {p n : Nat} (hp : OddPrime p)
    (v : IVector n) (hv : FullSupport p v) (Q : QMatrix n)
    (hQ : PublishedGeneratedPrimitive p v Q) : GeneratedPrimitive p v Q := by
  rcases hQ with ⟨ho, he, hl, A, hn, hr, hc⟩
  have hnonzero := matrix_rank_one_nonzero hp A hr
  rcases hnonzero with ⟨i, j, hij⟩
  exact ⟨ho, he, hl, A, hn, ⟨⟨i, j, hij⟩, v, ⟨i, hv i⟩, hc⟩, hc⟩

/-- Complete proof of the public all-prime nonexistence statement. -/
theorem published_conjecture38II : PublishedConjecture38II := by
  intro p n hp ho hn v hv hQ
  have hp' : OddPrime p := ⟨hp.two_le, ho, (Nat.prime_def.mp hp).2⟩
  rcases hQ with ⟨Q, hQ⟩
  have hb := generated_dimension_le_twice_prime hp' v hv.1 Q
    (published_generated_implies_basis_generated hp' v hv.1 Q hQ)
  omega

#print axioms matrix_rank_one_nonzero
#print axioms published_conjecture38II
#print PublishedConjecture38II
#print PublishedGeneratedPrimitive
#print published_conjecture38II

end Wang38
