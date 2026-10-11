import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import MatrixNumerator

open scoped BigOperators
namespace Wang38

 theorem orthogonal_matrix_identity {n : Nat} {Q : QMatrix n} (ho : Orthogonal Q) :
    (Matrix.transpose (Matrix.of Q) * Matrix.of Q : Matrix (Fin n) (Fin n) Rat) = 1 := by
  ext i j
  simpa [Matrix.mul_apply, Matrix.transpose_apply, sumQ, List.sum_ofFn, Matrix.one_apply] using ho i j

 theorem orthogonal_transpose_identity {n : Nat} {Q : QMatrix n} (ho : Orthogonal Q) :
    (Matrix.of Q * Matrix.transpose (Matrix.of Q) : Matrix (Fin n) (Fin n) Rat) = 1 := by
  exact mul_eq_one_comm.mp (orthogonal_matrix_identity ho)

 theorem orthogonal_transpose {n : Nat} {Q : QMatrix n} (ho : Orthogonal Q) :
    Orthogonal (Matrix.transpose Q) := by
  intro i j
  change sumQ (fun k => Q i k * Q j k) = if i = j then 1 else 0
  have h := congrFun (congrFun (orthogonal_transpose_identity ho) i) j
  simpa [Matrix.mul_apply, Matrix.transpose_apply, sumQ, List.sum_ofFn, Matrix.one_apply] using h

/-- A square orthogonal matrix spans the entire ambient space. -/
theorem numerator_columns_span {p n : Nat} (hp : 0 < p)
    {Q : QMatrix n} {A : IMatrix n} (ho : Orthogonal Q) (hn : Numerator p Q A)
    (a : IVector n) (ha : ∀ j, dotI a (fun i => A i j) = 0) :
    ∀ i, a i = 0 := by
  let ar : Fin n → Rat := fun i => (a i : Rat)
  have hpQ : (p : Rat) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt hp)
  have hzero : (Matrix.transpose (Matrix.of Q)).mulVec ar = 0 := by
    funext j
    have h := congrArg (fun z : Int => (z : Rat)) (ha j)
    change ((dotI a (fun i => A i j) : Int) : Rat) = 0 at h
    unfold dotI at h
    rw [← sumQ_intCast] at h
    have hf : (fun i => ((a i * A i j : Int) : Rat)) =
        (fun i => (p : Rat) * (Q i j * ar i)) := by
      funext i
      rw [Rat.intCast_mul, hn]
      dsimp [ar]
      ring
    rw [hf, sumQ_smul] at h
    have hs := (mul_eq_zero.mp h).resolve_left hpQ
    simpa [Matrix.mulVec, dotProduct, ar, sumQ, List.sum_ofFn] using hs
  have har : ar = 0 := by
    calc
      ar = (1 : Matrix (Fin n) (Fin n) Rat).mulVec ar := (Matrix.one_mulVec ar).symm
      _ = (Matrix.of Q * Matrix.transpose (Matrix.of Q)).mulVec ar := by
        rw [orthogonal_transpose_identity ho]
      _ = (Matrix.of Q).mulVec ((Matrix.transpose (Matrix.of Q)).mulVec ar) :=
        (Matrix.mulVec_mulVec ar _ _).symm
      _ = 0 := by rw [hzero, Matrix.mulVec_zero]
  intro i
  have h := congrFun har i
  apply Rat.intCast_inj.mp
  simpa [ar] using h

theorem oddPrime_isPrime {p : Nat} (hp : OddPrime p) : Nat.Prime p :=
  Nat.prime_def.mpr ⟨hp.1, hp.2.2⟩

theorem intCast_mod_zero_iff (p : Nat) (z : Int) :
    (z : ZMod p) = 0 ↔ z % (p : Int) = 0 := by
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd, Int.dvd_iff_emod_eq_zero]

/-- Two nonzero multiples of a residue vector differ by a nonzero scalar.
The integer scalar is chosen from an actual finite-field quotient. -/
theorem nonzero_residue_line_ratio {p n : Nat} (hp : OddPrime p)
    (a b v : IVector n) (c d : Int)
    (hc : c % (p : Int) ≠ 0) (hd : d % (p : Int) ≠ 0)
    (ha : ∀ i, a i % (p : Int) = (c*v i) % (p : Int))
    (hb : ∀ i, b i % (p : Int) = (d*v i) % (p : Int)) :
    ∃ k : Int, k % (p : Int) ≠ 0 ∧ ∀ i, (b i-k*a i) % (p : Int) = 0 := by
  let : Fact (Nat.Prime p) := ⟨oddPrime_isPrime hp⟩
  have hcZ : (c : ZMod p) ≠ 0 := by
    intro h
    exact hc ((intCast_mod_zero_iff p c).mp h)
  have hdZ : (d : ZMod p) ≠ 0 := by
    intro h
    exact hd ((intCast_mod_zero_iff p d).mp h)
  let q : ZMod p := (d : ZMod p)/(c : ZMod p)
  let k : Int := q.val
  have hkZ : (k : ZMod p) = q := by simp [k, ZMod.natCast_val]
  refine ⟨k, ?_, ?_⟩
  · intro h
    have hz := (intCast_mod_zero_iff p k).mpr h
    rw [hkZ] at hz
    exact div_ne_zero hdZ hcZ hz
  · intro i
    apply (intCast_mod_zero_iff p _).mp
    have haZ : (a i : ZMod p) = (c : ZMod p)*(v i : ZMod p) := by
      rw [← Int.cast_mul]
      exact (ZMod.intCast_eq_intCast_iff' _ _ p).mpr (ha i)
    have hbZ : (b i : ZMod p) = (d : ZMod p)*(v i : ZMod p) := by
      rw [← Int.cast_mul]
      exact (ZMod.intCast_eq_intCast_iff' _ _ p).mpr (hb i)
    rw [Int.cast_sub, Int.cast_mul, hkZ, haZ, hbZ]
    dsimp [q]
    rw [← mul_assoc, div_mul_cancel₀ _ hcZ, sub_self]

/-- Every norm-p² numerator in a nonzero generating residue class really is
an actual column, up to sign. This closes completeness, without assuming it. -/
theorem residue_class_complete {p n : Nat} (hp : OddPrime p)
    {v : IVector n} (hv : FullSupport p v) {Q : QMatrix n} {A : IMatrix n}
    (ho : Orthogonal Q) (hn : Numerator p Q A)
    (hk : RankOneMod p A) (hl : ColumnsInLine p v A)
    (a : IVector n) (ha : dotI a a = (p : Int)*(p : Int))
    (d : Int) (hd : d % (p : Int) ≠ 0)
    (hares : ∀ i, a i % (p : Int) = (d*v i) % (p : Int)) :
    ∃ j, (fun i => A i j) = a ∨ (fun i => A i j) = fun i => -a i := by
  classical
  by_contra hnone
  have hnot : ∀ j, (fun i => A i j) ≠ a ∧ (fun i => A i j) ≠ (fun i => -a i) := by
    simpa only [not_exists, not_or] using hnone
  have hfull := numerator_full_support hp hv ho hn hk hl
  have hall : ∀ j, dotI a (fun i => A i j) = 0 := by
    intro j
    rcases hl j with ⟨c, hc⟩
    have hc0 : c % (p : Int) ≠ 0 := by
      intro hz
      have he := hc j
      rw [Int.mul_emod, hz] at he
      simp at he
      exact hfull j j (Int.emod_eq_zero_of_dvd he)
    rcases nonzero_residue_line_ratio hp a (fun i => A i j) v d c hd hc0 hares hc with
      ⟨r, hr, hres⟩
    have h := orthogonal_or_equal_up_to_sign hp a (fun i => A i j) ha
      (numerator_column_norm ho hn j) r hr hres
    exact h.resolve_right (by
      intro h
      rcases h with h | h
      · exact (hnot j).1 h
      · exact (hnot j).2 h)
  have haz := numerator_columns_span (by have := hp.1; omega) ho hn a hall
  have hae : a = fun _ => 0 := funext haz
  rw [hae, dotI_zero_left] at ha
  have hp0 : 0 < (p : Int) := by have := hp.1; omega
  have hp2 := Int.mul_pos hp0 hp0
  omega

#print axioms orthogonal_transpose
#print axioms numerator_columns_span
#print axioms nonzero_residue_line_ratio
#print axioms residue_class_complete

end Wang38
