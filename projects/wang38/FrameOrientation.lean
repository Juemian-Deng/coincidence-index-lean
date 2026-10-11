import LatticeBridge

/-! Orient any orthonormal frame in the concrete neighbor using its
characteristic all-ones vector. This proves the regularity bridge. -/
open scoped BigOperators
namespace Wang38I
open Wang38

lemma column_sums_norm {n : ℕ} (Q : QMatrix n) (ho : Orthogonal Q) :
    dotQ (fun j => sumQ (fun i => Q i j)) (fun j => sumQ (fun i => Q i j)) = n := by
  have hs : (fun j => sumQ (fun i => Q i j)) =
      Matrix.vecMul (ones n) (Matrix.of Q) := by
    funext j
    simp [Matrix.vecMul, dotProduct, sumQ, List.sum_ofFn, ones]
  rw [hs]
  change dotProduct (Matrix.vecMul (ones n) (Matrix.of Q))
    (Matrix.vecMul (ones n) (Matrix.of Q)) = (n : ℚ)
  conv_lhs => arg 2; rw [← Matrix.mulVec_transpose]
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
    orthogonal_transpose_identity ho, Matrix.vecMul_one]
  simp [dotProduct, ones]

/-- Each column of an orthonormal frame has odd integral sum, and the
sums-of-squares identity forces this sum to be +1 or -1. -/
theorem frame_column_sums {p n : ℕ} (hp : OddPrime p) (u : IVector n)
    (hunorm : (p : ℤ) * p ∣ dotI u u) (husum : sumI u % (p : ℤ) = 0)
    (Q : QMatrix n) (ho : Orthogonal Q)
    (hcol : ∀ j, (fun i => Q i j) ∈ neighbor p u) :
    ∃ c : Fin n → ℤ, (∀ j, sumQ (fun i => Q i j) = (c j : ℚ)) ∧
      ∀ j, c j * c j = 1 := by
  have hp0 : p ≠ 0 := by have := hp.1; omega
  have hc : ∀ j, ∃ c : ℤ, sumQ (fun i => Q i j) = (c : ℚ) := by
    intro j
    obtain ⟨c, hc⟩ := neighbor_integral hp0 u hunorm (ones_mem_neighbor u husum) (hcol j)
    exact ⟨c, by simpa [dotQ, ones, sumQ, List.sum_ofFn] using hc⟩
  choose c hc using hc
  have hnonzero : ∀ j, c j ≠ 0 := by
    intro j hz
    obtain ⟨z, hz'⟩ := ones_characteristic hp u hunorm husum (hcol j)
    have hnorm : dotQ (fun i => Q i j) (fun i => Q i j) = 1 := by
      simpa [dotQ, sumQ, List.sum_ofFn] using ho j j
    have hsum : dotQ (ones n) (fun i => Q i j) = (c j : ℚ) := by
      simpa [dotQ, ones, sumQ, List.sum_ofFn] using hc j
    rw [hnorm, hsum, hz] at hz'
    have hh : (1 : ℤ) = 2 * z := by exact_mod_cast hz'
    omega
  have hle : ∀ j, (1 : ℤ) ≤ c j * c j := by
    intro j
    have h := int_square_positive (hnonzero j)
    omega
  have hsum : ∑ j, c j * c j = (n : ℤ) := by
    have hn := column_sums_norm Q ho
    simp only [dotQ, hc] at hn
    exact_mod_cast hn
  refine ⟨c, hc, ?_⟩
  have he : (∑ _j : Fin n, (1 : ℤ)) = ∑ j, c j * c j := by simpa using hsum.symm
  have hall := (Finset.sum_eq_sum_iff_of_le (s := Finset.univ)
    (fun j _ => hle j)).mp he
  exact fun j => (hall j (Finset.mem_univ j)).symm

/-- For an orthogonal square matrix, unit column sums imply unit row sums. -/
lemma regular_of_column_sums {n : ℕ} (Q : QMatrix n) (ho : Orthogonal Q)
    (hc : ∀ j, sumQ (fun i => Q i j) = 1) : Regular Q := by
  have he : (Matrix.transpose (Matrix.of Q)).mulVec (ones n) = ones n := by
    ext j
    simpa [Matrix.mulVec, dotProduct, ones, sumQ, List.sum_ofFn] using hc j
  have hr : (Matrix.of Q).mulVec (ones n) = ones n := by
    calc
      _ = (Matrix.of Q).mulVec ((Matrix.transpose (Matrix.of Q)).mulVec (ones n)) := by rw [he]
      _ = _ := by rw [Matrix.mulVec_mulVec, orthogonal_transpose_identity ho, Matrix.one_mulVec]
  intro i
  have hi := congrFun hr i
  simpa [Matrix.mulVec, dotProduct, ones, sumQ, List.sum_ofFn] using hi

/-- The sign-adjusted frame remains inside the actual neighbor and is regular. -/
theorem orient_neighbor_frame {p n : ℕ} (hp : OddPrime p) (u : IVector n)
    (hunorm : (p : ℤ) * p ∣ dotI u u) (husum : sumI u % (p : ℤ) = 0)
    (Q : QMatrix n) (ho : Orthogonal Q)
    (hcol : ∀ j, (fun i => Q i j) ∈ neighbor p u) :
    ∃ R : QMatrix n, Orthogonal R ∧ Regular R ∧
      ∀ j, (fun i => R i j) ∈ neighbor p u := by
  obtain ⟨c, hc, hc2⟩ := frame_column_sums hp u hunorm husum Q ho hcol
  let R : QMatrix n := fun i j => (c j : ℚ) * Q i j
  have hR : Orthogonal R := by
    intro j k
    have hfactor : (fun i => R i j * R i k) =
        (fun i => ((c j : ℚ) * (c k : ℚ)) * (Q i j * Q i k)) := by
      funext i; dsimp [R]; ring
    rw [hfactor, sumQ_smul, ho]
    by_cases hjk : j = k
    · subst k
      simp only [ite_true, mul_one]
      exact_mod_cast hc2 j
    · simp [hjk]
  have hsum : ∀ j, sumQ (fun i => R i j) = 1 := by
    intro j
    change sumQ (fun i => (c j : ℚ) * Q i j) = 1
    rw [sumQ_smul, hc]
    exact_mod_cast hc2 j
  refine ⟨R, hR, regular_of_column_sums R hR hsum, ?_⟩
  intro j
  have he : (fun i => R i j) = (c j) • (fun i => Q i j) := by
    funext i
    simp [R, zsmul_eq_mul]
  rw [he]
  exact (neighbor p u).smul_mem (c j) (hcol j)

#print axioms frame_column_sums
#print axioms orient_neighbor_frame
end Wang38I
