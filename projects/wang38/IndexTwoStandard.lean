import CovolumeGram
import Mathlib.GroupTheory.Index

/-! The index-two standard-lattice alternative.

The proof first passes to the no-unit case. Self-duality then forces every
coordinate of the nonzero intersection coset to be half an odd integer.
The index-two condition on the standard lattice permits a sign adjustment
of one half-coordinate, producing an actual lattice vector of square n/4.
Integrality and n ≤ 8 force n = 8. Elementary integer parity, together with
integral pairings, proves evenness on both intersection cosets.

Neither a half-integer normal form nor a parity-support classification is
assumed. The theorem is algebraic and therefore also applies to every actual
discrete full lattice satisfying its hypotheses.
-/
noncomputable section
open scoped BigOperators
namespace Wang38I.Classification

abbrev standardIntegerLattice (n : ℕ) : Submodule ℤ (EuclideanSpace ℝ (Fin n)) :=
  Submodule.span ℤ (Set.range (EuclideanSpace.basisFun (Fin n) ℝ))

lemma mem_standardIntegerLattice {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) :
    x ∈ standardIntegerLattice n ↔ ∀ i, ∃ k : ℤ, (k : ℝ) = x i := by
  simpa only [standardIntegerLattice, OrthonormalBasis.coe_toBasis,
    OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr,
    Set.mem_range, algebraMap_int_eq, Int.coe_castRingHom]
    using (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.mem_span_iff_repr_mem ℤ x

lemma standardIntegerLattice_inner {n : ℕ} {x y : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ standardIntegerLattice n) (hy : y ∈ standardIntegerLattice n) :
    ∃ k : ℤ, (k : ℝ) = inner ℝ x y := by
  obtain ⟨a, ha⟩ := Classical.axiomOfChoice ((mem_standardIntegerLattice x).mp hx)
  obtain ⟨b, hb⟩ := Classical.axiomOfChoice ((mem_standardIntegerLattice y).mp hy)
  refine ⟨∑ i, a i * b i, ?_⟩
  simp only [Int.cast_sum, Int.cast_mul, ha, hb, PiLp.inner_apply, RCLike.inner_apply,
    conj_trivial]
  congr 1
  funext i
  ring

lemma indexTwo_double_mem {E : Type*} [AddCommGroup E] [Module ℤ E]
    (L Z : Submodule ℤ E)
    (h : (L ⊓ Z).toAddSubgroup.relIndex L.toAddSubgroup = 2)
    {x : E} (hx : x ∈ L) : (2 : ℤ) • x ∈ Z := by
  have hh := AddSubgroup.two_smul_mem_of_index_two h (⟨x, hx⟩ : L)
  have hxx : x + x ∈ Z := by simpa [two_smul] using hh.2
  simpa only [two_zsmul] using hxx

lemma indexTwo_coset_representative {E : Type*} [AddCommGroup E] [Module ℤ E]
    (L Z : Submodule ℤ E)
    (h : (L ⊓ Z).toAddSubgroup.relIndex L.toAddSubgroup = 2) :
    ∃ a ∈ L, a ∉ Z ∧ ∀ x ∈ L, x + a ∈ Z ∨ x ∈ Z := by
  obtain ⟨a, ha, hnot, hcos⟩ := AddSubgroup.relIndex_eq_two_iff_exists_notMem_and.mp h
  refine ⟨a, ha, fun hz => hnot ⟨ha, hz⟩, ?_⟩
  intro x hx
  exact (hcos x hx).imp (fun h => h.2) (fun h => h.2)


lemma indexTwo_integral_test {n : ℕ} (L : Submodule ℤ (EuclideanSpace ℝ (Fin n)))
    (hL : LinearMap.BilinForm.dualSubmodule (innerₗ _) L = L)
    (a : EuclideanSpace ℝ (Fin n))
    (hcos : ∀ x ∈ L, x + a ∈ standardIntegerLattice n ∨ x ∈ standardIntegerLattice n)
    {z : EuclideanSpace ℝ (Fin n)} (hz : z ∈ standardIntegerLattice n)
    (haz : ∃ k : ℤ, (k : ℝ) = inner ℝ z a) : z ∈ L := by
  rw [← hL]
  intro y hy
  apply Submodule.mem_one.mpr
  rcases hcos y hy with h | h
  · obtain ⟨b, hb⟩ := standardIntegerLattice_inner hz h
    obtain ⟨k, hk⟩ := haz
    refine ⟨b - k, ?_⟩
    change ((b - k : ℤ) : ℝ) = inner ℝ z y
    rw [Int.cast_sub, hb, hk, inner_add_right]
    ring
  · exact standardIntegerLattice_inner hz h

lemma indexTwo_noUnit_representative_nonintegral {n : ℕ}
    (L : Submodule ℤ (EuclideanSpace ℝ (Fin n)))
    (hL : LinearMap.BilinForm.dualSubmodule (innerₗ _) L = L)
    (hunit : ¬ ∃ v ∈ L, inner ℝ v v = 1)
    (a : EuclideanSpace ℝ (Fin n))
    (hcos : ∀ x ∈ L, x + a ∈ standardIntegerLattice n ∨ x ∈ standardIntegerLattice n)
    (i : Fin n) : ¬ ∃ k : ℤ, (k : ℝ) = a i := by
  intro hi
  let e := EuclideanSpace.basisFun (Fin n) ℝ i
  have heZ : e ∈ standardIntegerLattice n := Submodule.subset_span ⟨i, rfl⟩
  have hea : ∃ k : ℤ, (k : ℝ) = inner ℝ e a := by
    simpa only [e, EuclideanSpace.basisFun_inner] using hi
  exact hunit ⟨e, indexTwo_integral_test L hL a hcos heZ hea,
    (EuclideanSpace.basisFun (Fin n) ℝ).inner_eq_one i⟩

lemma half_integer_of_double_integer (x : ℝ) (hx : ∃ k : ℤ, (k : ℝ) = 2*x)
    (hnot : ¬ ∃ k : ℤ, (k : ℝ) = x) : ∃ k : ℤ, x = k + 1/2 := by
  obtain ⟨b, hb⟩ := hx
  have hbodd : b % 2 = 1 := by
    by_contra h
    have he : b % 2 = 0 := by omega
    obtain ⟨k, hk⟩ := Int.dvd_of_emod_eq_zero he
    apply hnot
    refine ⟨k, ?_⟩
    rw [hk, Int.cast_mul] at hb
    norm_num at hb
    linarith
  refine ⟨b / 2, ?_⟩
  have h : b = b / 2 * 2 + 1 := by omega
  have hc : (b : ℝ) = (b / 2 : ℤ) * 2 + 1 := by exact_mod_cast h
  linarith


lemma indexTwo_noUnit_half_coordinates {n : ℕ}
    (L : Submodule ℤ (EuclideanSpace ℝ (Fin n)))
    (hL : LinearMap.BilinForm.dualSubmodule (innerₗ _) L = L)
    (hunit : ¬ ∃ v ∈ L, inner ℝ v v = 1)
    (hi : (L ⊓ standardIntegerLattice n).toAddSubgroup.relIndex L.toAddSubgroup = 2) :
    ∃ a ∈ L, ∃ k : Fin n → ℤ, (∀ i, a i = k i + 1/2) ∧
      ∀ x ∈ L, x + a ∈ standardIntegerLattice n ∨ x ∈ standardIntegerLattice n := by
  obtain ⟨a, ha, _, hcos⟩ := indexTwo_coset_representative L (standardIntegerLattice n) hi
  have h2 := (mem_standardIntegerLattice _).mp
    (indexTwo_double_mem L (standardIntegerLattice n) hi ha)
  have hc : ∀ i, ∃ k : ℤ, a i = k + 1/2 := by
    intro i
    apply half_integer_of_double_integer
    · simpa using h2 i
    · exact indexTwo_noUnit_representative_nonintegral L hL hunit a hcos i
  obtain ⟨k, hk⟩ := Classical.axiomOfChoice hc
  exact ⟨a, ha, k, hk, hcos⟩

lemma indexTwo_toggle {E : Type*} [AddCommGroup E] [Module ℤ E]
    (L Z : Submodule ℤ E)
    (h : (L ⊓ Z).toAddSubgroup.relIndex Z.toAddSubgroup = 2)
    {e z : E} (he : e ∈ Z) (hz : z ∈ Z) (henot : e ∉ L) :
    z ∈ L ∨ z + e ∈ L := by
  by_cases hzL : z ∈ L
  · exact Or.inl hzL
  · right
    have hh := (AddSubgroup.add_mem_iff_of_index_two h
      (a := (⟨z, hz⟩ : Z)) (b := (⟨e, he⟩ : Z))).mpr
      (by change (z ∈ L ∧ z ∈ Z ↔ e ∈ L ∧ e ∈ Z); simp [hzL, henot])
    exact hh.1

lemma indexTwo_noUnit_minimal_half_vector {n : ℕ} (hn : 0 < n)
    (L : Submodule ℤ (EuclideanSpace ℝ (Fin n)))
    (hunit : ¬ ∃ v ∈ L, inner ℝ v v = 1)
    (hi : (L ⊓ standardIntegerLattice n).toAddSubgroup.relIndex
      (standardIntegerLattice n).toAddSubgroup = 2)
    (a : EuclideanSpace ℝ (Fin n)) (ha : a ∈ L)
    (k : Fin n → ℤ) (hk : ∀ i, a i = k i + 1/2) :
    ∃ v ∈ L, inner ℝ v v = (n : ℝ)/4 := by
  let z : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun i => (k i : ℝ))
  let i0 : Fin n := ⟨0, hn⟩
  let e := EuclideanSpace.basisFun (Fin n) ℝ i0
  have hz : z ∈ standardIntegerLattice n := (mem_standardIntegerLattice _).mpr
    (fun i => ⟨k i, rfl⟩)
  have he : e ∈ standardIntegerLattice n := Submodule.subset_span ⟨i0, rfl⟩
  have henot : e ∉ L := fun heL => hunit ⟨e, heL,
    (EuclideanSpace.basisFun (Fin n) ℝ).inner_eq_one i0⟩
  rcases indexTwo_toggle L (standardIntegerLattice n) hi he hz henot with h | h
  · refine ⟨a-z, L.sub_mem ha h, ?_⟩
    have hv : ∀ i, (a-z) i = 1/2 := by intro i; simp [z, hk]
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, hv]
    simp
    ring
  · refine ⟨a-(z+e), L.sub_mem ha h, ?_⟩
    have hv : ∀ i, (a-(z+e)) i * (a-(z+e)) i = (1/4 : ℝ) := by
      intro i
      by_cases hh : i = i0
      · subst i
        simp [z, e, EuclideanSpace.basisFun_apply, hk]
        ring
      · simp [z, e, EuclideanSpace.basisFun_apply, hk, hh]
        ring
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, hv,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, div_eq_mul_inv, one_mul]


lemma half_coordinates_norm {n : ℕ} (a : EuclideanSpace ℝ (Fin n))
    (k : Fin n → ℤ) (hk : ∀ i, a i = k i + 1/2) :
    ∃ m : ℤ, inner ℝ a a = (n : ℝ)/4 + 2*m := by
  have he : ∀ i, ∃ b : ℤ, k i * (k i + 1) = 2*b := by
    intro i
    obtain ⟨b, hb⟩ := Int.even_mul_succ_self (k i)
    exact ⟨b, by omega⟩
  obtain ⟨b, hb⟩ := Classical.axiomOfChoice he
  refine ⟨∑ i, b i, ?_⟩
  have hi : ∀ i, a i * a i = (1/4 : ℝ) + 2*(b i : ℝ) := by
    intro i
    have hi : (k i : ℝ) * (k i + 1) = 2*(b i : ℝ) := by exact_mod_cast hb i
    rw [hk]
    nlinarith
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, hi,
    Finset.sum_add_distrib, ← Finset.mul_sum, Int.cast_sum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

lemma integer_vector_even_norm_of_half_pairing {n : ℕ}
    (a x : EuclideanSpace ℝ (Fin n)) (k : Fin n → ℤ)
    (hk : ∀ i, a i = k i + 1/2) (hx : x ∈ standardIntegerLattice n)
    (hax : ∃ p : ℤ, (p : ℝ) = inner ℝ a x) :
    ∃ m : ℤ, inner ℝ x x = 2*m := by
  obtain ⟨z, hz⟩ := Classical.axiomOfChoice ((mem_standardIntegerLattice _).mp hx)
  have he : ∀ i, ∃ b : ℤ, z i * (z i - 1) = 2*b := by
    intro i
    obtain ⟨b, hb⟩ := Int.even_mul_pred_self (z i)
    exact ⟨b, by omega⟩
  obtain ⟨b, hb⟩ := Classical.axiomOfChoice he
  obtain ⟨p, hp⟩ := hax
  refine ⟨p - ∑ i, k i*z i + ∑ i, b i, ?_⟩
  have hi : ∀ i, x i * x i = 2*(a i*x i) - 2*((k i : ℝ)*z i) + 2*(b i : ℝ) := by
    intro i
    have hi : (z i : ℝ) * (z i - 1) = 2*(b i : ℝ) := by exact_mod_cast hb i
    rw [← hz i, hk]
    nlinarith
  have hp' : (p : ℝ) = ∑ i, a i*x i := by
    simpa only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, mul_comm] using hp
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, hi,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Int.cast_add, Int.cast_sub, Int.cast_sum, Int.cast_mul]
  rw [← hp']
  ring

lemma indexTwo_inner_integral {n : ℕ} (L : Submodule ℤ (EuclideanSpace ℝ (Fin n)))
    (hL : LinearMap.BilinForm.dualSubmodule (innerₗ _) L = L)
    {x y : EuclideanSpace ℝ (Fin n)} (hx : x ∈ L) (hy : y ∈ L) :
    ∃ k : ℤ, (k : ℝ) = inner ℝ x y := by
  have hx' : x ∈ LinearMap.BilinForm.dualSubmodule (innerₗ _) L := by rwa [hL]
  exact Submodule.mem_one.mp (hx' y hy)

/-- The index-two alternative is derived from literal self-duality and the
actual intersection indices; no half-coordinate normal form is assumed. -/
theorem indexTwo_standard_alternative {n : ℕ} (hn : 0 < n) (hn8 : n ≤ 8)
    (L : Submodule ℤ (EuclideanSpace ℝ (Fin n)))
    (hL : LinearMap.BilinForm.dualSubmodule (innerₗ _) L = L)
    (hiL : (L ⊓ standardIntegerLattice n).toAddSubgroup.relIndex L.toAddSubgroup = 2)
    (hiZ : (L ⊓ standardIntegerLattice n).toAddSubgroup.relIndex
      (standardIntegerLattice n).toAddSubgroup = 2) :
    (∃ v ∈ L, inner ℝ v v = 1) ∨
      (n = 8 ∧ ∀ x ∈ L, ∃ m : ℤ, inner ℝ x x = 2*m) := by
  by_cases hunit : ∃ v ∈ L, inner ℝ v v = 1
  · exact Or.inl hunit
  right
  obtain ⟨a, ha, k, hk, hcos⟩ := indexTwo_noUnit_half_coordinates L hL hunit hiL
  obtain ⟨v, hv, hvnorm⟩ := indexTwo_noUnit_minimal_half_vector hn L hunit hiZ a ha k hk
  obtain ⟨q, hq⟩ := indexTwo_inner_integral L hL hv hv
  have hnq : (n : ℤ) = 4*q := by
    have hreal : (n : ℝ) = 4*(q : ℝ) := by rw [hvnorm] at hq; linarith
    exact_mod_cast hreal
  have hn4 : n ≠ 4 := by
    intro hn4
    apply hunit
    exact ⟨v, hv, by simpa [hn4] using hvnorm⟩
  have hn8eq : n = 8 := by omega
  refine ⟨hn8eq, ?_⟩
  have hevenZ : ∀ x ∈ L, x ∈ standardIntegerLattice n → ∃ m : ℤ, inner ℝ x x = 2*m := by
    intro x hx hxZ
    exact integer_vector_even_norm_of_half_pairing a x k hk hxZ
      (indexTwo_inner_integral L hL ha hx)
  obtain ⟨r, hr⟩ := half_coordinates_norm a k hk
  have haeven : inner ℝ a a = 2*((r+1 : ℤ) : ℝ) := by
    simp only [hn8eq] at hr
    push_cast
    norm_num at hr
    rw [real_inner_self_eq_norm_sq]
    linarith
  intro x hx
  rcases hcos x hx with h | h
  · obtain ⟨s, hs⟩ := hevenZ (x+a) (L.add_mem hx ha) h
    obtain ⟨t, ht⟩ := indexTwo_inner_integral L hL hx ha
    refine ⟨s - (r+1) - t, ?_⟩
    rw [inner_add_left, inner_add_right, inner_add_right,
      haeven] at hs
    have ht' : inner ℝ a x = (t : ℝ) := (real_inner_comm _ _).trans ht.symm
    rw [← ht, ht'] at hs
    push_cast at hs
    push_cast
    linarith
  · exact hevenZ x hx h

/-- Norm-square formulation for geometric applications. -/
theorem indexTwo_standard_norm_sq_alternative {n : ℕ} (hn : 0 < n) (hn8 : n ≤ 8)
    (L : Submodule ℤ (EuclideanSpace ℝ (Fin n)))
    (hL : LinearMap.BilinForm.dualSubmodule (innerₗ _) L = L)
    (hiL : (L ⊓ standardIntegerLattice n).toAddSubgroup.relIndex L.toAddSubgroup = 2)
    (hiZ : (L ⊓ standardIntegerLattice n).toAddSubgroup.relIndex
      (standardIntegerLattice n).toAddSubgroup = 2) :
    (∃ v ∈ L, ‖v‖^2 = 1) ∨
      (n = 8 ∧ ∀ x ∈ L, ∃ m : ℤ, ‖x‖^2 = 2*m) := by
  simpa only [real_inner_self_eq_norm_sq] using
    indexTwo_standard_alternative hn hn8 L hL hiL hiZ

#print axioms indexTwo_standard_norm_sq_alternative
#print axioms indexTwo_standard_alternative
#print axioms indexTwo_double_mem
#print axioms indexTwo_integral_test
end Wang38I.Classification
