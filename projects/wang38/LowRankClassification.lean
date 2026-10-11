import UnitOrNormFour
import RealUnitSplitting
import NormFourNeighbor
import StandardTransport

/-! Griess's sufficient low-rank classification, reconstructed from the
proved geometric, splitting, and index-two-neighbor components. -/
noncomputable section
namespace Wang38I.Classification
open Module MeasureTheory
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def OddLattice (L : Submodule ℤ E) : Prop :=
  ∃ x ∈ L, ∃ k : ℤ, inner ℝ x x = (k : ℝ) ∧ k % 2 = 1

/-- The only classification needed for Wang38(i): every rank≤7 self-dual
lattice and every odd rank-8 self-dual lattice has an orthonormal integer basis. -/
theorem lowRank_orthonormal_integer_basis
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (hL : LinearMap.BilinForm.dualSubmodule (innerₗ E) L = L)
    (hn8 : Module.finrank ℝ E ≤ 8)
    (hodd : Module.finrank ℝ E ≤ 7 ∨ OddLattice L) :
    ∃ b : Basis (Fin (Module.finrank ℝ E)) ℤ L,
      Orthonormal ℝ (fun i => (b i).val) := by
  generalize hn : Module.finrank ℝ E = n at *
  induction n using Nat.strong_induction_on generalizing E with
  | h n ih =>
    classical
    by_cases hn0 : n = 0
    · have hzero : Module.finrank ℝ E = 0 := hn.trans hn0
      let : Subsingleton E := Module.finrank_zero_iff.mp hzero
      let : Subsingleton L := inferInstance
      rw [hn0]
      refine ⟨Basis.empty L, ?_⟩
      exact orthonormal_iff_ite.mpr (fun i => Fin.elim0 i)
    have hnpos : 0 < n := by omega
    have hstandard_of_unit : ∀ (K : Submodule ℤ E) [DiscreteTopology K] [IsZLattice ℝ K],
        LinearMap.BilinForm.dualSubmodule (innerₗ E) K = K →
        (∃ u ∈ K, inner ℝ u u = 1) →
        ∃ b : Basis (Fin n) ℤ K, Orthonormal ℝ (fun i => (b i).val) := by
      intro K _ _ hK ⟨u, huK, hu⟩
      let : IsZLattice ℝ (rootComplement K u) := realUnitComplement_isZLattice K hK u huK hu
      have hd := realUnitPerp_finrank u hu
      rw [hn] at hd
      have hlt : Module.finrank ℝ (rootPerp u) < n := by omega
      have hle7 : Module.finrank ℝ (rootPerp u) ≤ 7 := by omega
      obtain ⟨bC, hbC⟩ := ih (Module.finrank ℝ (rootPerp u)) hlt
        (rootComplement K u) (realUnitComplement_selfDual K hK u huK hu) rfl
        (by omega) (Or.inl hle7)
      let bE := realUnitExtendBasis K hK u huK hu bC
      have hbE : Orthonormal ℝ (fun i => (bE i).val) :=
        realUnitExtendBasis_orthonormal K hK u huK hu bC hbC
      let e : Unit ⊕ Fin (Module.finrank ℝ (rootPerp u)) ≃ Fin n :=
        Fintype.equivOfCardEq (by simp only [Fintype.card_sum, Fintype.card_unique, Fintype.card_fin]; omega)
      refine ⟨bE.reindex e, ?_⟩
      apply orthonormal_iff_ite.mpr
      intro i j
      have hg := orthonormal_iff_ite.mp hbE (e.symm i) (e.symm j)
      simpa only [Basis.reindex_apply, e.symm.injective.eq_iff] using hg
    by_cases hunit : ∃ u ∈ L, inner ℝ u u = 1
    · exact hstandard_of_unit L hL hunit
    have hn1 : n ≠ 1 := by
      intro hn1
      exact hunit (selfDual_rank_one_has_unit L hL (hn.trans hn1))
    have hn2 : 2 ≤ Module.finrank ℝ E := by omega
    obtain hfound | ⟨v, hvL, hv⟩ := selfDual_unit_or_normFour L hL hn2 (by omega)
    · exact (hunit hfound).elim
    obtain hfound | ⟨K, hKdis, hKrest⟩ := normFour_unit_or_neighbor L hL v hvL hv
    · exact (hunit hfound).elim
    let : DiscreteTopology K := hKdis
    obtain ⟨hKlat, hKdual, hhalf, hhalfNorm, hiL, hiK⟩ := hKrest
    let : IsZLattice ℝ K := hKlat
    obtain ⟨bK, hbK⟩ := hstandard_of_unit K hKdual ⟨(1/2 : ℝ) • v, hhalf, hhalfNorm⟩
    obtain hfound | ⟨hnEq, heven⟩ :=
      indexTwo_orthonormalIntegerBasis_alternative hnpos hn8 L K bK
        (orthonormal_iff_ite.mp hbK) hL hiL hiK
    · exact (hunit hfound).elim
    exfalso
    rcases hodd with hsmall | hodd
    · omega
    · obtain ⟨x, hx, k, hk, hkodd⟩ := hodd
      obtain ⟨a, ha⟩ := heven x hx
      have he : k = 2 * a := by
        apply Int.cast_injective (α := ℝ)
        push_cast
        linarith
      rw [he, Int.mul_emod] at hkodd
      norm_num at hkodd

/-- The odd rank-at-most-eight classification, with no classification
hypothesis or external theorem assumed. -/
theorem odd_lowRank_orthonormal_integer_basis
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (hL : LinearMap.BilinForm.dualSubmodule (innerₗ E) L = L)
    (hn8 : Module.finrank ℝ E ≤ 8) (hodd : OddLattice L) :
    ∃ b : Basis (Fin (Module.finrank ℝ E)) ℤ L,
      Orthonormal ℝ (fun i => (b i).val) :=
  lowRank_orthonormal_integer_basis L hL hn8 (Or.inr hodd)

#print axioms lowRank_orthonormal_integer_basis
#print axioms odd_lowRank_orthonormal_integer_basis
end Wang38I.Classification
