import FrameExtraction

/-! All hypotheses needed on the constructed lattice are derived from the
literal source hypotheses. No dimension-bound classification is assumed. -/
namespace Wang38I
open Wang38

/-- Exact source-to-lattice bridge. The nontrivial remaining all-prime step
is existence of an orthonormal frame in this proved rank-n odd self-dual
lattice when n≤8. -/
theorem source_neighbor {p n : ℕ} (hp : Nat.Prime p) (hodd : p % 2 = 1)
    (hn : 0 < n) (v : IVector n) (hv : Admissible p v) :
    ∃ u : IVector n,
      Admissible p u ∧
      (∀ i, u i % (p : ℤ) = v i % (p : ℤ)) ∧
      (p : ℤ) * p ∣ dotI u u ∧
      Submodule.IsLattice ℚ (neighbor p u) ∧
      Module.finrank ℤ (neighbor p u) = n ∧
      LinearMap.BilinForm.dualSubmodule
        (dotProductBilin ℚ ℚ : LinearMap.BilinForm ℚ (QVector n))
        (neighbor p u) = neighbor p u ∧
      (∀ x ∈ neighbor p u, ∀ y ∈ neighbor p u, Integral (dotQ x y)) ∧
      (∀ x ∈ neighbor p u, x ≠ 0 → 0 < dotQ x x) ∧
      (∃ x ∈ neighbor p u, ∃ z : ℤ, dotQ x x = (z : ℚ) ∧ z % 2 = 1) ∧
      ones n ∈ neighbor p u ∧
      (∀ x ∈ neighbor p u, ∃ z : ℤ, dotQ x x - dotQ (ones n) x = (2 * z : ℤ)) := by
  have hp' : OddPrime p := ⟨hp.two_le, hodd, (Nat.prime_def.mp hp).2⟩
  obtain ⟨u, hua, huv, hun⟩ := exists_admissible_norm_divisible_lift hp' hn v hv
  have huj : ∃ j, u j % (p : ℤ) ≠ 0 := ⟨⟨0, hn⟩, hua.1 ⟨0, hn⟩⟩
  exact ⟨u, hua, huv, hun, neighbor_isLattice hp.ne_zero u,
    neighbor_finrank hp.ne_zero u, neighbor_dualSubmodule hp' u huj hun,
    fun _ hx _ hy => neighbor_integral hp.ne_zero u hun hx hy,
    fun _ hx hne => neighbor_positive hx hne,
    neighbor_is_odd hp' hn u, ones_mem_neighbor u hua.2.1,
    fun _ hx => ones_characteristic hp' u hun hua.2.1 hx⟩

/-- A literal orthonormal Z-basis of the constructed neighbor supplies the
frame used by the completed matrix extraction. This lemma does not assert
existence of that basis. -/
theorem published_matrix_of_orthonormal_Z_basis {p n : ℕ} (hp : OddPrime p)
    (v u : IVector n) (huj : ∃ j, u j % (p : ℤ) ≠ 0)
    (hu : (p : ℤ) * p ∣ dotI u u) (husum : sumI u % (p : ℤ) = 0)
    (hres : ∀ i, u i % (p : ℤ) = v i % (p : ℤ))
    (b : Module.Basis (Fin n) ℤ (neighbor p u))
    (hb : ∀ i j, dotQ (b i).val (b j).val = if i = j then 1 else 0) :
    ∃ R : QMatrix n, PublishedGeneratedPrimitive p v R := by
  apply published_matrix_of_neighbor_frame hp v u huj hu husum hres
    (fun i j => (b j).val i)
  · intro i j
    simpa [dotQ, sumQ, List.sum_ofFn] using hb i j
  · intro j
    exact (b j).prop

#print axioms source_neighbor
#print axioms published_matrix_of_orthonormal_Z_basis
end Wang38I
