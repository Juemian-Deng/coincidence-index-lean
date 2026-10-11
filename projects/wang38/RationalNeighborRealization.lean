import LowRankClassification
import SourceNeighbor
import PublishedStatement

set_option maxHeartbeats 2000000

noncomputable section
open scoped BigOperators
namespace Wang38I
open Wang38

/-- Coordinatewise rational inclusion into genuine real Euclidean space. -/
def rationalRealMap (n : ℕ) : QVector n →ₗ[ℤ] EuclideanSpace ℝ (Fin n) where
  toFun x := WithLp.toLp 2 (fun i => (x i : ℝ))
  map_add' x y := by ext i; simp
  map_smul' a x := by ext i; simp

@[simp] lemma rationalRealMap_apply {n : ℕ} (x : QVector n) (i : Fin n) :
    rationalRealMap n x i = (x i : ℝ) := rfl

lemma rationalRealMap_injective (n : ℕ) : Function.Injective (rationalRealMap n) := by
  intro x y h
  ext i
  exact Rat.cast_injective (congrArg (fun z : EuclideanSpace ℝ (Fin n) => z i) h)

@[simp] lemma rationalRealMap_inner {n : ℕ} (x y : QVector n) :
    inner ℝ (rationalRealMap n x) (rationalRealMap n y) = (dotQ x y : ℝ) := by
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, dotQ, mul_comm]

def realNeighbor (p : ℕ) {n : ℕ} (u : IVector n) : Submodule ℤ (EuclideanSpace ℝ (Fin n)) :=
  (neighbor p u).map (rationalRealMap n)

lemma rational_coordinate_mem {p n : ℕ} (u : IVector n) (i : Fin n) :
    (fun j => if j = i then (p : ℚ) else 0) ∈ neighbor p u := by
  classical
  have h := base_mem_neighbor (p := p) u
    (fun j => if j = i then (p : ℤ) else 0) (by simp [dotI, sumI, List.sum_ofFn])
  convert h using 1
  ext j
  simp [Wang38I.castVector]

lemma real_coordinate_mem {p n : ℕ} (u : IVector n) (i : Fin n) :
    (p : ℝ) • EuclideanSpace.basisFun (Fin n) ℝ i ∈ realNeighbor p u := by
  refine ⟨_, rational_coordinate_mem u i, ?_⟩
  ext j
  simp [EuclideanSpace.basisFun_apply, eq_comm]
  split_ifs <;> simp_all

lemma realNeighbor_span {p n : ℕ} (hp : p ≠ 0) (u : IVector n) :
    Submodule.span ℝ (realNeighbor p u : Set (EuclideanSpace ℝ (Fin n))) = ⊤ := by
  apply top_unique
  rw [← (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.span_eq]
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  have h := Submodule.subset_span (R := ℝ) (real_coordinate_mem (p := p) u i)
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp
  have h2 := (Submodule.span ℝ (realNeighbor p u : Set (EuclideanSpace ℝ (Fin n)))).smul_mem (p : ℝ)⁻¹ h
  rw [smul_smul, inv_mul_cancel₀ hpR, one_smul] at h2
  exact h2

lemma integral_cast_iff (q : ℚ) :
    (q : ℝ) ∈ (1 : Submodule ℤ ℝ) ↔ q ∈ (1 : Submodule ℤ ℚ) := by
  simp only [Submodule.mem_one]
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨z, by change (z : ℝ) = (q : ℝ) at hz; change (z : ℚ) = q; exact_mod_cast hz⟩
  · rintro ⟨z, hz⟩
    exact ⟨z, by change (z : ℚ) = q at hz; change (z : ℝ) = (q : ℝ); exact_mod_cast hz⟩

lemma realNeighbor_selfDual {p n : ℕ} (hp : p ≠ 0) (u : IVector n)
    (hdual : LinearMap.BilinForm.dualSubmodule
      (dotProductBilin ℚ ℚ : LinearMap.BilinForm ℚ (QVector n))
      (neighbor p u) = neighbor p u) :
    LinearMap.BilinForm.dualSubmodule (innerₗ _) (realNeighbor p u) = realNeighbor p u := by
  classical
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp
  ext x
  constructor
  · intro hx
    have hc : ∀ i : Fin n, ∃ z : ℤ, (z : ℝ) = (p : ℝ) * x i := by
      intro i
      have h := hx _ (real_coordinate_mem u i)
      change inner ℝ x ((p : ℝ) • EuclideanSpace.basisFun (Fin n) ℝ i) ∈ (1 : Submodule ℤ ℝ) at h
      simpa [inner_smul_right, EuclideanSpace.inner_eq_star_dotProduct,
        EuclideanSpace.basisFun_apply, dotProduct, Pi.single_apply] using Submodule.mem_one.mp h
    choose z hz using hc
    let q : QVector n := fun i => (z i : ℚ) / p
    have he : rationalRealMap n q = x := by
      ext i
      simp only [rationalRealMap_apply, q, Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast]
      rw [hz i, mul_div_cancel_left₀ _ hpR]
    refine ⟨q, ?_, he⟩
    rw [← hdual]
    intro y hy
    have h := hx (rationalRealMap n y) ⟨y, hy, rfl⟩
    change inner ℝ x (rationalRealMap n y) ∈ (1 : Submodule ℤ ℝ) at h
    rw [← he, rationalRealMap_inner, integral_cast_iff] at h
    exact h
  · rintro ⟨q, hq, rfl⟩ y ⟨r, hr, rfl⟩
    change inner ℝ (rationalRealMap n q) (rationalRealMap n r) ∈ (1 : Submodule ℤ ℝ)
    rw [rationalRealMap_inner, integral_cast_iff]
    rw [← hdual] at hq
    exact hq r hr

lemma integral_selfDual_discrete {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (L : Submodule ℤ E)
    (hL : LinearMap.BilinForm.dualSubmodule (innerₗ E) L = L) : DiscreteTopology L := by
  apply discreteTopology_of_isOpen_singleton_zero
  have he : Metric.ball (0 : L) 1 = {0} := by
    ext x
    simp only [Metric.mem_ball, dist_zero_right, Set.mem_singleton_iff]
    constructor
    · intro hx
      obtain ⟨k, hk⟩ := Classification.selfDual_inner_integral L hL x.prop x.prop
      have hn : inner ℝ (x : E) x = ‖(x : E)‖ ^ 2 := real_inner_self_eq_norm_sq _
      have hp : 0 ≤ k := by exact_mod_cast (show (0 : ℝ) ≤ k by rw [← hk, hn]; positivity)
      have hlt : k < 1 := by
        have hnx : ‖(x : E)‖ < 1 := hx
        have hnn := norm_nonneg (x : E)
        have : (k : ℝ) < 1 := by nlinarith
        exact_mod_cast this
      have hk0 : k = 0 := by omega
      apply Subtype.ext
      apply norm_eq_zero.mp
      have : ‖(x : E)‖ ^ 2 = 0 := by rw [← hn, hk, hk0]; norm_num
      nlinarith [norm_nonneg (x : E)]
    · rintro rfl
      simp
  rw [← he]
  exact Metric.isOpen_ball

lemma realNeighbor_isZLattice {p n : ℕ} (hp : p ≠ 0) (u : IVector n)
    [DiscreteTopology (realNeighbor p u)] : IsZLattice ℝ (realNeighbor p u) :=
  ⟨realNeighbor_span hp u⟩

/-- The rational prime-neighbor inherits an orthonormal integer basis from
its literal real realization and the proved low-rank classification. -/
theorem rationalNeighbor_orthonormal_basis {p n : ℕ} (hp : p ≠ 0) (hn8 : n ≤ 8)
    (u : IVector n)
    (hdual : LinearMap.BilinForm.dualSubmodule
      (dotProductBilin ℚ ℚ : LinearMap.BilinForm ℚ (QVector n))
      (neighbor p u) = neighbor p u)
    (hodd : ∃ x ∈ neighbor p u, ∃ z : ℤ, dotQ x x = (z : ℚ) ∧ z % 2 = 1) :
    ∃ b : Module.Basis (Fin n) ℤ (neighbor p u),
      ∀ i j, dotQ (b i).val (b j).val = if i = j then 1 else 0 := by
  classical
  have hd := realNeighbor_selfDual hp u hdual
  let := integral_selfDual_discrete (realNeighbor p u) hd
  let := realNeighbor_isZLattice hp u
  have ho : Classification.OddLattice (realNeighbor p u) := by
    obtain ⟨x, hx, z, hz, hpz⟩ := hodd
    refine ⟨rationalRealMap n x, ⟨x, hx, rfl⟩, z, ?_, hpz⟩
    rw [rationalRealMap_inner, hz]
    simp
  obtain ⟨bR, hbR⟩ := Classification.odd_lowRank_orthonormal_integer_basis
    (realNeighbor p u) hd (by simpa using hn8) ho
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := by simp
  let bR' : Module.Basis (Fin n) ℤ (realNeighbor p u) := bR.reindex (finCongr hdim)
  have hbR' : ∀ i j, inner ℝ (bR' i).val (bR' j).val = if i = j then 1 else 0 := by
    intro i j
    simpa [bR'] using orthonormal_iff_ite.mp hbR ((finCongr hdim).symm i) ((finCongr hdim).symm j)
  let e := Submodule.equivMapOfInjective (rationalRealMap n) (rationalRealMap_injective n) (neighbor p u)
  let b := bR'.map e.symm
  refine ⟨b, ?_⟩
  intro i j
  have hi : rationalRealMap n (b i).val = (bR' i).val :=
    Submodule.map_equivMapOfInjective_symm_apply (rationalRealMap n) (rationalRealMap_injective n) (neighbor p u) (bR' i)
  have hj : rationalRealMap n (b j).val = (bR' j).val :=
    Submodule.map_equivMapOfInjective_symm_apply (rationalRealMap n) (rationalRealMap_injective n) (neighbor p u) (bR' j)
  have h := hbR' i j
  rw [← hi, ← hj, rationalRealMap_inner] at h
  apply Rat.cast_injective (α := ℝ)
  simpa only [apply_ite, Rat.cast_one, Rat.cast_zero] using h

/-- Wang's published Conjecture 3.8(i), including every odd prime and
all source dimensions at most eight. -/
theorem published_conjecture38I : Wang38.PublishedConjecture38I := by
  intro p n hp hodd hn hn8 v hv
  obtain ⟨u, hua, huv, hun, _, _, hdual, _, _, huodd, _⟩ :=
    source_neighbor hp hodd hn v hv
  obtain ⟨b, hb⟩ := rationalNeighbor_orthonormal_basis hp.ne_zero hn8 u hdual huodd
  have hp' : OddPrime p := ⟨hp.two_le, hodd, (Nat.prime_def.mp hp).2⟩
  exact published_matrix_of_orthonormal_Z_basis hp' v u
    ⟨⟨0, hn⟩, hua.1 ⟨0, hn⟩⟩ hun hua.2.1 huv b hb

#print axioms rationalRealMap_injective
#print axioms rationalRealMap_inner
#print axioms realNeighbor_span
#print axioms realNeighbor_selfDual
#print axioms integral_selfDual_discrete
#print axioms realNeighbor_isZLattice
#print axioms rationalNeighbor_orthonormal_basis
#print axioms published_conjecture38I
end Wang38I
