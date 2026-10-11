import SelfDual
import Mathlib.Algebra.Module.Lattice
import Mathlib.LinearAlgebra.BilinearForm.DualLattice

/-! Bridge the concrete neighbor to Mathlib's actual lattice and dual notions. -/
open scoped BigOperators
namespace Wang38I
open Wang38

def fractionalCast (p n : ℕ) : IVector n →ₗ[ℤ] QVector n where
  toFun m i := (m i : ℚ) / p
  map_add' m r := by ext i; simp [add_div]
  map_smul' a m := by
    ext i
    simp only [Pi.smul_apply, smul_eq_mul, Int.cast_mul, zsmul_eq_mul, RingHom.id_apply]
    ring

/-- Finite generation is proved by embedding in (1/p)ℤ^n. -/
theorem neighbor_fg {p n : ℕ} (hp : p ≠ 0) (u : IVector n) :
    (neighbor p u).FG := by
  have hpQ : (p : ℚ) ≠ 0 := by exact_mod_cast hp
  apply (Submodule.fg_range (fractionalCast p n)).of_le
  intro x hx
  obtain ⟨a, ha, _⟩ := neighbor_numerator hx
  refine ⟨a, ?_⟩
  ext i
  change (a i : ℚ) / p = x i
  rw [ha, mul_div_cancel_left₀ _ hpQ]

/-- The rational span is all of Q^n, since p times every standard coordinate
vector lies in the neighbor. -/
theorem neighbor_span {p n : ℕ} (hp : p ≠ 0) (u : IVector n) :
    Submodule.span ℚ (neighbor p u : Set (QVector n)) = ⊤ := by
  classical
  have hpQ : (p : ℚ) ≠ 0 := by exact_mod_cast hp
  apply top_le_iff.mp
  rw [← (Pi.basisFun ℚ (Fin n)).span_eq]
  apply Submodule.span_le.mpr
  rintro x ⟨j, rfl⟩
  let m : IVector n := fun i => if i = j then (p : ℤ) else 0
  have hm : castVector m ∈ neighbor p u := by
    apply base_mem_neighbor
    rw [dotI_comm]
    dsimp [m]
    rw [dotI_single]
    exact dvd_mul_left _ _
  have h := (Submodule.span ℚ (neighbor p u : Set (QVector n))).smul_mem
    ((p : ℚ)⁻¹) (Submodule.subset_span hm)
  have he : (Pi.basisFun ℚ (Fin n)) j = ((p : ℚ)⁻¹) • castVector m := by
    ext i
    by_cases hij : i = j
    · subst i
      simp [Pi.basisFun_apply, castVector, m, hpQ]
    · simp [Pi.basisFun_apply, castVector, m, hij]
  rw [he]
  exact h

/-- The constructed submodule satisfies Mathlib's lattice class. -/
theorem neighbor_isLattice {p n : ℕ} (hp : p ≠ 0) (u : IVector n) :
    Submodule.IsLattice ℚ (neighbor p u) :=
  ⟨neighbor_fg hp u, neighbor_span hp u⟩

theorem neighbor_finrank {p n : ℕ} (hp : p ≠ 0) (u : IVector n) :
    Module.finrank ℤ (neighbor p u) = n := by
  let : Submodule.IsLattice ℚ (neighbor p u) := neighbor_isLattice hp u
  simpa using Submodule.IsLattice.finrank_of_pi ℚ (neighbor p u)

/-- Literal equality to Mathlib's bilinear-form dual submodule. -/
theorem neighbor_dualSubmodule {p n : ℕ} (hp : OddPrime p)
    (u : IVector n) (huj : ∃ j, u j % (p : ℤ) ≠ 0)
    (hu : (p : ℤ) * p ∣ dotI u u) :
    LinearMap.BilinForm.dualSubmodule
      (dotProductBilin ℚ ℚ : LinearMap.BilinForm ℚ (QVector n))
      (neighbor p u) = neighbor p u := by
  ext x
  rw [← neighbor_self_dual hp u huj hu x]
  simp only [LinearMap.BilinForm.mem_dualSubmodule, Submodule.mem_one]
  constructor
  · intro h y hy
    obtain ⟨z, hz⟩ := h y hy
    exact ⟨z, hz.symm⟩
  · intro h y hy
    obtain ⟨z, hz⟩ := h y hy
    exact ⟨z, hz.symm⟩

#print axioms neighbor_isLattice
#print axioms neighbor_finrank
#print axioms neighbor_dualSubmodule
end Wang38I
