import ActualFiberBounds
import IntegerEvenCore

namespace ActualLargeClassBound
open scoped BigOperators
open ResidueParityBridge ActualFiberBounds

noncomputable section
local instance (α : Type*) : DecidableEq α := Classical.decEq α
variable {n : ℕ} (P : Matrix (Fin n) (Fin n) ℤ) (d : ℕ) [NeZero d]

/-- The actual dual-row count combined with an explicit integer column
normalization. This intermediate theorem still displays all structural
normal-form premises; its conclusion is an actual-image bound. -/
theorem bound_from_reduced_column (j : Fin n) (I : Finset (Fin n))
    (w : Fin n → ℤ) (δ a : ℤ)
    (hI : 0 < I.card) (ha : 0 < a)
    (hcol : ∀ i, P i j = δ * w i)
    (hcap : (I.card : ℤ) * a ≤ 2 * (addOrderOf (columnLabel P d j) : ℤ))
    (henergy : ∑ i ∈ Finset.univ \ I, (w i)^2 =
      2 * (addOrderOf (columnLabel P d j) : ℤ) * a - (I.card : ℤ) * a^2)
    (hrows : ∀ i, rowEvaluation P d i ≠ 0)
    (hrowcap : ∀ i, (signClass (rowEvaluation P d) i).card ≤ I.card) :
    n ≤ 2 * Nat.card (ResidueImage P d) := by
  classical
  let g := columnLabel P d j
  let q := Nat.card (AddMonoidHom.eval g : (ResidueImage P d →+ ZMod d) →+ ZMod d).ker
  let : Finite (ResidueImage P d →+ ZMod d) :=
    Finite.of_injective (fun f : ResidueImage P d →+ ZMod d =>
      (f : ResidueImage P d → ZMod d)) DFunLike.coe_injective
  have hq : 0 < q := Nat.card_pos
  have hg : 0 < addOrderOf g := addOrderOf_pos g
  have han : 0 < a.toNat := by omega
  let bin : Fin n → Fin a.toNat := fun i =>
    ⟨(w i).natAbs % a.toNat, Nat.mod_lt _ han⟩
  let zeroBin : Fin a.toNat := ⟨0, han⟩
  let L := (Finset.univ \ I).filter (fun i => ¬a^2 ≤ (w i)^2)
  have hbin (i : Fin n) (hi : i ∈ L) : (bin i).val = (w i).natAbs := by
    have hs : ¬ a^2 ≤ (w i)^2 := (Finset.mem_filter.mp hi).2
    have hw : |w i| < a := by nlinarith [sq_abs (w i), abs_nonneg (w i)]
    have hw' : (w i).natAbs < a.toNat := by
      have hh : ((w i).natAbs : ℤ) < (a.toNat : ℤ) := by
        simpa only [Int.natCast_natAbs, Int.toNat_of_nonneg (le_of_lt ha)] using hw
      exact_mod_cast hh
    exact Nat.mod_eq_of_lt hw'
  have hsub (b : Fin a.toNat) :
      L.filter (fun i => bin i = b) ⊆ Finset.univ.filter (fun i => |w i| = (b.val : ℤ)) := by
    intro i hi
    obtain ⟨hiL, hib⟩ := Finset.mem_filter.mp hi
    have hv : (w i).natAbs = b.val := (hbin i hiL).symm.trans (congrArg Fin.val hib)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← Int.natCast_natAbs, hv]
  have hz : ((L.filter (fun i => bin i = zeroBin)).card : ℤ) ≤ (I.card : ℤ) * ((q : ℤ)-1) := by
    have hc := (Finset.card_le_card (hsub zeroBin)).trans
      (zero_bin_card_le P d w j δ I.card hcol hrows hrowcap)
    have hqm : ((q - 1 : ℕ) : ℤ) = (q : ℤ)-1 := by omega
    have hci : ((L.filter (fun i => bin i = zeroBin)).card : ℤ) ≤
        (I.card : ℤ) * ((q-1 : ℕ) : ℤ) := by exact_mod_cast hc
    simpa only [hqm] using hci
  have ho (b : Fin a.toNat) (_hb : b ≠ zeroBin) :
      ((L.filter (fun i => bin i = b)).card : ℤ) ≤ (I.card : ℤ) * (q : ℤ) := by
    have hc := (Finset.card_le_card (hsub b)).trans
      (abs_bin_card_le P d w j δ b.val I.card hcol hrowcap)
    exact_mod_cast hc
  have hbound := DualFiberCounting.finite_partition_from_bins
    (Finset.univ : Finset (Fin n)) I w (addOrderOf g) q a bin zeroBin
    (by simp only [Fintype.card_fin, Int.toNat_of_nonneg (le_of_lt ha)])
    (Finset.subset_univ _) hI (by exact_mod_cast hg) (by exact_mod_cast hq) ha
    hcap henergy hz ho
  have hcard := DualCardinality.card_eval_ker_mul_order d g (image_annihilated P d)
  have hh : (n : ℤ) ≤ 2 * (Nat.card (ResidueImage P d) : ℤ) := by
    have heq : (q : ℤ) * (addOrderOf g : ℤ) = (Nat.card (ResidueImage P d) : ℤ) := by
      exact_mod_cast hcard
    simp only [Finset.card_univ, Fintype.card_fin] at hbound
    nlinarith only [hbound, heq]
  exact_mod_cast hh

end
end ActualLargeClassBound
