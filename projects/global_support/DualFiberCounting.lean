import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Dual-fiber counting: arithmetic and finite-set core only

The inputs here are explicit integer bounds and finite sets. No rational
orthogonal matrix, coincidence lattice, finite dual group, or sign class is
postulated or formalized by these declarations. In particular, the low-row
capacity remains a hypothesis until proved from an actual domain model.
-/

namespace DualFiberCounting
open scoped BigOperators

/-- Cancellation-free polynomial identity for the selected-column energy. -/
theorem outside_energy_identity (K h a : ℤ) :
    h^2 - ((K-1)*a^2 + (a-h)^2) = 2*h*a-K*a^2 := by ring

/-- The purely numerical closure. Positivity and every counting premise are
explicit. No structural matrix fact is hidden in the types. -/
theorem partition_numeric_bound (K h q a m high low energy : ℤ)
    (_hK : 0 < K) (_hh : 0 < h) (hq : 0 < q) (ha : 0 < a)
    (hcap : K*a ≤ 2*h)
    (henergy : energy = 2*h*a-K*a^2)
    (hhigh : high*a^2 ≤ energy)
    (hlow : low ≤ K*(q*a-1))
    (hpartition : m ≤ K+high+low) : m ≤ 2*h*q := by
  have ha0 : 0 ≤ a := le_of_lt ha
  have hasq : 0 < a^2 := sq_pos_of_pos ha
  have hqa : 0 ≤ q*a-1 := by
    have hqa' : 1 ≤ q*a := by
      calc
        1 = 1*1 := by ring
        _ ≤ q*a := mul_le_mul (by omega) (by omega) (by omega) (by omega)
    omega
  have hlow' := mul_le_mul_of_nonneg_right hlow (le_of_lt hasq)
  have hpartition' := mul_le_mul_of_nonneg_right hpartition (le_of_lt hasq)
  have hcap' := mul_le_mul_of_nonneg_right hcap (mul_nonneg ha0 hqa)
  have hfinal : m*a^2 ≤ (2*h*q)*a^2 := by
    calc
      m*a^2 ≤ (K+high+low)*a^2 := hpartition'
      _ ≤ 2*h*a+K*(q*a-1)*a^2 := by nlinarith only [henergy, hhigh, hlow']
      _ ≤ 2*h*a+2*h*(a*(q*a-1)) := by nlinarith only [hcap']
      _ = (2*h*q)*a^2 := by ring
  exact (mul_le_mul_iff_left₀ hasq).mp hfinal

/-- A finite collection of entries whose squares exceed a threshold has
cardinality times that threshold at most its squared energy. -/
theorem high_rows_energy {ι : Type*} (H : Finset ι) (w : ι → ℤ) (a : ℤ)
    (hH : ∀ i ∈ H, a^2 ≤ (w i)^2) :
    (H.card : ℤ)*a^2 ≤ ∑ i ∈ H, (w i)^2 := by
  have h := Finset.sum_le_sum hH
  simpa only [Finset.sum_const, nsmul_eq_mul] using h

/-- The high-row energy bound remains valid inside a larger set because all
remaining squared entries are nonnegative. -/
theorem high_rows_energy_of_subset {ι : Type*} (H S : Finset ι)
    (w : ι → ℤ) (a : ℤ) (hHS : H ⊆ S)
    (hH : ∀ i ∈ H, a^2 ≤ (w i)^2) :
    (H.card : ℤ)*a^2 ≤ ∑ i ∈ S, (w i)^2 := by
  exact (high_rows_energy H w a hH).trans
    (Finset.sum_le_sum_of_subset_of_nonneg hHS (fun i _ _ => sq_nonneg (w i)))

/-- Actual finite-bin counting with a distinguished zero bin. Every nonzero
bin has capacity K*q and the zero bin has capacity K*(q-1). These capacities
are hypotheses, not asserted consequences of a dual group. -/
theorem low_fiber_capacity {ι β : Type*} [Fintype β] [DecidableEq β]
    (L : Finset ι) (f : ι → β) (zeroBin : β) (K q : ℤ)
    (hzero : ((L.filter (fun i => f i = zeroBin)).card : ℤ) ≤ K*(q-1))
    (hother : ∀ b, b ≠ zeroBin →
      ((L.filter (fun i => f i = b)).card : ℤ) ≤ K*q) :
    (L.card : ℤ) ≤ K*(q*(Fintype.card β : ℤ)-1) := by
  have hcardNat : L.card = ∑ b, (L.filter (fun i => f i = b)).card :=
    Finset.card_eq_sum_card_fiberwise (by intro i hi; simp)
  have hcard : (L.card : ℤ) = ∑ b, ((L.filter (fun i => f i = b)).card : ℤ) := by
    exact_mod_cast hcardNat
  have hpoint : ∀ b, ((L.filter (fun i => f i = b)).card : ℤ)
      ≤ K*q - (if b = zeroBin then K else 0) := by
    intro b
    by_cases hb : b = zeroBin
    · subst b
      simp only [ite_true]
      nlinarith only [hzero]
    · simp only [ite_eq_right hb, sub_zero]
      exact hother b hb
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun b _ => hpoint b)
  rw [← hcard] at hs
  simp [Finset.sum_sub_distrib] at hs
  nlinarith only [hs]

/-- Finite-row version with an actual threshold partition. The low-row
capacity and selected-column energy identity are explicit domain inputs.
The high-row energy estimate and the partition cardinality are proved here. -/
theorem finite_partition_bound {ι : Type*} [DecidableEq ι]
    (S I : Finset ι) (w : ι → ℤ) (h q a : ℤ)
    (hIS : I ⊆ S) (hIpos : 0 < I.card)
    (hh : 0 < h) (hq : 0 < q) (ha : 0 < a)
    (hcap : (I.card : ℤ)*a ≤ 2*h)
    (henergy : (∑ i ∈ S \ I, (w i)^2) = 2*h*a-(I.card : ℤ)*a^2)
    (hlow : (((S \ I).filter (fun i => ¬ a^2 ≤ (w i)^2)).card : ℤ)
      ≤ (I.card : ℤ)*(q*a-1)) :
    (S.card : ℤ) ≤ 2*h*q := by
  let H := (S \ I).filter (fun i => a^2 ≤ (w i)^2)
  let L := (S \ I).filter (fun i => ¬ a^2 ≤ (w i)^2)
  have hHS : H ⊆ S \ I := Finset.filter_subset _ _
  have hH : ∀ i ∈ H, a^2 ≤ (w i)^2 := by
    intro i hi
    exact (Finset.mem_filter.mp hi).2
  have hhigh := high_rows_energy_of_subset H (S \ I) w a hHS hH
  have hsplit : H.card+L.card = (S \ I).card :=
    Finset.card_filter_add_card_filter_not _
  have htotal := Finset.card_sdiff_add_card_eq_card hIS
  have hpartition : (S.card : ℤ) ≤ (I.card : ℤ)+(H.card : ℤ)+(L.card : ℤ) := by
    have hn : S.card = I.card+H.card+L.card := by omega
    exact_mod_cast (le_of_eq hn)
  exact partition_numeric_bound I.card h q a S.card H.card L.card _
    (by exact_mod_cast hIpos) hh hq ha hcap henergy hhigh hlow hpartition

/-- A combined finite theorem requiring only per-bin low-row capacities.
The map to bins, their number, and their capacities are supplied explicitly;
this file does not claim that matrix characters provide those inputs. -/
theorem finite_partition_from_bins {ι β : Type*}
    [DecidableEq ι] [Fintype β] [DecidableEq β]
    (S I : Finset ι) (w : ι → ℤ) (h q a : ℤ)
    (bin : ι → β) (zeroBin : β) (hbins : (Fintype.card β : ℤ) = a)
    (hIS : I ⊆ S) (hIpos : 0 < I.card)
    (hh : 0 < h) (hq : 0 < q) (ha : 0 < a)
    (hcap : (I.card : ℤ)*a ≤ 2*h)
    (henergy : (∑ i ∈ S \ I, (w i)^2) = 2*h*a-(I.card : ℤ)*a^2)
    (hzero : ((((S \ I).filter (fun i => ¬ a^2 ≤ (w i)^2)).filter
      (fun i => bin i = zeroBin)).card : ℤ) ≤ (I.card : ℤ)*(q-1))
    (hother : ∀ b, b ≠ zeroBin →
      ((((S \ I).filter (fun i => ¬ a^2 ≤ (w i)^2)).filter
      (fun i => bin i = b)).card : ℤ) ≤ (I.card : ℤ)*q) :
    (S.card : ℤ) ≤ 2*h*q := by
  apply finite_partition_bound S I w h q a hIS hIpos hh hq ha hcap henergy
  have hc := low_fiber_capacity ((S \ I).filter (fun i => ¬ a^2 ≤ (w i)^2))
    bin zeroBin I.card q hzero hother
  simpa only [hbins] using hc

/-- Explicit involution-orbit capacity. At a fixed label the occupancy is at
most four; at every nonfixed pair the combined occupancy is at most eight.
This does not assume that both labels in a pair are occupied. -/
theorem involution_capacity {α : Type*} [Fintype α]
    (σ : α → α) (hσ : Function.Involutive σ) (occupancy : α → ℕ)
    (hfixed : ∀ x, σ x = x → occupancy x ≤ 4)
    (hpair : ∀ x, σ x ≠ x → occupancy x+occupancy (σ x) ≤ 8) :
    (∑ x, occupancy x) ≤ 4*Fintype.card α := by
  have hpoint : ∀ x, occupancy x+occupancy (σ x) ≤ 8 := by
    intro x
    by_cases hx : σ x = x
    · have hc := hfixed x hx
      rw [hx]
      omega
    · exact hpair x hx
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun x _ => hpoint x)
  have hperm : (∑ x, occupancy (σ x)) = ∑ x, occupancy x :=
    hσ.bijective.sum_comp occupancy
  rw [Finset.sum_add_distrib, hperm] at hsum
  simp at hsum
  omega

/-- Parity-coset application of the explicit involution lemma. The label type
must have half the total size, supplied as an exact integer equation.
No assertion that a matrix induces such labels is made here. -/
theorem parity_orbit_capacity {α : Type*} [Fintype α]
    (σ : α → α) (hσ : Function.Involutive σ) (occupancy : α → ℕ)
    (Sigma : ℕ) (hhalf : 2*Fintype.card α = Sigma)
    (hfixed : ∀ x, σ x = x → occupancy x ≤ 4)
    (hpair : ∀ x, σ x ≠ x → occupancy x+occupancy (σ x) ≤ 8) :
    (∑ x, occupancy x) ≤ 2*Sigma := by
  have h := involution_capacity σ hσ occupancy hfixed hpair
  omega

end DualFiberCounting
