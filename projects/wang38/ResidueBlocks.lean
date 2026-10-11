import MathlibBridge
import VectorFrequency
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity

open scoped BigOperators
namespace Wang38

def SameAbs {R : Type*} [Neg R] (x y : R) : Prop := x = y ∨ x = -y

 theorem sameAbs_refl {R : Type*} [Neg R] (x : R) : SameAbs x x := Or.inl rfl

 theorem sameAbs_symm {R : Type*} [AddGroup R] {x y : R} (h : SameAbs x y) : SameAbs y x := by
  rcases h with h | h
  · exact Or.inl h.symm
  · exact Or.inr (by rw [h]; simp)

 theorem sameAbs_trans {R : Type*} [AddGroup R] {x y z : R}
    (h : SameAbs x y) (k : SameAbs y z) : SameAbs x z := by
  rcases h with h | h <;> rcases k with k | k
  · exact Or.inl (h.trans k)
  · exact Or.inr (h.trans k)
  · exact Or.inr (by rw [h, k])
  · exact Or.inl (by rw [h, k]; simp)

 theorem sameAbs_mul_cancel {R : Type*} [Ring R] [NoZeroDivisors R]
    {c x y : R} (hc : c ≠ 0) (h : SameAbs (c*x) (c*y)) : SameAbs x y := by
  rcases h with h | h
  · exact Or.inl (mul_left_cancel₀ hc h)
  · exact Or.inr (mul_left_cancel₀ hc (by simpa using h))

 theorem sameAbs_sign_mul {R : Type*} [Ring R] (ε : Int) (hε : ε = 1 ∨ ε = -1) (x : R) :
    SameAbs ((ε : R)*x) x := by
  rcases hε with h | h
  · rw [h]; left; simp
  · rw [h]; right; simp

 theorem sameAbs_cast_of_natAbs_eq {p : Nat} (x y : Int) (h : x.natAbs = y.natAbs) :
    SameAbs (x : ZMod p) (y : ZMod p) := by
  rcases Int.natAbs_eq_natAbs_iff.mp h with h | h
  · exact Or.inl (congrArg (fun z : Int => (z : ZMod p)) h)
  · right
    simpa using congrArg (fun z : Int => (z : ZMod p)) h

noncomputable def absResidueBlock {p n : Nat} (v : IVector n) (i : Fin n) : Finset (Fin n) :=
by
  classical
  exact Finset.univ.filter (fun j => SameAbs (v j : ZMod p) (v i : ZMod p))

 theorem mem_absResidueBlock {p n : Nat} (v : IVector n) (i j : Fin n) :
    j ∈ absResidueBlock (p := p) v i ↔ SameAbs (v j : ZMod p) (v i : ZMod p) := by
  classical
  simp [absResidueBlock]

 theorem self_mem_absResidueBlock {p n : Nat} (v : IVector n) (i : Fin n) :
    i ∈ absResidueBlock (p := p) v i :=
  (mem_absResidueBlock v i i).mpr (sameAbs_refl _)

 theorem exists_maximal_absResidueBlock {p n : Nat} (hp : OddPrime p)
    (v : IVector n) (hn : p < n) :
    ∃ i : Fin n, 2 ≤ (absResidueBlock (p := p) v i).card ∧
      ∀ j, (absResidueBlock (p := p) v j).card ≤ (absResidueBlock (p := p) v i).card := by
  classical
  let : Fact (Nat.Prime p) := ⟨oddPrime_isPrime hp⟩
  have hcard : Fintype.card (ZMod p) < Fintype.card (Fin n) := by simpa using hn
  rcases Fintype.exists_ne_map_eq_of_card_lt (fun i : Fin n => (v i : ZMod p)) hcard with
    ⟨i, j, hij, heq⟩
  have hpair : ({i,j} : Finset (Fin n)) ⊆ absResidueBlock (p := p) v i := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with h | h
    · subst k; exact self_mem_absResidueBlock v i
    · subst k; exact (mem_absResidueBlock v i j).mpr (Or.inl heq.symm)
  have hi2 : 2 ≤ (absResidueBlock (p := p) v i).card := by
    simpa [Finset.card_pair hij] using Finset.card_le_card hpair
  rcases Finset.exists_max_image (Finset.univ : Finset (Fin n))
    (fun k => (absResidueBlock (p := p) v k).card) ⟨i, Finset.mem_univ i⟩ with ⟨k, _, hk⟩
  exact ⟨k, hi2.trans (hk i (Finset.mem_univ i)), fun j => hk j (Finset.mem_univ j)⟩

/-- Each actual magnitude class injects into one absolute residue block. -/
theorem magnitudeCount_le_maximal_block {p n : Nat} (hp : OddPrime p)
    (u v : IVector n) (c : ZMod p) (hc : c ≠ 0) (i : Fin n)
    (hmax : ∀ j, (absResidueBlock (p := p) v j).card ≤ (absResidueBlock (p := p) v i).card)
    (hres : ∀ j, SameAbs (u j : ZMod p) (c*(v j : ZMod p))) (t : Nat) :
    magnitudeCount u t ≤ (absResidueBlock (p := p) v i).card := by
  classical
  let : Fact (Nat.Prime p) := ⟨oddPrime_isPrime hp⟩
  let S := Finset.univ.filter (fun j => (u j).natAbs = t)
  by_cases hs : S.Nonempty
  · rcases hs with ⟨j, hj⟩
    have hsub : S ⊆ absResidueBlock (p := p) v j := by
      intro k hk
      have hm : (u k).natAbs = (u j).natAbs := by
        exact (Finset.mem_filter.mp hk).2.trans (Finset.mem_filter.mp hj).2.symm
      have habs := sameAbs_cast_of_natAbs_eq (p := p) (u k) (u j) hm
      have hscaled := sameAbs_trans (sameAbs_symm (hres k)) (sameAbs_trans habs (hres j))
      exact (mem_absResidueBlock v j k).mpr (sameAbs_mul_cancel hc hscaled)
    exact (Finset.card_le_card hsub).trans (hmax j)
  · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    change S.card ≤ _
    rw [he]
    exact Nat.zero_le _

/-- Orient the signs so the selected absolute-residue block has one residue. -/
noncomputable def orientSign {p n : Nat} (v : IVector n) (i j : Fin n) : Int :=
  if (v j : ZMod p) = (v i : ZMod p) then 1 else -1

 theorem orientSign_cases {p n : Nat} (v : IVector n) (i j : Fin n) :
    orientSign (p := p) v i j = 1 ∨ orientSign (p := p) v i j = -1 := by
  classical
  unfold orientSign
  split <;> simp_all

 theorem orientSign_square {p n : Nat} (v : IVector n) (i j : Fin n) :
    orientSign (p := p) v i j * orientSign (p := p) v i j = 1 := by
  rcases orientSign_cases (p := p) v i j with h | h <;> rw [h] <;> decide

 theorem orientSign_on_block {p n : Nat} (v : IVector n) (i j : Fin n)
    (hj : j ∈ absResidueBlock (p := p) v i) :
    (orientSign (p := p) v i j : ZMod p)*(v j : ZMod p) = (v i : ZMod p) := by
  classical
  have habs := (mem_absResidueBlock v i j).mp hj
  unfold orientSign
  split
  · rename_i h; simp [h]
  · rename_i h
    have he := habs.resolve_left h
    rw [he]
    simp

#print axioms exists_maximal_absResidueBlock
#print axioms magnitudeCount_le_maximal_block
#print axioms orientSign_on_block

end Wang38
