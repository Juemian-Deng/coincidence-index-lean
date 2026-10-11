import MatrixClassAdapters

namespace MaximumClass
open ActualFiberBounds ResidueParityBridge
variable {n : ℕ} (P : Matrix (Fin n) (Fin n) ℤ) (d : ℕ)

/-- Failing the small-class branch produces a genuine largest occupied class.
The witness is an actual column, not an unoccupied ambient residue. -/
theorem exists_large_maximum
    (hnot : ¬ ∀ j, (signClass (columnLabel P d) j).card ≤ 8) :
    ∃ j, 9 ≤ (signClass (columnLabel P d) j).card ∧
      ∀ k, (signClass (columnLabel P d) k).card ≤ (signClass (columnLabel P d) j).card := by
  classical
  obtain ⟨j, hj⟩ := not_forall.mp hnot
  obtain ⟨k, _, hk⟩ := Finset.exists_max_image Finset.univ
    (fun i => (signClass (columnLabel P d) i).card) ⟨j, Finset.mem_univ j⟩
  refine ⟨k, ?_, fun i => hk i (Finset.mem_univ i)⟩
  have h := hk j (Finset.mem_univ j)
  omega

/-- Every column belongs to its own actual class. -/
theorem mem_own_class (j : Fin n) : j ∈ signClass (columnLabel P d) j := by
  classical
  simp [signClass]

end MaximumClass
