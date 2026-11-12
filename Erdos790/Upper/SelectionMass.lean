import Erdos790.Upper.DyadicMeans
import Mathlib.Data.Finset.Max
import Mathlib.Order.Interval.Finset.Nat

/-!
# Counts on a finite interval of levels
-/

namespace Erdos790.Upper

def selectionMass (S : ℕ → Finset ℤ) (start stop : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (stop - start), (S (start + i)).card

theorem selectionMass_le {S : ℕ → Finset ℤ} {start stop M : ℕ}
    (hpoint : ∀ j < stop, (S j).card ≤ M) :
    selectionMass S start stop ≤ (stop - start) * M := by
  unfold selectionMass
  calc
    _ ≤ ∑ _i ∈ Finset.range (stop - start), M := by
      apply Finset.sum_le_sum
      intro i hi
      apply hpoint
      have := Finset.mem_range.mp hi
      omega
    _ = _ := by simp

theorem selectionMass_split (S : ℕ → Finset ℤ) {start middle stop : ℕ}
    (hleft : start ≤ middle) (hright : middle ≤ stop) :
    selectionMass S start stop = selectionMass S start middle + selectionMass S middle stop := by
  have hlength : stop - start = (middle - start) + (stop - middle) := by omega
  unfold selectionMass
  rw [hlength, Finset.sum_range_add]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  congr 2
  omega

theorem first_bad_level {start stop : ℕ} (bad : ℕ → Prop)
    (hexists : ∃ j, start ≤ j ∧ j < stop ∧ bad j) :
    ∃ j, start ≤ j ∧ j < stop ∧ bad j ∧ ∀ i, start ≤ i → i < j → ¬bad i := by
  classical
  let candidates := (Finset.Ico start stop).filter bad
  have hne : candidates.Nonempty := by
    obtain ⟨j, hstart, hstop, hbad⟩ := hexists
    exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hstart, hstop⟩, hbad⟩⟩
  let j := candidates.min' hne
  have hj := Finset.mem_filter.mp (Finset.min'_mem candidates hne)
  obtain ⟨hstart, hstop⟩ := Finset.mem_Ico.mp hj.1
  refine ⟨j, hstart, hstop, hj.2, ?_⟩
  intro i hsi hij hbad
  have hi : i ∈ candidates :=
    Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hsi, by omega⟩, hbad⟩
  have hmin : j ≤ i := Finset.min'_le candidates i hi
  omega

end Erdos790.Upper
