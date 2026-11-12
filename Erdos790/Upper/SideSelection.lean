import Erdos790.Upper.DensityOnset

/-!
# Choosing the first selected point of a cell
-/

namespace Erdos790.Upper

theorem first_selected_occurrence {d : ℕ}
    (occurrences : Finset (ℕ × ℤ × (Fin d → Fin 2))) (hne : occurrences.Nonempty) :
    ∃ p ∈ occurrences, ∀ q ∈ occurrences, p.1 ≤ q.1 := by
  classical
  let levels := occurrences.image Prod.fst
  have hlevels : levels.Nonempty := hne.image Prod.fst
  let first := levels.min' hlevels
  obtain ⟨p, hp, hfirst⟩ := Finset.mem_image.mp (Finset.min'_mem levels hlevels)
  refine ⟨p, hp, ?_⟩
  intro q hq
  rw [hfirst]
  exact Finset.min'_le levels q.1 (Finset.mem_image.mpr ⟨q, hq, rfl⟩)

theorem first_level_le_dense_onset {d a : ℕ}
    {all later : Finset (ℕ × ℤ × (Fin d → Fin 2))} {first : ℕ × ℤ × (Fin d → Fin 2)}
    (hlater : later ⊆ all) (hfirst : ∀ q ∈ all, first.1 ≤ q.1)
    (hne : (cumulativeCoordinates later a).Nonempty) : first.1 ≤ a := by
  obtain ⟨t, ht⟩ := hne
  obtain ⟨q, hq, _⟩ := Finset.mem_image.mp ht
  obtain ⟨hq, hqa⟩ := Finset.mem_filter.mp hq
  exact (hfirst q (hlater hq)).trans hqa

end Erdos790.Upper
