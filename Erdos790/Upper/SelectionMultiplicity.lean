import Erdos790.Upper.SelectedCoordinates
import Erdos790.Upper.SelectionUnion
import Erdos790.Upper.ClusterMultiplicity

/-!
# Coordinate multiplicity for an actual selected binary-word family
-/

namespace Erdos790.Upper

theorem selected_coordinate_incidence_bound {d start stop delay R : ℕ} {B : Finset ℕ}
    (family : ℕ → Finset (ℤ × (Fin d → Fin 2)))
    (free : Finset (Fin d)) (fixed : Fin d → Fin 2)
    (value : ℤ → (Fin d → Fin 2) → ℕ)
    (hB : RepeatedSumFree R B) (hR : 2 ^ delay ≤ R) (hstop : stop ≤ start + delay)
    (hfixed : ∀ j, start ≤ j → j < stop → ∀ t word, (t, word) ∈ family j →
      ∀ h, h ∉ free → word h = fixed h)
    (hselected : ∀ j, start ≤ j → j < stop → ∀ t word, (t, word) ∈ family j →
      2 ^ j * value t word ∈ B) (t : ℤ) :
    ((selectionIncidences (selectedCoordinates family) start stop).filter
      (fun p => p.2 = t)).card ≤ 2 ^ free.card := by
  classical
  let E := (selectionIncidences (selectedCoordinates family) start stop).filter
    (fun p => p.2 = t)
  let project := fun p : ℕ × ℤ => (p.1, selectedCoordinateWord family p.1 p.2)
  let words := E.image project
  have hinj : Set.InjOn project ↑E := by
    intro a ha b hb hab
    have hlevel : a.1 = b.1 := congrArg (fun p : ℕ × (Fin d → Fin 2) => p.1) hab
    have hat := (Finset.mem_filter.mp ha).2
    have hbt := (Finset.mem_filter.mp hb).2
    exact Prod.ext hlevel (hat.trans hbt.symm)
  have hcard : words.card = E.card := Finset.card_image_of_injOn hinj
  change E.card ≤ _
  rw [← hcard]
  apply binary_occurrences_card_le words free fixed (value t) hB hR
  · intro p hp
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hp
    have ha := mem_selectionIncidences.mp (Finset.mem_filter.mp ha).1
    exact ⟨ha.1, ha.2.1.trans_le hstop⟩
  · intro p hp h hh
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hp
    have ha := mem_selectionIncidences.mp (Finset.mem_filter.mp ha).1
    exact hfixed a.1 ha.1 ha.2.1 a.2 _ (selectedCoordinateWord_mem family ha.2.2) h hh
  · intro p hp
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨ha, hat⟩ := Finset.mem_filter.mp ha
    have hmem := mem_selectionIncidences.mp ha
    have hchosen := selectedCoordinateWord_mem family hmem.2.2
    have hvalue := hselected a.1 hmem.1 hmem.2.1 a.2 _ hchosen
    simpa only [project, hat] using hvalue

end Erdos790.Upper
