import Erdos790.Upper.OccurrenceBounds
import Erdos790.Upper.CellGrid
import Erdos790.Upper.CoordinateMultiplicity

/-!
# Restriction and the zero-free-bit case of the cell recursion
-/

namespace Erdos790.Upper

theorem DyadicMean.mono_family {A B : ℕ → Finset ℤ} {cut t : ℤ} {j : ℕ}
    (h : DyadicMean A cut j t) (hAB : ∀ k, A k ⊆ B k) : DyadicMean B cut j t := by
  obtain ⟨L, hL, hweight, hmoment, hleft, hright⟩ := h
  refine ⟨L, ?_, hweight, hmoment, hleft, hright⟩
  intro p hp
  exact ⟨(hL p hp).1, hAB p.1 (hL p hp).2⟩

theorem occurrence_coordinates_mono {d : ℕ} {E F : Finset (ℕ × ℤ × (Fin d → Fin 2))}
    (hEF : E ⊆ F) (j : ℕ) :
    selectedCoordinates (occurrenceFamily E) j ⊆ selectedCoordinates (occurrenceFamily F) j := by
  intro t ht
  obtain ⟨word, hword⟩ := mem_occurrenceCoordinates.mp ht
  exact mem_occurrenceCoordinates.mpr ⟨word, hEF hword⟩

theorem occurrence_forbidden_of_subset {d : ℕ}
    {E F : Finset (ℕ × ℤ × (Fin d → Fin 2))} {cut : ℤ}
    (hEF : E ⊆ F)
    (hforbidden : ∀ p ∈ F,
      ¬DyadicMean (selectedCoordinates (occurrenceFamily F)) cut p.1 p.2.1) :
    ∀ p ∈ E, ¬DyadicMean (selectedCoordinates (occurrenceFamily E)) cut p.1 p.2.1 := by
  intro p hp hmean
  exact hforbidden p (hEF hp) (hmean.mono_family (occurrence_coordinates_mono hEF))

theorem empty_profile_occurrence_bound {d start width R M : ℕ} {left : ℤ}
    {E : Finset (ℕ × ℤ × (Fin d → Fin 2))} {B : Finset ℕ}
    (fixed : Fin d → Fin 2) (value : ℤ → (Fin d → Fin 2) → ℕ)
    (hB : RepeatedSumFree R B) (hR : 2 ^ width ≤ R)
    (hlevels : ∀ p ∈ E, start ≤ p.1 ∧ p.1 < start + width)
    (hinterval : ∀ p ∈ E, left ≤ p.2.1 ∧ p.2.1 < left + M)
    (hfixed : ∀ p ∈ E, ∀ h, p.2.2 h = fixed h)
    (hselected : ∀ p ∈ E, 2 ^ p.1 * value p.2.1 p.2.2 ∈ B) :
    E.card ≤ M := by
  have hbound := coordinate_occurrences_card_le (start := start) (delay := width)
    E (Finset.Ico left (left + M)) ∅ fixed value hB hR hlevels
    (fun p hp => Finset.mem_Ico.mpr (hinterval p hp))
    (fun p hp h _ => hfixed p hp h) hselected
  simpa using hbound

end Erdos790.Upper
