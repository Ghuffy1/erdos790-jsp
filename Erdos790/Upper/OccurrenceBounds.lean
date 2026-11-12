import Erdos790.Upper.OccurrenceFamilies
import Erdos790.Upper.LaterSideBound
import Erdos790.Upper.SelectionMultiplicity

/-!
# Applying the later-side estimate to actual selected occurrences
-/

namespace Erdos790.Upper

theorem later_occurrence_card_bound
    {d R stop width M : ℕ} {E later : Finset (ℕ × ℤ × (Fin d → Fin 2))}
    (free : Finset (Fin d)) (fixed : Fin d → Fin 2)
    (value : ℤ → (Fin d → Fin 2) → ℕ)
    (anchor : ℕ × ℤ × (Fin d → Fin 2)) {cut left : ℤ} {B : Finset ℕ}
    (hd : 48 ≤ d) (hfree : 6 * free.card ≤ d)
    (hwidth : 12 * width ≤ d) (hwidthPos : 0 < width) (hM : 2 ^ d ≤ M)
    (hanchor : anchor ∈ E) (hlater : later ⊆ E)
    (hfirst : ∀ p ∈ later, anchor.1 ≤ p.1) (hend : ∀ p ∈ E, p.1 < stop)
    (hshort : stop ≤ anchor.1 + width)
    (hunique : ∀ j t a b, (j, t, a) ∈ E → (j, t, b) ∈ E → a = b)
    (hfixed : ∀ p ∈ E, ∀ h, h ∉ free → p.2.2 h = fixed h)
    (hselected : ∀ p ∈ E, 2 ^ p.1 * value p.2.1 p.2.2 ∈ B)
    (hB : RepeatedSumFree R B) (hR : 2 ^ width ≤ R)
    (hinterval : ∀ p ∈ later, left ≤ p.2.1 ∧ p.2.1 < left + M)
    (hside : (anchor.2.1 < cut ∧ ∀ p ∈ later, cut ≤ p.2.1) ∨
      (cut ≤ anchor.2.1 ∧ ∀ p ∈ later, p.2.1 < cut))
    (hdistance : ∀ p ∈ later, |anchor.2.1 - p.2.1| ≤ 2 * (M : ℤ))
    (hforbidden : ∀ p ∈ E,
      ¬DyadicMean (selectedCoordinates (occurrenceFamily E)) cut p.1 p.2.1) :
    (later.card : ℝ) ≤ (M : ℝ) *
      ((2 : ℝ) ^ free.card * clusterDensity free.card + 600 * (free.card + 1 : ℝ) ^ 2) := by
  classical
  let A := selectedCoordinates (occurrenceFamily E)
  let S := selectedCoordinates (occurrenceFamily later)
  have hsubset : ∀ j < stop, S j ⊆ A j := by
    intro j hj t ht
    obtain ⟨word, hword⟩ := mem_occurrenceCoordinates.mp ht
    exact mem_occurrenceCoordinates.mpr ⟨word, hlater hword⟩
  have hSinterval : ∀ j < stop, S j ⊆ Finset.Ico left (left + M) := by
    intro j hj t ht
    obtain ⟨word, hword⟩ := mem_occurrenceCoordinates.mp ht
    exact Finset.mem_Ico.mpr (hinterval (j, t, word) hword)
  have hpoint : ∀ j < stop, (S j).card ≤ M := by
    intro j hj
    calc
      (S j).card ≤ (Finset.Ico left (left + (M : ℤ))).card :=
        Finset.card_le_card (hSinterval j hj)
      _ = M := by simp
  have hnotMean : ∀ j < stop, ∀ t ∈ S j, ¬DyadicMean A cut j t := by
    intro j hj t ht
    obtain ⟨word, hword⟩ := mem_occurrenceCoordinates.mp ht
    exact hforbidden (j, t, word) (hlater hword)
  have hcount : ∀ t,
      ((selectionIncidences S anchor.1 stop).filter (fun p => p.2 = t)).card ≤ 2 ^ free.card := by
    apply selected_coordinate_incidence_bound (occurrenceFamily later) free fixed value hB hR hshort
    · intro j hjStart hjStop t word hword h hh
      exact hfixed (j, t, word) (hlater (mem_occurrenceFamily.mp hword)) h hh
    · intro j hjStart hjStop t word hword
      exact hselected (j, t, word) (hlater (mem_occurrenceFamily.mp hword))
  have hanchorCoordinate : anchor.2.1 ∈ A anchor.1 :=
    mem_occurrenceCoordinates.mpr ⟨anchor.2.2, hanchor⟩
  have hSside : (anchor.2.1 < cut ∧
        ∀ j, anchor.1 ≤ j → j < stop → ∀ t ∈ S j, cut ≤ t) ∨
      (cut ≤ anchor.2.1 ∧
        ∀ j, anchor.1 ≤ j → j < stop → ∀ t ∈ S j, t < cut) := by
    rcases hside with ⟨hcut, hselectedSide⟩ | ⟨hcut, hselectedSide⟩
    · refine Or.inl ⟨hcut, ?_⟩
      intro j hjStart hjStop t ht
      obtain ⟨word, hword⟩ := mem_occurrenceCoordinates.mp ht
      exact hselectedSide (j, t, word) hword
    · refine Or.inr ⟨hcut, ?_⟩
      intro j hjStart hjStop t ht
      obtain ⟨word, hword⟩ := mem_occurrenceCoordinates.mp ht
      exact hselectedSide (j, t, word) hword
  have hSdistance : ∀ j, anchor.1 ≤ j → j < stop → ∀ t ∈ S j,
      |anchor.2.1 - t| ≤ 2 * (M : ℤ) := by
    intro j hjStart hjStop t ht
    obtain ⟨word, hword⟩ := mem_occurrenceCoordinates.mp ht
    exact hdistance (j, t, word) hword
  have hbound := later_side_mass_bound hd hfree hwidth hwidthPos hM
    (hend anchor hanchor).le (by omega) hpoint hsubset hSinterval hnotMean hcount
    (le_refl anchor.1) hanchorCoordinate hSside hSdistance
  have hcard := occurrence_mass_eq later
    (fun p hp => ⟨hfirst p hp, hend p (hlater hp)⟩)
    (fun j t a b ha hb => hunique j t a b (hlater ha) (hlater hb))
  simpa only [S, ← hcard] using hbound

end Erdos790.Upper
