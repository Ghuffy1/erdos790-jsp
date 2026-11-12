import Erdos790.Upper.RecursiveExclusion
import Erdos790.Upper.SideSelection
import Erdos790.Upper.ClusterBudget

/-!
# Combining the two recursive children with the later half of one cell
-/

namespace Erdos790.Upper

theorem cell_mass_bound {d s R start width size : ℕ} {left : ℤ}
    (E : Finset (ℕ × ℤ × (Fin d → Fin 2)))
    (free : Finset (Fin d)) (fixed : Fin d → Fin 2)
    (value : ℤ → (Fin d → Fin 2) → ℕ) (H : Fin d) {B : Finset ℕ}
    (hd : 48 ≤ d) (hcard : free.card = s + 1) (hfree : 6 * free.card ≤ d)
    (hwidth : 12 * width ≤ d) (hwidthPos : 0 < width) (hsize : 2 ^ d ≤ size)
    (hB : RepeatedSumFree R B) (hR : 2 ^ width ≤ R)
    (hframe : ∀ p ∈ E, left ≤ p.2.1 ∧ p.2.1 < left + 2 * (size : ℤ))
    (hlevels : ∀ p ∈ E, start ≤ p.1 ∧ p.1 < start + width)
    (hunique : ∀ j t a b, (j, t, a) ∈ E → (j, t, b) ∈ E → a = b)
    (hfixed : ∀ p ∈ E, ∀ h, h ∉ free → p.2.2 h = fixed h)
    (hselected : ∀ p ∈ E, 2 ^ p.1 * value p.2.1 p.2.2 ∈ B)
    (hforbidden : ∀ p ∈ E,
      ¬DyadicMean (selectedCoordinates (occurrenceFamily E)) (left + size) p.1 p.2.1)
    (hchildren : ∀ right : Bool, ∀ bit : Fin 2,
      ((bitOccurrences (halfOccurrences E (left + size) right) H bit).card : ℝ) ≤
        (2 : ℝ) ^ s * clusterSequence 1200 s * size) :
    (E.card : ℝ) ≤ (2 : ℝ) ^ (s + 1) * clusterSequence 1200 (s + 1) * (2 * (size : ℝ)) := by
  classical
  by_cases hnonempty : E.Nonempty
  · obtain ⟨anchor, hanchor, hfirst⟩ := first_selected_occurrence E hnonempty
    let right := decide (left + (size : ℤ) ≤ anchor.2.1)
    let earlier := halfOccurrences E (left + size) right
    let later := halfOccurrences E (left + size) (!right)
    have hearlier : earlier ⊆ E := halfOccurrences_subset E _ right
    have hlater : later ⊆ E := halfOccurrences_subset E _ (!right)
    have hanchorHalf : anchor ∈ earlier := anchor_mem_half hanchor _
    have hside : (anchor.2.1 < left + size ∧ ∀ p ∈ later, left + size ≤ p.2.1) ∨
        (left + size ≤ anchor.2.1 ∧ ∀ p ∈ later, p.2.1 < left + size) := by
      by_cases ha : anchor.2.1 < left + size
      · refine Or.inl ⟨ha, ?_⟩
        intro p hp
        rcases opposite_half_relation hanchorHalf hp with h | h
        · exact h.2
        · omega
      · refine Or.inr ⟨le_of_not_gt ha, ?_⟩
        intro p hp
        rcases opposite_half_relation hanchorHalf hp with h | h
        · omega
        · exact h.2
    have hlaterBound := later_occurrence_card_bound free fixed value anchor hd hfree
      hwidth hwidthPos hsize hanchor hlater
      (fun p hp => hfirst p (hlater hp)) (fun p hp => (hlevels p hp).2)
      (by have := (hlevels anchor hanchor).1; omega)
      hunique hfixed hselected hB hR (halfOccurrences_interval hframe (!right)) hside
      (fun p hp => cell_coordinate_distance hframe hanchor (hlater hp)) hforbidden
    rw [hcard] at hlaterBound
    push_cast at hlaterBound
    have hearlierEq : (earlier.card : ℝ) =
        ((bitOccurrences earlier H 0).card : ℝ) + (bitOccurrences earlier H 1).card := by
      exact_mod_cast bitOccurrences_card_split earlier H
    have hzero := hchildren right 0
    have hone := hchildren right 1
    have hearlierBound : (earlier.card : ℝ) ≤
        (2 : ℝ) ^ s * clusterSequence 1200 s * (2 * (size : ℝ)) := by
      change ((bitOccurrences earlier H 0).card : ℝ) ≤ _ at hzero
      change ((bitOccurrences earlier H 1).card : ℝ) ≤ _ at hone
      nlinarith
    have hlaterScaled : (later.card : ℝ) ≤
        ((2 : ℝ) ^ (s + 1) * clusterDensity (s + 1) + 600 * (s + 2 : ℝ) ^ 2) *
          ((2 * (size : ℝ)) / 2) := by
      nlinarith
    have hbound := cluster_budget_step_scaled (s := s) (by positivity)
      hearlierBound hlaterScaled
    have htotal : (E.card : ℝ) = (earlier.card : ℝ) + (later.card : ℝ) := by
      exact_mod_cast halfOccurrences_card_split E (left + size) right
    rwa [← htotal] at hbound
  · have heq : E = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnonempty
    have hnonneg := clusterSequence_nonneg (by norm_num : (0 : ℝ) ≤ 1200) (s + 1)
    simp only [heq, Finset.card_empty, Nat.cast_zero]
    positivity

end Erdos790.Upper
