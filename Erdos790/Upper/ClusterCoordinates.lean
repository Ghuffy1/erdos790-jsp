import Erdos790.Upper.AssignedProfiles
import Erdos790.Upper.SelectedCoordinates
import Erdos790.Upper.CoordinateMultiplicity

/-!
# Coordinate counts in the actual heavy clusters
-/

namespace Erdos790.Upper.AuxiliaryParameters

theorem heavy_cluster_coordinates_card {d K start j amplification constant step : ℕ}
    {C B : Finset ℕ} (family : ℕ → Finset (ℤ × (Fin d → Fin 2))) (fixed : Fin d → Fin 2)
    (hd : 0 < d) (hK : 0 < K) (hshort : 12 * clusterWidth d ≤ d)
    (hC : ∀ u ∈ C, baseRange d ≤ u ∧ u < 2 * baseRange d)
    (hcover : SumCover C K (sumThreshold d)) (hB : RepeatedSumFree (arityLimit d) B)
    (hstart : start ∈ heavyClusterStarts d K C B)
    (hj : j ∈ levelCluster (heavyLevels (levelCount d) K C B) (clusterWidth d) start)
    (hfixed : ∀ t word, (t, word) ∈ family j → ∀ h,
      h ∉ assignedPositions d (6 * d) start
        ((heavyClusterStarts d K C B).filter (fun i => i < start)) → word h = fixed h)
    (hselected : ∀ t word, (t, word) ∈ family j →
      2 ^ j * nativeTentValue amplification (2 ^ (6 * d)) constant
        (factorialModulus d) step t.toNat word ∈ B) :
    (selectedCoordinates family j).card = (family j).card := by
  classical
  apply selectedCoordinates_card
  intro t a b ha hb
  let words : Finset (Fin d → Fin 2) := {a, b}
  have hmem : ∀ word ∈ words, (t, word) ∈ family j := by
    intro word hword
    rcases Finset.mem_insert.mp hword with rfl | hword
    · exact ha
    · exact (Finset.mem_singleton.mp hword) ▸ hb
  have hcard := heavy_cluster_selected_profiles fixed words hd hK hshort hC hcover hB
    hstart hj (fun word hw h hh => hfixed t word (hmem word hw) h hh)
    (fun word hw => hselected t word (hmem word hw))
  exact Finset.card_le_one.mp hcard a (by simp [words]) b (by simp [words])

theorem heavy_cluster_coordinate_occurrences_card_le {d K start : ℕ} {C B : Finset ℕ}
    (occurrences : Finset (ℕ × ℤ × (Fin d → Fin 2)))
    (coordinates : Finset ℤ) (free : Finset (Fin d)) (fixed : Fin d → Fin 2)
    (value : ℤ → (Fin d → Fin 2) → ℕ)
    (hK : 0 < K) (hshort : 12 * clusterWidth d ≤ d)
    (hC : ∀ u ∈ C, baseRange d ≤ u ∧ u < 2 * baseRange d)
    (hcover : SumCover C K (sumThreshold d)) (hB : RepeatedSumFree (arityLimit d) B)
    (hstart : start ∈ heavyClusterStarts d K C B)
    (hlevels : ∀ p ∈ occurrences,
      p.1 ∈ levelCluster (heavyLevels (levelCount d) K C B) (clusterWidth d) start)
    (hcoordinates : ∀ p ∈ occurrences, p.2.1 ∈ coordinates)
    (hfixed : ∀ p ∈ occurrences, ∀ h, h ∉ free → p.2.2 h = fixed h)
    (hselected : ∀ p ∈ occurrences, 2 ^ p.1 * value p.2.1 p.2.2 ∈ B) :
    occurrences.card ≤ 2 ^ free.card * coordinates.card := by
  apply coordinate_occurrences_card_le (start := start) (delay := clusterWidth d)
    occurrences coordinates free fixed value hB
  · unfold arityLimit
    exact Nat.pow_le_pow_right (by decide) (by omega)
  · intro p hp
    exact cluster_member_bounds (clusterWidth_pos d) (by omega)
      (heavyLevels_gapFree hK hC hcover hB) hstart (hlevels p hp)
  · exact hcoordinates
  · exact hfixed
  · exact hselected

end Erdos790.Upper.AuxiliaryParameters
