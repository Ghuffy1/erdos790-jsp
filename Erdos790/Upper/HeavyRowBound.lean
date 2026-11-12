import Erdos790.Upper.HeavyClusterBound
import Erdos790.Upper.ExteriorProfiles

/-!
# Counting every exterior profile in one row of a heavy cluster
-/

namespace Erdos790.Upper.AuxiliaryParameters

theorem heavy_cluster_row_bound {d K start constant step : ℕ} {C B : Finset ℕ}
    (E : Finset (ℕ × ℤ × (Fin d → Fin 2)))
    (hd : 48 ≤ d) (hK : 0 < K) (hshort : 12 * clusterWidth d ≤ d)
    (hmargin : 32 * (tentAmplification d * timeCount d + 1) * timeCount d ≤ radixBase d)
    (hC : ∀ u ∈ C, baseRange d ≤ u ∧ u < 2 * baseRange d)
    (hcover : SumCover C K (sumThreshold d)) (hB : RepeatedSumFree (arityLimit d) B)
    (hstart : start ∈ heavyClusterStarts d K C B)
    (hlevels : ∀ p ∈ E,
      p.1 ∈ levelCluster (heavyLevels (levelCount d) K C B) (clusterWidth d) start)
    (hcoordinates : ∀ p ∈ E, 0 ≤ p.2.1 ∧ p.2.1 < timeCount d)
    (hselected : ∀ p ∈ E,
      2 ^ p.1 * nativeTentValue (tentAmplification d) (2 ^ (6 * d)) constant
        (factorialModulus d) step p.2.1.toNat p.2.2 ∈ B) :
    let positions := assignedPositions d (6 * d) start
      ((heavyClusterStarts d K C B).filter (fun i => i < start))
    (E.card : ℝ) ≤ (2 : ℝ) ^ (3 * d) * clusterSequence 1200 positions.card := by
  classical
  let positions := assignedPositions d (6 * d) start
    ((heavyClusterStarts d K C B).filter (fun i => i < start))
  have hprofiles : ∀ profile : (↥(positionsᶜ : Finset (Fin d))) → Fin 2,
      ((profileOccurrences E positions profile).card : ℝ) ≤
        (2 : ℝ) ^ positions.card * clusterSequence 1200 positions.card * timeCount d := by
    intro profile
    let F := profileOccurrences E positions profile
    have hFE : F ⊆ E := profileOccurrences_subset E positions profile
    exact heavy_cluster_fixed_profile_bound F (fillExterior positions profile)
      hd hK hshort hmargin hC hcover hB hstart
      (fun p hp => hlevels p (hFE hp))
      (fun p hp => hcoordinates p (hFE hp))
      (profileOccurrences_fixed positions profile)
      (fun p hp => hselected p (hFE hp))
  have hbound := profileOccurrences_card_bound E positions
    ((2 : ℝ) ^ positions.card * clusterSequence 1200 positions.card * timeCount d) hprofiles
  have hcard : positions.card ≤ d := by simpa using Finset.card_le_univ positions
  have hpower : (2 : ℝ) ^ (d - positions.card) * (2 : ℝ) ^ positions.card = (2 : ℝ) ^ d := by
    rw [← pow_add, Nat.sub_add_cancel hcard]
  calc
    (E.card : ℝ) ≤ (2 : ℝ) ^ (d - positions.card) *
        ((2 : ℝ) ^ positions.card * clusterSequence 1200 positions.card * timeCount d) := hbound
    _ = ((2 : ℝ) ^ (d - positions.card) * (2 : ℝ) ^ positions.card) *
        clusterSequence 1200 positions.card * timeCount d := by ring
    _ = (2 : ℝ) ^ d * clusterSequence 1200 positions.card * timeCount d := by rw [hpower]
    _ = clusterSequence 1200 positions.card * ((2 : ℝ) ^ d * (2 : ℝ) ^ (2 * d)) := by
      simp only [timeCount, Nat.cast_pow, Nat.cast_ofNat]
      ring
    _ = clusterSequence 1200 positions.card * (2 : ℝ) ^ (3 * d) := by
      rw [← pow_add]
      congr 2
      omega
    _ = _ := by ring

end Erdos790.Upper.AuxiliaryParameters
