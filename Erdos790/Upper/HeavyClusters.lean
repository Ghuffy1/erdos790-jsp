import Erdos790.Upper.HeavyLevels
import Erdos790.Upper.LevelClusters
import Erdos790.Upper.ClusterDigits

/-!
# Clusters and digit assignments for the actual heavy levels
-/

namespace Erdos790.Upper

def heavyLevels (L K : ℕ) (C B : Finset ℕ) : Finset ℕ :=
  (Finset.range L).filter (fun j => K ≤ (levelSlice j C B).card)

namespace AuxiliaryParameters

theorem clusterWidth_pos (d : ℕ) : 0 < clusterWidth d := by unfold clusterWidth; omega

theorem heavyLevels_gapFree {d K : ℕ} {C B : Finset ℕ} (hK : 0 < K)
    (hC : ∀ u ∈ C, baseRange d ≤ u ∧ u < 2 * baseRange d)
    (hcover : SumCover C K (sumThreshold d)) (hB : RepeatedSumFree (arityLimit d) B) :
    MediumGapFree (heavyLevels (levelCount d) K C B) (clusterWidth d) (36 * d) := by
  intro i hi j hj hij hgap
  have hheavy := (Finset.mem_filter.mp hi).2
  have hjheavy := (Finset.mem_filter.mp hj).2
  have hoccupied : (levelSlice j C B).Nonempty := Finset.card_pos.mp (lt_of_lt_of_le hK hjheavy)
  by_contra hnot
  exact occupied_level_gap_impossible hC hcover hB hheavy hoccupied hij hgap (by omega)

noncomputable def heavyClusterStarts (d K : ℕ) (C B : Finset ℕ) : Finset ℕ :=
  clusterStarts (heavyLevels (levelCount d) K C B) (clusterWidth d) (clusterWidth_pos d)

theorem heavyClusterStarts_separated {d K : ℕ} {C B : Finset ℕ} (hK : 0 < K)
    (hshort : 12 * clusterWidth d ≤ d)
    (hC : ∀ u ∈ C, baseRange d ≤ u ∧ u < 2 * baseRange d)
    (hcover : SumCover C K (sumThreshold d)) (hB : RepeatedSumFree (arityLimit d) B)
    {a b : ℕ} (ha : a ∈ heavyClusterStarts d K C B) (hb : b ∈ heavyClusterStarts d K C B)
    (hab : a < b) : a + 36 * d ≤ b :=
  clusterStarts_separated (clusterWidth_pos d) (by omega)
    (heavyLevels_gapFree hK hC hcover hB) ha hb hab

theorem heavyClusterStarts_bound {d K start : ℕ} {C B : Finset ℕ}
    (hstart : start ∈ heavyClusterStarts d K C B) : start ≤ 6 * d ^ 2 := by
  have hmem := clusterStarts_subset (clusterWidth_pos d) hstart
  have hbound := Finset.mem_range.mp (Finset.mem_filter.mp hmem).1
  unfold levelCount at hbound
  omega

theorem heavyCluster_digit_data {d K start j : ℕ} {C B : Finset ℕ}
    (hd : 0 < d) (hK : 0 < K) (hshort : 12 * clusterWidth d ≤ d)
    (hC : ∀ u ∈ C, baseRange d ≤ u ∧ u < 2 * baseRange d)
    (hcover : SumCover C K (sumThreshold d)) (hB : RepeatedSumFree (arityLimit d) B)
    (hstart : start ∈ heavyClusterStarts d K C B)
    (hj : j ∈ levelCluster (heavyLevels (levelCount d) K C B) (clusterWidth d) start) :
    let previous := (heavyClusterStarts d K C B).filter (fun i => i < start)
    (previous.image (assignedDigit d (6 * d) start)).card = previous.card ∧
      previous.card ≤ d / 6 ∧
      ∀ i ∈ previous,
        2 ≤ assignedDigit d (6 * d) start i ∧ assignedDigit d (6 * d) start i ≤ d - 4 ∧
        d * (6 * d) + 2 * (6 * d) ≤ j - i + (6 * d) * assignedDigit d (6 * d) start i ∧
        j - i + (6 * d) * assignedDigit d (6 * d) start i < d * (6 * d) + 4 * (6 * d) := by
  have hframe := cluster_member_bounds (clusterWidth_pos d) (by omega)
    (heavyLevels_gapFree hK hC hcover hB) hstart hj
  apply predecessor_digit_data (heavyClusterStarts d K C B) (by omega) hstart
    (by have h := heavyClusterStarts_bound hstart; nlinarith)
    (fun a ha b hb hab => by
      have h := heavyClusterStarts_separated hK hshort hC hcover hB ha hb hab
      omega)
    hframe.1 hframe.2 (by omega)

end AuxiliaryParameters
end Erdos790.Upper
