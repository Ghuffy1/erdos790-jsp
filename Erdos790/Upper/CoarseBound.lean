import Erdos790.Upper.HeavyClusterMass
import Erdos790.Upper.ClusterSums

/-!
# A uniform independence bound for the constructed coarse host
-/

namespace Erdos790.Upper

noncomputable def coarseConstant : ℝ := 1 + ∑' n, clusterSequence 1200 n

theorem coarseConstant_pos : 0 < coarseConstant := by
  have hnonneg : 0 ≤ ∑' n, clusterSequence 1200 n :=
    tsum_nonneg (clusterSequence_nonneg (by norm_num : (0 : ℝ) ≤ 1200))
  unfold coarseConstant
  linarith

namespace AuxiliaryParameters

theorem coarse_independence_bound {d J : ℕ} (offset : Fin J → ℕ) {C B : Finset ℕ}
    (hd : 48 ≤ d) (hshort : 12 * clusterWidth d ≤ d)
    (hmargin : 32 * (tentAmplification d * timeCount d + 1) * timeCount d ≤ radixBase d)
    (hCeq : C = translatedHost (baseRange d) offset (tentTranslations d (tentAmplification d)))
    (hC : ∀ u ∈ C, baseRange d ≤ u ∧ u < 2 * baseRange d)
    (hcard : C.card = J * 2 ^ (3 * d))
    (hK : 0 < C.card / levelCount d)
    (hcover : SumCover C (C.card / levelCount d) (sumThreshold d))
    (hB : RepeatedSumFree (arityLimit d) B) (hsubset : B ⊆ layeredHost (levelCount d) C) :
    (B.card : ℝ) ≤ coarseConstant * C.card := by
  classical
  let L := levelCount d
  let K := C.card / L
  let heavy := heavyLevels L K C B
  let light := (Finset.range L).filter (fun j => (levelSlice j C B).card < K)
  let starts := heavyClusterStarts d K C B
  let weight := fun j => ((levelSlice j C B).card : ℝ)
  have hdisjoint : Disjoint heavy light := by
    apply Finset.disjoint_left.mpr
    intro j hj hk
    have hheavy := (Finset.mem_filter.mp hj).2
    have hlight := (Finset.mem_filter.mp hk).2
    omega
  have hunion : heavy ∪ light = Finset.range L := by
    ext j
    simp only [Finset.mem_union, heavy, heavyLevels, light, Finset.mem_filter]
    constructor
    · rintro (⟨hj, h⟩ | ⟨hj, h⟩) <;> exact hj
    · intro hj
      by_cases h : K ≤ (levelSlice j C B).card
      · exact Or.inl ⟨hj, h⟩
      · exact Or.inr ⟨hj, lt_of_not_ge h⟩
  have hsplit : (∑ j ∈ Finset.range L, weight j) =
      (∑ j ∈ heavy, weight j) + ∑ j ∈ light, weight j := by
    rw [← hunion, Finset.sum_union hdisjoint]
  have hlightNat : (∑ j ∈ light, (levelSlice j C B).card) ≤ C.card := by
    have h := light_level_mass_le L K C B
    have hLK : L * K ≤ C.card := by
      have hdiv := Nat.div_mul_le_self C.card L
      simpa only [K, Nat.mul_comm] using hdiv
    exact h.trans hLK
  have hlightReal : (∑ j ∈ light, weight j) ≤ (C.card : ℝ) := by
    change (∑ j ∈ light, ((levelSlice j C B).card : ℝ)) ≤ (C.card : ℝ)
    exact_mod_cast hlightNat
  have hgap := heavyLevels_gapFree (show 0 < K from hK) hC hcover hB
  have hpartition : (∑ j ∈ heavy, weight j) =
      ∑ a ∈ starts, ∑ j ∈ levelCluster heavy (clusterWidth d) a, weight j :=
    levelClusters_sum (clusterWidth_pos d) (by omega) hgap weight
  have hcardReal : (C.card : ℝ) = (J : ℝ) * (2 : ℝ) ^ (3 * d) := by exact_mod_cast hcard
  have hcluster : ∀ a ∈ starts, (∑ j ∈ levelCluster heavy (clusterWidth d) a, weight j) ≤
      (C.card : ℝ) * clusterSequence 1200 (starts.filter (fun i => i < a)).card := by
    intro a ha
    have h := heavy_cluster_mass_bound offset hd (show 0 < K from hK) hshort hmargin
      hCeq hC hcover hB ha
    push_cast at h
    rw [← hcardReal] at h
    exact h
  have hnonneg := clusterSequence_nonneg (by norm_num : (0 : ℝ) ≤ 1200)
  have hsummable := (clusterSequence_summable (by norm_num : (0 : ℝ) ≤ 1200)).1
  have hranks := cluster_rank_sum_le_tsum starts hnonneg hsummable
  have hheavyReal : (∑ j ∈ heavy, weight j) ≤
      (C.card : ℝ) * (∑' n, clusterSequence 1200 n) := by
    rw [hpartition]
    calc
      _ ≤ ∑ a ∈ starts, (C.card : ℝ) *
          clusterSequence 1200 (starts.filter (fun i => i < a)).card := Finset.sum_le_sum hcluster
      _ = (C.card : ℝ) * (∑ a ∈ starts,
          clusterSequence 1200 (starts.filter (fun i => i < a)).card) := (Finset.mul_sum ..).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hranks (by positivity)
  have htotal : (B.card : ℝ) = ∑ j ∈ Finset.range L, weight j := by
    change (B.card : ℝ) = ∑ j ∈ Finset.range (levelCount d), ((levelSlice j C B).card : ℝ)
    exact_mod_cast selected_layer_card_sum hC hsubset
  rw [htotal, hsplit]
  unfold coarseConstant
  nlinarith

end AuxiliaryParameters
end Erdos790.Upper
