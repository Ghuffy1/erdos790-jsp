import Erdos790.Upper.ClusterMultiplicity
import Erdos790.Upper.HeavyClusters

/-!
# Bit profiles assigned to the actual earlier heavy clusters
-/

namespace Erdos790.Upper

def assignedPositions (d width start : ℕ) (previous : Finset ℕ) : Finset (Fin d) :=
  Finset.univ.filter (fun h => h.val ∈ previous.image (assignedDigit d width start))

theorem assignedPositions_card {d width start : ℕ} (previous : Finset ℕ)
    (hbound : ∀ i ∈ previous, assignedDigit d width start i < d) :
    (assignedPositions d width start previous).card =
      (previous.image (assignedDigit d width start)).card := by
  classical
  have himage : (assignedPositions d width start previous).image Fin.val =
      previous.image (assignedDigit d width start) := by
    ext n
    constructor
    · intro hn
      obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hn
      exact (Finset.mem_filter.mp hh).2
    · intro hn
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hn
      exact Finset.mem_image.mpr ⟨⟨_, hbound i hi⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩, rfl⟩
  rw [← himage, Finset.card_image_of_injOn (fun _ _ _ _ h => Fin.ext h)]

namespace AuxiliaryParameters

theorem arityLimit_eq_radix (d : ℕ) : arityLimit d = (2 ^ (6 * d)) ^ 6 := by
  unfold arityLimit
  rw [← pow_mul]
  congr 1
  omega

theorem bit_profile_threshold {d : ℕ} (hshort : 12 * clusterWidth d ≤ d) :
    2 * sumThreshold d ≤ (2 ^ (6 * d)) ^ 2 * baseRange d := by
  have hgap : sumThreshold d ≤ gapScale d * baseRange d := by
    unfold sumThreshold gapScale
    exact Nat.mul_le_mul_right _ (Nat.le_succ _)
  have hsmall : clusterWidth d + 1 ≤ 12 * d := by
    have := clusterWidth_pos d
    omega
  calc
    2 * sumThreshold d ≤ 2 * (gapScale d * baseRange d) := Nat.mul_le_mul_left 2 hgap
    _ ≤ 2 * (2 ^ clusterWidth d * baseRange d) :=
      Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right _ (gapScale_lt_power d).le)
    _ = 2 ^ (clusterWidth d + 1) * baseRange d := by rw [pow_succ']; ring
    _ ≤ 2 ^ (12 * d) * baseRange d :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) hsmall)
    _ = (2 ^ (6 * d)) ^ 2 * baseRange d := by rw [← pow_mul]; congr 2; omega

theorem heavy_cluster_profile_data {d K start j : ℕ} {C B : Finset ℕ}
    (hd : 0 < d) (hK : 0 < K) (hshort : 12 * clusterWidth d ≤ d)
    (hC : ∀ u ∈ C, baseRange d ≤ u ∧ u < 2 * baseRange d)
    (hcover : SumCover C K (sumThreshold d)) (hB : RepeatedSumFree (arityLimit d) B)
    (hstart : start ∈ heavyClusterStarts d K C B)
    (hj : j ∈ levelCluster (heavyLevels (levelCount d) K C B) (clusterWidth d) start) :
    let previous := (heavyClusterStarts d K C B).filter (fun i => i < start)
    let positions := assignedPositions d (6 * d) start previous
    positions.card = previous.card ∧ positions.card ≤ d / 6 ∧
      ∀ H ∈ positions, ∃ i, i ≤ j ∧ K ≤ (levelSlice i C B).card ∧
        (2 ^ (6 * d)) ^ 2 * baseRange d ≤
          factorialModulus d * 2 ^ (j - i) * (2 ^ (6 * d)) ^ H.val ∧
        factorialModulus d * 2 ^ (j - i) * (2 ^ (6 * d)) ^ H.val ≤
          (2 ^ (6 * d)) ^ 4 * baseRange d := by
  classical
  let previous := (heavyClusterStarts d K C B).filter (fun i => i < start)
  let positions := assignedPositions d (6 * d) start previous
  have hdata := heavyCluster_digit_data hd hK hshort hC hcover hB hstart hj
  change (previous.image (assignedDigit d (6 * d) start)).card = previous.card ∧
    previous.card ≤ d / 6 ∧ _ at hdata
  have hbound : ∀ i ∈ previous, assignedDigit d (6 * d) start i < d := by
    intro i hi
    have h := hdata.2.2 i hi
    omega
  have hcard : positions.card = previous.card :=
    (assignedPositions_card previous hbound).trans hdata.1
  refine ⟨hcard, hcard.le.trans hdata.2.1, ?_⟩
  intro H hH
  obtain ⟨i, hi, hiH⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hH).2
  have hiStart := Finset.mem_filter.mp hi
  have hiHeavy := clusterStarts_subset (clusterWidth_pos d) hiStart.1
  have hframe := cluster_member_bounds (clusterWidth_pos d) (by omega)
    (heavyLevels_gapFree hK hC hcover hB) hstart hj
  have hscale := assigned_bit_scale_bounds (Q := factorialModulus d)
    (hdata.2.2 i hi).2.2.1 (hdata.2.2 i hi).2.2.2
  have hbase : factorialModulus d * (2 ^ (6 * d)) ^ d = baseRange d := by
    unfold baseRange
    rw [← pow_mul]
    congr 2
    ring
  rw [hbase, hiH] at hscale
  exact ⟨i, by omega, (Finset.mem_filter.mp hiHeavy).2, hscale.1, hscale.2⟩

theorem heavy_cluster_selected_profiles {d K start j amplification constant step t : ℕ}
    {C B : Finset ℕ} (fixed : Fin d → Fin 2) (words : Finset (Fin d → Fin 2))
    (hd : 0 < d) (hK : 0 < K) (hshort : 12 * clusterWidth d ≤ d)
    (hC : ∀ u ∈ C, baseRange d ≤ u ∧ u < 2 * baseRange d)
    (hcover : SumCover C K (sumThreshold d)) (hB : RepeatedSumFree (arityLimit d) B)
    (hstart : start ∈ heavyClusterStarts d K C B)
    (hj : j ∈ levelCluster (heavyLevels (levelCount d) K C B) (clusterWidth d) start)
    (hfixed : ∀ a ∈ words, ∀ h,
      h ∉ assignedPositions d (6 * d) start
        ((heavyClusterStarts d K C B).filter (fun i => i < start)) → a h = fixed h)
    (hselected : ∀ a ∈ words,
      2 ^ j * nativeTentValue amplification (2 ^ (6 * d)) constant
        (factorialModulus d) step t a ∈ B) : words.card ≤ 1 := by
  have hq : 3 ≤ 2 ^ (6 * d) := by
    have h := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (show 2 ≤ 6 * d by omega)
    norm_num at h
    omega
  have hdata := heavy_cluster_profile_data hd hK hshort hC hcover hB hstart hj
  apply selected_profiles_card_le_one C B _ fixed words hq (baseRange_pos d) hC hcover
    (by simpa only [arityLimit_eq_radix] using hB) (bit_profile_threshold hshort)
    hdata.2.2 hfixed hselected

theorem heavy_cluster_occurrences_card_le {d K start : ℕ} {C B : Finset ℕ}
    (occurrences : Finset (ℕ × (Fin d → Fin 2))) (free : Finset (Fin d))
    (fixed : Fin d → Fin 2) (value : (Fin d → Fin 2) → ℕ)
    (hK : 0 < K) (hshort : 12 * clusterWidth d ≤ d)
    (hC : ∀ u ∈ C, baseRange d ≤ u ∧ u < 2 * baseRange d)
    (hcover : SumCover C K (sumThreshold d)) (hB : RepeatedSumFree (arityLimit d) B)
    (hstart : start ∈ heavyClusterStarts d K C B)
    (hlevels : ∀ p ∈ occurrences,
      p.1 ∈ levelCluster (heavyLevels (levelCount d) K C B) (clusterWidth d) start)
    (hfixed : ∀ p ∈ occurrences, ∀ h, h ∉ free → p.2 h = fixed h)
    (hselected : ∀ p ∈ occurrences, 2 ^ p.1 * value p.2 ∈ B) :
    occurrences.card ≤ 2 ^ free.card := by
  apply binary_occurrences_card_le occurrences free fixed value hB
    (delay := clusterWidth d) (start := start)
  · unfold arityLimit
    exact Nat.pow_le_pow_right (by decide) (by omega)
  · intro p hp
    exact cluster_member_bounds (clusterWidth_pos d) (by omega)
      (heavyLevels_gapFree hK hC hcover hB) hstart (hlevels p hp)
  · exact hfixed
  · exact hselected

end AuxiliaryParameters
end Erdos790.Upper
