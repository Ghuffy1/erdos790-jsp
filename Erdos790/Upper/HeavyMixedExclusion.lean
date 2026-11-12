import Erdos790.Upper.RecursiveExclusion
import Erdos790.Upper.AssignedProfiles

/-!
# Mixed-mean exclusion in the actual heavy clusters
-/

namespace Erdos790.Upper.AuxiliaryParameters

theorem heavy_cluster_mixed_exclusion {d K start constant step : ℕ} {C B : Finset ℕ}
    (E : Finset (ℕ × ℤ × (Fin d → Fin 2)))
    (hd : 0 < d) (hK : 0 < K) (hshort : 12 * clusterWidth d ≤ d)
    (hmargin : 32 * (tentAmplification d * timeCount d + 1) * timeCount d ≤ radixBase d)
    (hC : ∀ u ∈ C, baseRange d ≤ u ∧ u < 2 * baseRange d)
    (hcover : SumCover C K (sumThreshold d)) (hB : RepeatedSumFree (arityLimit d) B)
    (hstart : start ∈ heavyClusterStarts d K C B)
    (hlevels : ∀ p ∈ E,
      p.1 ∈ levelCluster (heavyLevels (levelCount d) K C B) (clusterWidth d) start)
    (hselected : ∀ p ∈ E,
      2 ^ p.1 * nativeTentValue (tentAmplification d) (2 ^ (6 * d)) constant
        (factorialModulus d) step p.2.1.toNat p.2.2 ∈ B) :
    MixedExclusion (assignedPositions d (6 * d) start
      ((heavyClusterStarts d K C B).filter (fun i => i < start))) E := by
  classical
  have hbaseIdentity : factorialModulus d * (2 ^ (6 * d)) ^ d = baseRange d := by
    change factorialModulus d * radixBase d ^ d = baseRange d
    rw [radixBase_pow]
    rfl
  have hC' : ∀ u ∈ C,
      factorialModulus d * (2 ^ (6 * d)) ^ d ≤ u ∧
        u < 2 * (factorialModulus d * (2 ^ (6 * d)) ^ d) := by
    simpa only [hbaseIdentity] using hC
  have hthreshold : sumThreshold d ≤
      (2 ^ (6 * d)) ^ 2 * (factorialModulus d * (2 ^ (6 * d)) ^ d) := by
    rw [hbaseIdentity]
    have h := bit_profile_threshold hshort
    omega
  have hB' : RepeatedSumFree ((2 ^ (6 * d)) ^ 6) B := by
    simpa only [arityLimit_eq_radix] using hB
  let D := tentAmplification d * timeCount d + 1
  have hDpos : 0 < D := by dsimp [D]; omega
  have hDT : D ≤ D * timeCount d := Nat.le_mul_of_pos_right _ (timeCount_pos d)
  have hDnat : D < radixBase d := by
    change 32 * D * timeCount d ≤ radixBase d at hmargin
    nlinarith
  have hDint : (tentAmplification d : ℤ) * timeCount d + 1 ≤ (2 : ℤ) ^ (6 * d) - 1 := by
    have hcast : (tentAmplification d : ℤ) * timeCount d + 1 < (2 : ℤ) ^ (6 * d) := by
      exact_mod_cast hDnat
    omega
  intro H hH F hFE a halign hframe hwords p hp
  have hpLevel := hlevels p (hFE hp)
  have hdata := heavyCluster_digit_data hd hK hshort hC hcover hB hstart hpLevel
  obtain ⟨i, hi, hiH⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hH).2
  have hiStart := Finset.mem_filter.mp hi
  have hiHeavy := clusterStarts_subset (clusterWidth_pos d) hiStart.1
  have hiCount : K ≤ (levelSlice i C B).card := (Finset.mem_filter.mp hiHeavy).2
  have hindex := hdata.2.2 i hi
  have hindexLower : d * (6 * d) + 2 * (6 * d) ≤ p.1 - i + (6 * d) * H.val := by
    simpa only [hiH] using hindex.2.2.1
  have hindexUpper : p.1 - i + (6 * d) * H.val < d * (6 * d) + 4 * (6 * d) := by
    simpa only [hiH] using hindex.2.2.2
  have hpBounds := cluster_member_bounds (clusterWidth_pos d) (by omega)
    (heavyLevels_gapFree hK hC hcover hB) hstart hpLevel
  have halign' : 2 * 2 ^ (d + H.val) ∣ a := by
    simpa only [pow_succ'] using halign
  have hheadCast : (p.2.1.toNat : ℤ) = p.2.1 := by
    apply Int.toNat_of_nonneg
    have hleft := (hframe p hp).1
    have ha : (0 : ℤ) ≤ a := by positivity
    omega
  have hhead : (p.2.1.toNat : ℤ) ∈ selectedCoordinates (occurrenceFamily F) p.1 := by
    rw [hheadCast]
    exact mem_occurrenceCoordinates.mpr ⟨p.2.2, hp⟩
  have hnot := selectedCoordinates_not_dyadic_mean
    (earlier := i) (start := start) (j := p.1) (delay := clusterWidth d) (width := 6 * d)
    (Q := factorialModulus d) (U := step) (constant := constant) (head := p.2.1.toNat)
    (a := a) (K := K) (threshold := sumThreshold d)
    (tentAmplification d) H (occurrenceFamily F) p.2.2 C B
    (by omega) (factorialModulus_pos d) hiStart.2.le rfl hpBounds.2 (by omega)
    hDint halign' hindexLower hindexUpper
    (fun k t word hword => by
      have hmem := mem_occurrenceFamily.mp hword
      have hlevel := hlevels (k, t, word) (hFE hmem)
      have hb := cluster_member_bounds (clusterWidth_pos d) (by omega)
        (heavyLevels_gapFree hK hC hcover hB) hstart hlevel
      exact ⟨hb.1, (hframe (k, t, word) hmem).1, (hframe (k, t, word) hmem).2⟩)
    (fun k t word hword h hh => hwords (k, t, word) (mem_occurrenceFamily.mp hword) p hp h hh)
    (fun k t word hword => hselected (k, t, word) (hFE (mem_occurrenceFamily.mp hword)))
    hhead hC' hcover hiCount hthreshold hB'
  simpa only [hheadCast, Nat.cast_pow, Nat.cast_ofNat] using hnot

end Erdos790.Upper.AuxiliaryParameters
