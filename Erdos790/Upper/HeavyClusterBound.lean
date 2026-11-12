import Erdos790.Upper.HeavyMixedExclusion
import Erdos790.Upper.RecursiveMass
import Erdos790.Upper.ClusterCoordinates

/-!
# Recursive counting for a fixed exterior profile in a heavy cluster
-/

namespace Erdos790.Upper.AuxiliaryParameters

theorem heavy_cluster_occurrence_unique {d K start constant step : ℕ} {C B : Finset ℕ}
    (E : Finset (ℕ × ℤ × (Fin d → Fin 2))) (fixed : Fin d → Fin 2)
    (hd : 0 < d) (hK : 0 < K) (hshort : 12 * clusterWidth d ≤ d)
    (hC : ∀ u ∈ C, baseRange d ≤ u ∧ u < 2 * baseRange d)
    (hcover : SumCover C K (sumThreshold d)) (hB : RepeatedSumFree (arityLimit d) B)
    (hstart : start ∈ heavyClusterStarts d K C B)
    (hlevels : ∀ p ∈ E,
      p.1 ∈ levelCluster (heavyLevels (levelCount d) K C B) (clusterWidth d) start)
    (hfixed : ∀ p ∈ E, ∀ h, h ∉ assignedPositions d (6 * d) start
      ((heavyClusterStarts d K C B).filter (fun i => i < start)) → p.2.2 h = fixed h)
    (hselected : ∀ p ∈ E,
      2 ^ p.1 * nativeTentValue (tentAmplification d) (2 ^ (6 * d)) constant
        (factorialModulus d) step p.2.1.toNat p.2.2 ∈ B) :
    ∀ j t a b, (j, t, a) ∈ E → (j, t, b) ∈ E → a = b := by
  classical
  intro j t a b ha hb
  have hcard := heavy_cluster_coordinates_card (occurrenceFamily E) fixed hd hK hshort
    hC hcover hB hstart (hlevels (j, t, a) ha)
    (fun t word hword h hh => hfixed (j, t, word) (mem_occurrenceFamily.mp hword) h hh)
    (fun t word hword => hselected (j, t, word) (mem_occurrenceFamily.mp hword))
  have hinj : Set.InjOn (Prod.fst : (ℤ × (Fin d → Fin 2)) → ℤ) ↑(occurrenceFamily E j) :=
    Finset.card_image_iff.mp hcard
  have heq := hinj (mem_occurrenceFamily.mpr ha) (mem_occurrenceFamily.mpr hb) rfl
  exact congrArg (fun p : ℤ × (Fin d → Fin 2) => p.2) heq

theorem heavy_cluster_fixed_profile_bound {d K start constant step : ℕ} {C B : Finset ℕ}
    (E : Finset (ℕ × ℤ × (Fin d → Fin 2))) (fixed : Fin d → Fin 2)
    (hd : 48 ≤ d) (hK : 0 < K) (hshort : 12 * clusterWidth d ≤ d)
    (hmargin : 32 * (tentAmplification d * timeCount d + 1) * timeCount d ≤ radixBase d)
    (hC : ∀ u ∈ C, baseRange d ≤ u ∧ u < 2 * baseRange d)
    (hcover : SumCover C K (sumThreshold d)) (hB : RepeatedSumFree (arityLimit d) B)
    (hstart : start ∈ heavyClusterStarts d K C B)
    (hlevels : ∀ p ∈ E,
      p.1 ∈ levelCluster (heavyLevels (levelCount d) K C B) (clusterWidth d) start)
    (hcoordinates : ∀ p ∈ E, 0 ≤ p.2.1 ∧ p.2.1 < timeCount d)
    (hfixed : ∀ p ∈ E, ∀ h, h ∉ assignedPositions d (6 * d) start
      ((heavyClusterStarts d K C B).filter (fun i => i < start)) → p.2.2 h = fixed h)
    (hselected : ∀ p ∈ E,
      2 ^ p.1 * nativeTentValue (tentAmplification d) (2 ^ (6 * d)) constant
        (factorialModulus d) step p.2.1.toNat p.2.2 ∈ B) :
    let positions := assignedPositions d (6 * d) start
      ((heavyClusterStarts d K C B).filter (fun i => i < start))
    (E.card : ℝ) ≤ (2 : ℝ) ^ positions.card * clusterSequence 1200 positions.card * timeCount d := by
  classical
  let positions := assignedPositions d (6 * d) start
    ((heavyClusterStarts d K C B).filter (fun i => i < start))
  have hdpos : 0 < d := by omega
  have hstartHeavy := clusterStarts_subset (clusterWidth_pos d) hstart
  have hself : start ∈ levelCluster (heavyLevels (levelCount d) K C B) (clusterWidth d) start :=
    Finset.mem_filter.mpr ⟨hstartHeavy, levelClose_refl (clusterWidth_pos d) start⟩
  have hdata := heavy_cluster_profile_data hdpos hK hshort hC hcover hB hstart hself
  have hcount : positions.card ≤ d / 6 := hdata.2.1
  have hfree : 6 * positions.card ≤ d := by
    have hdiv := Nat.div_mul_le_self d 6
    omega
  have hR : 2 ^ clusterWidth d ≤ arityLimit d := by
    unfold arityLimit
    apply Nat.pow_le_pow_right (by decide)
    omega
  let value : ℤ → (Fin d → Fin 2) → ℕ := fun t =>
    nativeTentValue (tentAmplification d) (2 ^ (6 * d)) constant (factorialModulus d) step t.toNat
  have hbound := recursive_occurrence_bound (start := start) value hd hshort (clusterWidth_pos d)
    hB hR positions.card positions fixed E 0 (2 * d) rfl hfree
    (fun H hH => by have := H.isLt; omega) (dvd_zero _)
    (by simpa only [Nat.cast_zero, zero_add, timeCount] using hcoordinates)
    (fun p hp => cluster_member_bounds (clusterWidth_pos d) (by omega)
      (heavyLevels_gapFree hK hC hcover hB) hstart (hlevels p hp))
    (heavy_cluster_occurrence_unique E fixed hdpos hK hshort hC hcover hB hstart hlevels hfixed hselected)
    hfixed hselected
    (heavy_cluster_mixed_exclusion E hdpos hK hshort hmargin hC hcover hB hstart hlevels hselected)
  simpa only [timeCount, Nat.cast_pow, Nat.cast_ofNat] using hbound

end Erdos790.Upper.AuxiliaryParameters
