import Erdos790.Upper.HeavyRowBound
import Erdos790.Upper.RowOccurrences

/-!
# The mass of an entire heavy cluster in the constructed host
-/

namespace Erdos790.Upper.AuxiliaryParameters

theorem heavy_cluster_mass_bound {d J K start : ℕ} (offset : Fin J → ℕ) {C B : Finset ℕ}
    (hd : 48 ≤ d) (hK : 0 < K) (hshort : 12 * clusterWidth d ≤ d)
    (hmargin : 32 * (tentAmplification d * timeCount d + 1) * timeCount d ≤ radixBase d)
    (hCeq : C = translatedHost (baseRange d) offset (tentTranslations d (tentAmplification d)))
    (hC : ∀ u ∈ C, baseRange d ≤ u ∧ u < 2 * baseRange d)
    (hcover : SumCover C K (sumThreshold d)) (hB : RepeatedSumFree (arityLimit d) B)
    (hstart : start ∈ heavyClusterStarts d K C B) :
    let levels := levelCluster (heavyLevels (levelCount d) K C B) (clusterWidth d) start
    let rank := ((heavyClusterStarts d K C B).filter (fun i => i < start)).card
    ((∑ j ∈ levels, (levelSlice j C B).card : ℕ) : ℝ) ≤
      (J : ℝ) * (2 : ℝ) ^ (3 * d) * clusterSequence 1200 rank := by
  classical
  let levels := levelCluster (heavyLevels (levelCount d) K C B) (clusterWidth d) start
  let positions := assignedPositions d (6 * d) start
    ((heavyClusterStarts d K C B).filter (fun i => i < start))
  let rows := fun i => rowOccurrences d levels (baseRange d + offset i) (rowStep d) B
  let value : Fin J → ℤ → (Fin d → Fin 2) → ℕ := fun i t word =>
    nativeTentValue (tentAmplification d) (2 ^ (6 * d)) (baseRange d + offset i)
      (factorialModulus d) (rowStep d) t.toNat word
  have hrowCover : ∀ j ∈ levels, ∀ u ∈ levelSlice j C B,
      ∃ i t word, (j, t, word) ∈ rows i ∧ value i t word = u := by
    simpa only [hCeq] using translated_rows_cover_selected offset levels B
  have hmass := selected_mass_le_row_occurrences levels C B rows value hrowCover
  have hrowBound : ∀ i : Fin J, ((rows i).card : ℝ) ≤
      (2 : ℝ) ^ (3 * d) * clusterSequence 1200 positions.card := by
    intro i
    apply heavy_cluster_row_bound (rows i) hd hK hshort hmargin hC hcover hB hstart
    · rintro ⟨j, t, word⟩ hp
      exact (mem_rowOccurrences.mp hp).1
    · rintro ⟨j, t, word⟩ hp
      have h := mem_rowOccurrences.mp hp
      exact ⟨h.2.1, h.2.2.1⟩
    · rintro ⟨j, t, word⟩ hp
      exact (mem_rowOccurrences.mp hp).2.2.2
  have hmassReal : ((∑ j ∈ levels, (levelSlice j C B).card : ℕ) : ℝ) ≤
      ∑ i : Fin J, ((rows i).card : ℝ) := by exact_mod_cast hmass
  have hstartHeavy := clusterStarts_subset (clusterWidth_pos d) hstart
  have hself : start ∈ levels :=
    Finset.mem_filter.mpr ⟨hstartHeavy, levelClose_refl (clusterWidth_pos d) start⟩
  have hdata := heavy_cluster_profile_data (by omega : 0 < d) hK hshort hC hcover hB hstart hself
  have hrank : positions.card = ((heavyClusterStarts d K C B).filter (fun i => i < start)).card :=
    hdata.1
  calc
    ((∑ j ∈ levels, (levelSlice j C B).card : ℕ) : ℝ) ≤
        ∑ i : Fin J, ((rows i).card : ℝ) := hmassReal
    _ ≤ ∑ _i : Fin J, (2 : ℝ) ^ (3 * d) * clusterSequence 1200 positions.card :=
      Finset.sum_le_sum (fun i hi => hrowBound i)
    _ = (J : ℝ) * (2 : ℝ) ^ (3 * d) * clusterSequence 1200 positions.card := by simp [mul_assoc]
    _ = _ := by rw [hrank]

end Erdos790.Upper.AuxiliaryParameters
