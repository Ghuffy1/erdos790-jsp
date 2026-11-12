import Erdos790.Upper.CoarseBound

/-!
# The unconditional coarse construction for all large parameters
-/

open Filter

namespace Erdos790.Upper.AuxiliaryParameters

noncomputable def coarseSize (d : ℕ) : ℕ := sampleSize d * 2 ^ (3 * d)

theorem coarseSize_pos (d : ℕ) : 0 < coarseSize d := by
  have hL := levelCount_pos d
  have hk := sampleExponent_pos d
  unfold coarseSize sampleSize
  positivity

theorem coarseSize_div_levelCount (d : ℕ) :
    coarseSize d / levelCount d = 2 * sampleExponent d * 2 ^ (3 * d) := by
  unfold coarseSize sampleSize
  rw [show 2 * levelCount d * sampleExponent d * 2 ^ (3 * d) =
    levelCount d * (2 * sampleExponent d * 2 ^ (3 * d)) by ring]
  exact Nat.mul_div_cancel_left _ (levelCount_pos d)

theorem eventual_coarse_host : ∀ᶠ d : ℕ in atTop,
    ∃ F : Finset ℕ,
      F.card = levelCount d * coarseSize d ∧
      (∀ a ∈ F, 0 < a) ∧
      ∀ B ⊆ F, RepeatedSumFree (arityLimit d) B →
        (B.card : ℝ) ≤ coarseConstant * coarseSize d := by
  filter_upwards [eventual_tent_host, eventual_clusterWidth_bound,
    eventual_radix_margin, eventually_ge_atTop 48] with d hhost hshort hmargin hd
  obtain ⟨offset, _, _, hcard, hbounds, hcover⟩ := hhost
  let C := translatedHost (baseRange d) offset
    (tentTranslations d (tentAmplification d))
  have hC : ∀ u ∈ C, baseRange d ≤ u ∧ u < 2 * baseRange d :=
    fun u hu => ⟨(hbounds u hu).1, (hbounds u hu).2.1⟩
  have hsize : C.card = coarseSize d := hcard
  have hK : 0 < C.card / levelCount d := by
    rw [hsize, coarseSize_div_levelCount]
    have hk := sampleExponent_pos d
    positivity
  refine ⟨layeredHost (levelCount d) C, ?_, ?_, ?_⟩
  · rw [layeredHost_card hC, hsize]
  · intro a ha
    obtain ⟨j, _, hja⟩ := Finset.mem_biUnion.mp ha
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hja
    exact Nat.mul_pos (Nat.two_pow_pos j) ((baseRange_pos d).trans_le (hC u hu).1)
  · intro B hBF hB
    have h := coarse_independence_bound offset hd hshort hmargin rfl hC hcard hK hcover hB hBF
    change (B.card : ℝ) ≤ coarseConstant * C.card at h
    rwa [hsize] at h

end Erdos790.Upper.AuxiliaryParameters
