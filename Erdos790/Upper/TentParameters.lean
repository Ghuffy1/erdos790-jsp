import Erdos790.Upper.DeterministicTents
import Erdos790.Upper.GrowthBounds
import Mathlib.Data.Nat.Log

/-!
# The dyadic amplification and the eventual radix margin
-/

open Filter

namespace Erdos790.Upper.AuxiliaryParameters

noncomputable def gapScale (d : ℕ) : ℕ := 2 * sampleSize d * coefficientRange d + 1
noncomputable def clusterWidth (d : ℕ) : ℕ := Nat.log 2 (gapScale d) + 1
noncomputable def tentAmplification (d : ℕ) : ℕ := 2 ^ (clusterWidth d + 3)

theorem gapScale_pos (d : ℕ) : 0 < gapScale d := by unfold gapScale; omega

theorem gapScale_lt_power (d : ℕ) : gapScale d < 2 ^ clusterWidth d :=
  Nat.lt_pow_succ_log_self (by decide) _

theorem tentAmplification_le_gapScale (d : ℕ) : tentAmplification d ≤ 16 * gapScale d := by
  have hlog := Nat.pow_log_le_self 2 (gapScale_pos d).ne'
  unfold tentAmplification clusterWidth
  rw [show Nat.log 2 (gapScale d) + 1 + 3 = Nat.log 2 (gapScale d) + 4 by omega, pow_add]
  norm_num
  simpa only [Nat.mul_comm] using Nat.mul_le_mul_right 16 hlog

theorem gapScale_le_sixth_power (d : ℕ) : gapScale d ≤ 201 * roughScale d ^ 6 := by
  have hsample := sampleSize_le_fourth_power d
  have hproduct : 2 * sampleSize d * coefficientRange d ≤ 200 * roughScale d ^ 6 := by
    calc
      _ ≤ 2 * roughScale d ^ 4 * coefficientRange d :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 hsample)
      _ = 200 * roughScale d ^ 6 := by unfold coefficientRange; ring
  have hone : 1 ≤ roughScale d ^ 6 := Nat.one_le_pow _ _ (by have h := roughScale_large d; omega)
  unfold gapScale
  nlinarith

theorem roughScale_le_quadratic (d : ℕ) : roughScale d ≤ 700000 * (d + 1) ^ 2 := by
  unfold roughScale levelCount
  nlinarith [Nat.zero_le d, Nat.zero_le (d ^ 2)]

theorem amplification_le_polynomial (d : ℕ) :
    tentAmplification d ≤ (3216 * 700000 ^ 6) * (d + 1) ^ 12 := by
  calc
    tentAmplification d ≤ 16 * gapScale d := tentAmplification_le_gapScale d
    _ ≤ 16 * (201 * roughScale d ^ 6) := Nat.mul_le_mul_left 16 (gapScale_le_sixth_power d)
    _ = 3216 * roughScale d ^ 6 := by ring
    _ ≤ 3216 * (700000 * (d + 1) ^ 2) ^ 6 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (roughScale_le_quadratic d) 6)
    _ = (3216 * 700000 ^ 6) * (d + 1) ^ 12 := by rw [mul_pow, ← pow_mul]; ring

theorem eventual_radix_margin : ∀ᶠ d : ℕ in atTop,
    32 * (tentAmplification d * timeCount d + 1) * timeCount d ≤ radixBase d := by
  have hpoly := eventually_polynomial_le_power (64 * (3216 * 700000 ^ 6)) 12 4 (by decide)
  filter_upwards [hpoly, eventually_ge_atTop 2] with d hpoly hd
  have hamp : 64 * tentAmplification d ≤ 2 ^ (2 * d) := by
    calc
      _ ≤ 64 * ((3216 * 700000 ^ 6) * (d + 1) ^ 12) :=
        Nat.mul_le_mul_left _ (amplification_le_polynomial d)
      _ = (64 * (3216 * 700000 ^ 6)) * (d + 1) ^ 12 := by ring
      _ ≤ 4 ^ d := hpoly
      _ = 2 ^ (2 * d) := by rw [pow_mul]; norm_num
  have hconstant : 64 ≤ 2 ^ (4 * d) := by
    have h := Nat.pow_le_pow_right (by decide : 0 < 2) (show 6 ≤ 4 * d by omega)
    norm_num at h
    exact h
  have hlarge : 64 * tentAmplification d * 2 ^ (4 * d) ≤ 2 ^ (6 * d) := by
    calc
      _ ≤ 2 ^ (2 * d) * 2 ^ (4 * d) := Nat.mul_le_mul_right _ hamp
      _ = 2 ^ (6 * d) := by rw [← pow_add]; congr 1; omega
  have hsmall : 64 * 2 ^ (2 * d) ≤ 2 ^ (6 * d) := by
    calc
      _ ≤ 2 ^ (4 * d) * 2 ^ (2 * d) := Nat.mul_le_mul_right _ hconstant
      _ = 2 ^ (6 * d) := by rw [← pow_add]; congr 1; omega
  have hproduct : (2 ^ (2 * d)) ^ 2 = 2 ^ (4 * d) := by rw [← pow_mul]; congr 1; omega
  unfold timeCount radixBase
  nlinarith

theorem eventual_tent_host : ∀ᶠ d : ℕ in atTop,
    ∃ offset : Fin (sampleSize d) → ℕ,
      (∀ i, offset i < blockCount d * factorialModulus d ∧
        Nat.Coprime (offset i) (factorialModulus d)) ∧
      Function.Injective (fun i => offset i % factorialModulus d) ∧
      let C := translatedHost (baseRange d) offset (tentTranslations d (tentAmplification d))
      C.card = sampleSize d * 2 ^ (3 * d) ∧
      (∀ x ∈ C, baseRange d ≤ x ∧ x < 2 * baseRange d ∧ Nat.Coprime x (factorialModulus d)) ∧
      SumCover C (C.card / levelCount d) (sumThreshold d) := by
  filter_upwards [eventual_radix_margin, eventually_ge_atTop 1] with d hmargin hd
  have hdpos : 0 < d := by omega
  obtain ⟨offset, hoffset, hinjective, hcard, hbounds, hcover⟩ :=
    tent_auxiliary_host_exists hdpos hmargin
  refine ⟨offset, hoffset, hinjective, ?_, hbounds, ?_⟩
  · simpa only [tentTranslations_card hdpos hmargin] using hcard
  · have hthreshold :
        (translatedHost (baseRange d) offset (tentTranslations d (tentAmplification d))).card /
            levelCount d =
          2 * sampleExponent d * (tentTranslations d (tentAmplification d)).card := by
      rw [hcard]
      change (2 * levelCount d * sampleExponent d * _) / levelCount d = _
      rw [show 2 * levelCount d * sampleExponent d *
          (tentTranslations d (tentAmplification d)).card =
          levelCount d * (2 * sampleExponent d *
            (tentTranslations d (tentAmplification d)).card) by ring]
      exact Nat.mul_div_cancel_left _ (levelCount_pos d)
    rw [hthreshold]
    exact hcover

theorem eventual_clusterWidth_bound : ∀ᶠ d : ℕ in atTop, 12 * clusterWidth d ≤ d := by
  have hpoly := eventually_polynomial_le_power_div (3216 * 700000 ^ 6) 12 2 12
    (by decide) (by decide)
  filter_upwards [hpoly] with d hpoly
  have hamp : 2 ^ (clusterWidth d + 3) ≤ 2 ^ (d / 12) :=
    (amplification_le_polynomial d).trans hpoly
  have hexponent : clusterWidth d + 3 ≤ d / 12 :=
    (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp hamp
  have hdiv := Nat.div_mul_le_self d 12
  nlinarith

end Erdos790.Upper.AuxiliaryParameters
