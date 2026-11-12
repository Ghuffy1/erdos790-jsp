import Erdos790.Upper.Tents
import Erdos790.Upper.RadixSeparation

/-!
# Weighted tent gaps and radix residuals
-/

namespace Erdos790.Upper

theorem integerTent_weighted_gap {ι : Type*} [DecidableEq ι] (I : Finset ι)
    (w : ι → ℚ) (x : ι → ℤ) {M head : ℤ} {W δ : ℚ}
    (hW : 0 < W) (hw : ∀ i ∈ I, 0 ≤ w i)
    (hmass : ∑ i ∈ I, w i = W) (hmean : ∑ i ∈ I, w i * (x i : ℚ) = W * head)
    (hleft : ∃ i ∈ I, x i < M ∧ δ ≤ w i)
    (hright : ∃ i ∈ I, M ≤ x i ∧ δ ≤ w i) :
    (∑ i ∈ I, w i * (integerTent M (x i) : ℚ)) + 2 * δ ≤ W * integerTent M head := by
  have hdivide (f : ι → ℚ) :
      (∑ i ∈ I, (w i / W) * f i) = (∑ i ∈ I, w i * f i) / W := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hmass' : ∑ i ∈ I, w i / W = 1 := by
    rw [← Finset.sum_div, hmass, div_self hW.ne']
  have hmean' : ∑ i ∈ I, (w i / W) * (x i : ℚ) = head := by
    rw [hdivide, hmean]
    field_simp
  have hleft' : ∃ i ∈ I, x i < M ∧ δ / W ≤ w i / W := by
    obtain ⟨i, hi, hx, hδ⟩ := hleft
    exact ⟨i, hi, hx, div_le_div_of_nonneg_right hδ hW.le⟩
  have hright' : ∃ i ∈ I, M ≤ x i ∧ δ / W ≤ w i / W := by
    obtain ⟨i, hi, hx, hδ⟩ := hright
    exact ⟨i, hi, hx, div_le_div_of_nonneg_right hδ hW.le⟩
  have hgap := integerTent_mixed_gap I (fun i => w i / W) x
    (fun i hi => div_nonneg (hw i hi) hW.le) hmass' hmean' hleft' hright'
  rw [hdivide] at hgap
  have hgap' : ((∑ i ∈ I, w i * (integerTent M (x i) : ℚ)) + 2 * δ) / W ≤
      (integerTent M head : ℚ) := by
    simpa only [add_div, mul_div_assoc] using hgap
  exact (div_le_iff₀ hW).mp hgap' |>.trans_eq (mul_comm _ _)

theorem integerTent_weighted_gap_int {ι : Type*} [DecidableEq ι] (I : Finset ι)
    (w x : ι → ℤ) {M head W δ : ℤ}
    (hW : 0 < W) (hw : ∀ i ∈ I, 0 ≤ w i)
    (hmass : ∑ i ∈ I, w i = W) (hmean : ∑ i ∈ I, w i * x i = W * head)
    (hleft : ∃ i ∈ I, x i < M ∧ δ ≤ w i)
    (hright : ∃ i ∈ I, M ≤ x i ∧ δ ≤ w i) :
    (∑ i ∈ I, w i * integerTent M (x i)) + 2 * δ ≤ W * integerTent M head := by
  have hleft' : ∃ i ∈ I, x i < M ∧ (δ : ℚ) ≤ w i := by
    obtain ⟨i, hi, hx, hδ⟩ := hleft
    exact ⟨i, hi, hx, by exact_mod_cast hδ⟩
  have hright' : ∃ i ∈ I, M ≤ x i ∧ (δ : ℚ) ≤ w i := by
    obtain ⟨i, hi, hx, hδ⟩ := hright
    exact ⟨i, hi, hx, by exact_mod_cast hδ⟩
  have hgap := integerTent_weighted_gap I (fun i => (w i : ℚ)) x
    (M := M) (head := head) (W := (W : ℚ)) (δ := (δ : ℚ))
    (by exact_mod_cast hW) (fun i hi => by exact_mod_cast hw i hi)
    (by exact_mod_cast hmass) (by exact_mod_cast hmean) hleft' hright'
  exact_mod_cast hgap

theorem weighted_affine_digit_difference {ι : Type*} (I : Finset ι)
    (w x : ι → ℤ) {W head slope intercept : ℤ}
    (hmass : ∑ i ∈ I, w i = W) (hmean : ∑ i ∈ I, w i * x i = W * head) :
    W * (slope * head + intercept) -
      (∑ i ∈ I, w i * (slope * x i + intercept)) = 0 := by
  have hsum : (∑ i ∈ I, w i * (slope * x i + intercept)) =
      slope * (∑ i ∈ I, w i * x i) + intercept * (∑ i ∈ I, w i) := by
    calc
      _ = ∑ i ∈ I, (slope * (w i * x i) + intercept * w i) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by simp only [Finset.sum_add_distrib, Finset.mul_sum]
  rw [hsum, hmass, hmean]
  ring

theorem weighted_digit_difference_abs {ι : Type*} (I : Finset ι)
    (w digit : ι → ℤ) {W D headDigit : ℤ}
    (hW : 0 ≤ W) (hw : ∀ i ∈ I, 0 ≤ w i) (hmass : ∑ i ∈ I, w i = W)
    (hhead : 0 ≤ headDigit ∧ headDigit ≤ D)
    (hdigit : ∀ i ∈ I, 0 ≤ digit i ∧ digit i ≤ D) :
    |W * headDigit - ∑ i ∈ I, w i * digit i| ≤ W * D := by
  have hsum0 : 0 ≤ ∑ i ∈ I, w i * digit i :=
    Finset.sum_nonneg (fun i hi => mul_nonneg (hw i hi) (hdigit i hi).1)
  have hsumUpper : (∑ i ∈ I, w i * digit i) ≤ W * D := by
    calc
      _ ≤ ∑ i ∈ I, w i * D := Finset.sum_le_sum
        (fun i hi => mul_le_mul_of_nonneg_left (hdigit i hi).2 (hw i hi))
      _ = W * D := by rw [← Finset.sum_mul, hmass]
  have hhead0 := mul_nonneg hW hhead.1
  have hheadUpper := mul_le_mul_of_nonneg_left hhead.2 hW
  rw [abs_le]
  constructor <;> linarith

theorem weighted_tent_digit_lower {ι : Type*} [DecidableEq ι] (I : Finset ι)
    (w x bit : ι → ℤ) {M head W δ amplification headBit : ℤ}
    (hW : 0 < W) (hamplification : 0 ≤ amplification)
    (hw : ∀ i ∈ I, 0 ≤ w i) (hmass : ∑ i ∈ I, w i = W)
    (hmean : ∑ i ∈ I, w i * x i = W * head)
    (hleft : ∃ i ∈ I, x i < M ∧ δ ≤ w i)
    (hright : ∃ i ∈ I, M ≤ x i ∧ δ ≤ w i)
    (hbit : ∀ i ∈ I, bit i ≤ 1) (hheadBit : 0 ≤ headBit)
    (hscale : 2 * W ≤ amplification * δ) :
    2 * W ≤ W * (amplification * integerTent M head + headBit) -
      ∑ i ∈ I, w i * (amplification * integerTent M (x i) + bit i) := by
  have hgap := integerTent_weighted_gap_int I w x hW hw hmass hmean hleft hright
  have hgapScaled := mul_le_mul_of_nonneg_left hgap hamplification
  have hbits : (∑ i ∈ I, w i * bit i) ≤ W := by
    calc
      _ ≤ ∑ i ∈ I, w i * 1 := Finset.sum_le_sum
        (fun i hi => mul_le_mul_of_nonneg_left (hbit i hi) (hw i hi))
      _ = W := by simp only [mul_one, hmass]
  have hsum : (∑ i ∈ I, w i * (amplification * integerTent M (x i) + bit i)) =
      amplification * (∑ i ∈ I, w i * integerTent M (x i)) + ∑ i ∈ I, w i * bit i := by
    calc
      _ = ∑ i ∈ I, (amplification * (w i * integerTent M (x i)) + w i * bit i) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by rw [Finset.sum_add_distrib, Finset.mul_sum]
  rw [hsum]
  nlinarith [mul_nonneg hW.le hheadBit]

end Erdos790.Upper
