import Erdos790.Upper.WeightedDigits

/-!
# Cancellation of the affine part of a weighted radix host
-/

namespace Erdos790.Upper

theorem weighted_expansion_residual {ι κ : Type*} (I : Finset ι) (J : Finset κ)
    (exponent : κ → ℕ) (w x : ι → ℤ) (digit : ι → κ → ℤ) (headDigit : κ → ℤ)
    {W head constant step scale radix : ℤ}
    (hmass : ∑ i ∈ I, w i = W) (hmean : ∑ i ∈ I, w i * x i = W * head) :
    W * (constant + step * head + scale * ∑ h ∈ J, headDigit h * radix ^ exponent h) -
        (∑ i ∈ I, w i * (constant + step * x i +
          scale * ∑ h ∈ J, digit i h * radix ^ exponent h)) =
      scale * ∑ h ∈ J,
        (W * headDigit h - ∑ i ∈ I, w i * digit i h) * radix ^ exponent h := by
  have hfubini :
      (∑ i ∈ I, w i * ∑ h ∈ J, digit i h * radix ^ exponent h) =
        ∑ h ∈ J, (∑ i ∈ I, w i * digit i h) * radix ^ exponent h := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro h _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hweighted :
      (∑ i ∈ I, w i * (constant + step * x i +
        scale * ∑ h ∈ J, digit i h * radix ^ exponent h)) =
      constant * W + step * (W * head) +
        scale * ∑ h ∈ J, (∑ i ∈ I, w i * digit i h) * radix ^ exponent h := by
    calc
      _ = ∑ i ∈ I, (constant * w i + step * (w i * x i) +
          scale * (w i * ∑ h ∈ J, digit i h * radix ^ exponent h)) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = constant * (∑ i ∈ I, w i) + step * (∑ i ∈ I, w i * x i) +
          scale * (∑ i ∈ I, w i * ∑ h ∈ J, digit i h * radix ^ exponent h) := by
        simp only [Finset.sum_add_distrib, Finset.mul_sum]
      _ = _ := by rw [hmass, hmean, hfubini]
  have hdifference :
      (∑ h ∈ J, (W * headDigit h - ∑ i ∈ I, w i * digit i h) * radix ^ exponent h) =
      W * (∑ h ∈ J, headDigit h * radix ^ exponent h) -
        ∑ h ∈ J, (∑ i ∈ I, w i * digit i h) * radix ^ exponent h := by
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro h _
    ring
  rw [hweighted, hdifference]
  ring

theorem weighted_radix_residual {ι : Type*} (I : Finset ι) (size : ℕ)
    (w x : ι → ℤ) (digit : ι → ℕ → ℤ) (headDigit : ℕ → ℤ)
    {W head constant step scale radix : ℤ}
    (hmass : ∑ i ∈ I, w i = W) (hmean : ∑ i ∈ I, w i * x i = W * head) :
    W * (constant + step * head + scale * ∑ h ∈ Finset.range size, headDigit h * radix ^ h) -
        (∑ i ∈ I, w i * (constant + step * x i +
          scale * ∑ h ∈ Finset.range size, digit i h * radix ^ h)) =
      scale * ∑ h ∈ Finset.range size,
        (W * headDigit h - ∑ i ∈ I, w i * digit i h) * radix ^ h :=
  weighted_expansion_residual I (Finset.range size) id w x digit headDigit hmass hmean

end Erdos790.Upper
