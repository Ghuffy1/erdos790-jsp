import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic

/-!
# Quantitative concavity of the integer tents

The peak is between adjacent integers. A term from the opposite half therefore
contributes at least twice its weight to the concavity gap.
-/

open Finset

namespace Erdos790.Upper

def integerTent (M t : ℤ) : ℤ := min (2 * t + 1) (4 * M - 2 * t - 1)

theorem weighted_single_gap {ι : Type*} [DecidableEq ι] (I : Finset ι)
    (w f g : ι → ℚ) (d : ℚ) {k : ι} (hk : k ∈ I)
    (hw : ∀ i ∈ I, 0 ≤ w i) (hfg : ∀ i ∈ I, f i ≤ g i)
    (hgap : f k + d ≤ g k) :
    (∑ i ∈ I, w i * f i) + w k * d ≤ ∑ i ∈ I, w i * g i := by
  have hrest : (∑ i ∈ I.erase k, w i * f i) ≤
      ∑ i ∈ I.erase k, w i * g i := by
    apply Finset.sum_le_sum
    intro i hi
    exact mul_le_mul_of_nonneg_left (hfg i (Finset.mem_of_mem_erase hi))
      (hw i (Finset.mem_of_mem_erase hi))
  have hterm : w k * f k + w k * d ≤ w k * g k := by
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left hgap (hw k hk)
  have hf := Finset.sum_erase_add I (fun i => w i * f i) hk
  have hg := Finset.sum_erase_add I (fun i => w i * g i) hk
  linarith

theorem weighted_affine_sum {ι : Type*} (I : Finset ι) (w x : ι → ℚ)
    (slope intercept : ℚ) :
    (∑ i ∈ I, w i * (slope * x i + intercept)) =
      slope * (∑ i ∈ I, w i * x i) + intercept * (∑ i ∈ I, w i) := by
  calc
    (∑ i ∈ I, w i * (slope * x i + intercept)) =
        ∑ i ∈ I, (slope * (w i * x i) + intercept * w i) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by simp only [Finset.sum_add_distrib, Finset.mul_sum]

theorem integerTent_left_gap {ι : Type*} [DecidableEq ι] (I : Finset ι)
    (w : ι → ℚ) (x : ι → ℤ) {M h : ℤ} {k : ι} (hk : k ∈ I)
    (hw : ∀ i ∈ I, 0 ≤ w i) (hmass : ∑ i ∈ I, w i = 1)
    (hmean : ∑ i ∈ I, w i * (x i : ℚ) = h)
    (hhead : h < M) (hopposite : M ≤ x k) :
    (∑ i ∈ I, w i * (integerTent M (x i) : ℚ)) + 2 * w k ≤ integerTent M h := by
  have hhead_eq : integerTent M h = 2 * h + 1 := by
    apply min_eq_left
    omega
  have hupper : ∀ i ∈ I, (integerTent M (x i) : ℚ) ≤ 2 * (x i : ℚ) + 1 := by
    intro i _
    exact_mod_cast (min_le_left (2 * x i + 1) (4 * M - 2 * x i - 1))
  have hgap : (integerTent M (x k) : ℚ) + 2 ≤ 2 * (x k : ℚ) + 1 := by
    have hright := min_le_right (2 * x k + 1) (4 * M - 2 * x k - 1)
    have hgap_int : integerTent M (x k) + 2 ≤ 2 * x k + 1 := by
      unfold integerTent
      omega
    exact_mod_cast hgap_int
  have hweighted := weighted_single_gap I w (fun i => (integerTent M (x i) : ℚ))
    (fun i => 2 * (x i : ℚ) + 1) 2 hk hw hupper hgap
  have hlinear := weighted_affine_sum I w (fun i => (x i : ℚ)) 2 1
  rw [hmean, hmass] at hlinear
  rw [hhead_eq]
  push_cast
  linarith

theorem integerTent_right_gap {ι : Type*} [DecidableEq ι] (I : Finset ι)
    (w : ι → ℚ) (x : ι → ℤ) {M h : ℤ} {k : ι} (hk : k ∈ I)
    (hw : ∀ i ∈ I, 0 ≤ w i) (hmass : ∑ i ∈ I, w i = 1)
    (hmean : ∑ i ∈ I, w i * (x i : ℚ) = h)
    (hhead : M ≤ h) (hopposite : x k < M) :
    (∑ i ∈ I, w i * (integerTent M (x i) : ℚ)) + 2 * w k ≤ integerTent M h := by
  have hhead_eq : integerTent M h = 4 * M - 2 * h - 1 := by
    apply min_eq_right
    omega
  have hupper : ∀ i ∈ I, (integerTent M (x i) : ℚ) ≤
      -2 * (x i : ℚ) + (4 * (M : ℚ) - 1) := by
    intro i _
    have hi := min_le_right (2 * x i + 1) (4 * M - 2 * x i - 1)
    have hi' : (integerTent M (x i) : ℚ) ≤ 4 * (M : ℚ) - 2 * (x i : ℚ) - 1 := by
      exact_mod_cast hi
    linarith
  have hgap : (integerTent M (x k) : ℚ) + 2 ≤
      -2 * (x k : ℚ) + (4 * (M : ℚ) - 1) := by
    have hleft := min_le_left (2 * x k + 1) (4 * M - 2 * x k - 1)
    have hgap_int : integerTent M (x k) + 2 ≤ 4 * M - 2 * x k - 1 := by
      unfold integerTent
      omega
    have hgap_rat : (integerTent M (x k) : ℚ) + 2 ≤
        4 * (M : ℚ) - 2 * (x k : ℚ) - 1 := by exact_mod_cast hgap_int
    linarith
  have hweighted := weighted_single_gap I w (fun i => (integerTent M (x i) : ℚ))
    (fun i => -2 * (x i : ℚ) + (4 * (M : ℚ) - 1)) 2 hk hw hupper hgap
  have hlinear := weighted_affine_sum I w (fun i => (x i : ℚ)) (-2) (4 * (M : ℚ) - 1)
  rw [hmean, hmass] at hlinear
  rw [hhead_eq]
  push_cast
  linarith

theorem integerTent_mixed_gap {ι : Type*} [DecidableEq ι] (I : Finset ι)
    (w : ι → ℚ) (x : ι → ℤ) {M h : ℤ} {δ : ℚ}
    (hw : ∀ i ∈ I, 0 ≤ w i) (hmass : ∑ i ∈ I, w i = 1)
    (hmean : ∑ i ∈ I, w i * (x i : ℚ) = h)
    (hleft : ∃ k ∈ I, x k < M ∧ δ ≤ w k)
    (hright : ∃ k ∈ I, M ≤ x k ∧ δ ≤ w k) :
    (∑ i ∈ I, w i * (integerTent M (x i) : ℚ)) + 2 * δ ≤ integerTent M h := by
  by_cases hh : h < M
  · obtain ⟨k, hk, hx, hδ⟩ := hright
    have hgap := integerTent_left_gap I w x hk hw hmass hmean hh hx
    linarith
  · obtain ⟨k, hk, hx, hδ⟩ := hleft
    have hgap := integerTent_right_gap I w x hk hw hmass hmean (by omega) hx
    linarith

theorem tent_scale_gap (k : ℕ) : (2 : ℚ) ^ (k + 3) * (2 / 2 ^ k) = 16 := by
  rw [pow_add]
  field_simp
  ring

end Erdos790.Upper
