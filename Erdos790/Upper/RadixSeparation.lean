import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# A positive radix digit dominates every lower digit
-/

namespace Erdos790.Upper

theorem radix_gap {q W : ℤ} {H : ℕ} (d : ℕ → ℤ)
    (hq : 2 ≤ q) (hW : 0 < W)
    (hlower : 2 * W ≤ d H) (hupper : d H ≤ W * (q - 1))
    (hlow : ∀ h < H, |d h| ≤ W * (q - 1)) :
    W * q ^ H ≤ ∑ h ∈ Finset.range (H + 1), d h * q ^ h ∧
      (∑ h ∈ Finset.range (H + 1), d h * q ^ h) < W * q ^ (H + 1) := by
  have hq0 : 0 ≤ q := by omega
  have htail : |∑ h ∈ Finset.range H, d h * q ^ h| ≤ W * (q ^ H - 1) := by
    calc
      |∑ h ∈ Finset.range H, d h * q ^ h| ≤
          ∑ h ∈ Finset.range H, |d h * q ^ h| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ h ∈ Finset.range H, |d h| * q ^ h := by
        apply Finset.sum_congr rfl
        intro h _
        rw [abs_mul, abs_of_nonneg (pow_nonneg hq0 h)]
      _ ≤ ∑ h ∈ Finset.range H, (W * (q - 1)) * q ^ h := by
        apply Finset.sum_le_sum
        intro h hh
        exact mul_le_mul_of_nonneg_right (hlow h (Finset.mem_range.mp hh)) (pow_nonneg hq0 h)
      _ = (W * (q - 1)) * (∑ h ∈ Finset.range H, q ^ h) :=
        (Finset.mul_sum _ _ _).symm
      _ = W * ((∑ h ∈ Finset.range H, q ^ h) * (q - 1)) := by ring
      _ = W * (q ^ H - 1) := by rw [geom_sum_mul]
  obtain ⟨htailLower, htailUpper⟩ := abs_le.mp htail
  have hleadLower := mul_le_mul_of_nonneg_right hlower (pow_nonneg hq0 H)
  have hleadUpper := mul_le_mul_of_nonneg_right hupper (pow_nonneg hq0 H)
  simp only [Finset.sum_range_succ, pow_succ]
  constructor <;> nlinarith

theorem radix_gap_of_higher_zero {q W : ℤ} {H size : ℕ} (d : ℕ → ℤ)
    (hq : 2 ≤ q) (hW : 0 < W) (hH : H < size)
    (hlower : 2 * W ≤ d H) (hupper : d H ≤ W * (q - 1))
    (hlow : ∀ h < H, |d h| ≤ W * (q - 1))
    (hhigh : ∀ h, H < h → h < size → d h = 0) :
    W * q ^ H ≤ ∑ h ∈ Finset.range size, d h * q ^ h ∧
      (∑ h ∈ Finset.range size, d h * q ^ h) < W * q ^ (H + 1) := by
  have hsum : (∑ h ∈ Finset.range size, d h * q ^ h) =
      ∑ h ∈ Finset.range (H + 1), d h * q ^ h := by
    symm
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro h hh hnot
    have hhsize := Finset.mem_range.mp hh
    have hhH : H < h := by simpa using hnot
    rw [hhigh h hhH hhsize, zero_mul]
  rw [hsum]
  exact radix_gap d hq hW hlower hupper hlow

end Erdos790.Upper
