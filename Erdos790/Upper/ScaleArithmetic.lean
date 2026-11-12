import Erdos790.Upper.ClusterArithmetic

/-!
# Converting the assigned digit into residual and arity bounds
-/

namespace Erdos790.Upper

theorem dyadic_amplification_weight_bound {base start j delay : ℕ}
    (hbase : base ≤ start) (hstart : start ≤ j) (hj : j < start + delay) :
    2 * (2 : ℕ) ^ (j - base) ≤ 2 ^ (delay + 3) * 2 ^ (start - base) := by
  calc
    2 * (2 : ℕ) ^ (j - base) = 2 ^ (j - base + 1) := by rw [pow_succ']
    _ ≤ 2 ^ (delay + 3 + (start - base)) := Nat.pow_le_pow_right (by decide) (by omega)
    _ = 2 ^ (delay + 3) * 2 ^ (start - base) := pow_add _ _ _

theorem radix_dyadic_identity (Q width gap digit : ℕ) :
    Q * 2 ^ gap * (2 ^ width) ^ digit = Q * 2 ^ (gap + width * digit) := by
  rw [← pow_mul, Nat.mul_assoc, ← pow_add]

theorem assigned_residual_scale_bounds {Q d width gap digit : ℕ}
    (hlower : d * width + 2 * width ≤ gap + width * digit)
    (hupper : gap + width * digit < d * width + 4 * width) :
    (2 ^ width) ^ 2 * (Q * (2 ^ width) ^ d) ≤ Q * 2 ^ gap * (2 ^ width) ^ digit ∧
      Q * 2 ^ gap * (2 ^ width) ^ (digit + 1) ≤
        (2 ^ width) ^ 5 * (Q * (2 ^ width) ^ d) := by
  have htwo : (2 ^ width) ^ 2 * (Q * (2 ^ width) ^ d) = Q * 2 ^ (d * width + 2 * width) := by
    calc
      _ = Q * ((2 ^ width) ^ d * (2 ^ width) ^ 2) := by ring
      _ = Q * (2 ^ width) ^ (d + 2) := by rw [pow_add]
      _ = Q * 2 ^ (d * width + 2 * width) := by rw [← pow_mul]; congr 2; ring
  have hfive : (2 ^ width) ^ 5 * (Q * (2 ^ width) ^ d) = Q * 2 ^ (d * width + 5 * width) := by
    calc
      _ = Q * ((2 ^ width) ^ d * (2 ^ width) ^ 5) := by ring
      _ = Q * (2 ^ width) ^ (d + 5) := by rw [pow_add]
      _ = Q * 2 ^ (d * width + 5 * width) := by rw [← pow_mul]; congr 2; ring
  rw [htwo, hfive, radix_dyadic_identity, radix_dyadic_identity]
  constructor
  · exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) hlower)
  · exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) (by nlinarith))

theorem dyadic_arity_budget {width delay : ℕ} (hw : 0 < width) (hdelay : delay ≤ 5 * width) :
    2 ^ delay + (2 ^ width) ^ 5 ≤ (2 ^ width) ^ 6 := by
  have hq : 2 ≤ 2 ^ width := by
    calc
      2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ width := Nat.pow_le_pow_right (by decide) hw
  have hnear : 2 ^ delay ≤ (2 ^ width) ^ 5 := by
    rw [← pow_mul]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  calc
    2 ^ delay + (2 ^ width) ^ 5 ≤ 2 * (2 ^ width) ^ 5 := by omega
    _ ≤ (2 ^ width) * (2 ^ width) ^ 5 := Nat.mul_le_mul_right _ hq
    _ = (2 ^ width) ^ 6 := (pow_succ' (2 ^ width) 5).symm

theorem assigned_bit_scale_bounds {Q d width gap digit : ℕ}
    (hlower : d * width + 2 * width ≤ gap + width * digit)
    (hupper : gap + width * digit < d * width + 4 * width) :
    (2 ^ width) ^ 2 * (Q * (2 ^ width) ^ d) ≤ Q * 2 ^ gap * (2 ^ width) ^ digit ∧
      Q * 2 ^ gap * (2 ^ width) ^ digit ≤
        (2 ^ width) ^ 4 * (Q * (2 ^ width) ^ d) := by
  refine ⟨(assigned_residual_scale_bounds hlower hupper).1, ?_⟩
  have hfour : (2 ^ width) ^ 4 * (Q * (2 ^ width) ^ d) =
      Q * 2 ^ (d * width + 4 * width) := by
    calc
      _ = Q * ((2 ^ width) ^ d * (2 ^ width) ^ 4) := by ring
      _ = Q * (2 ^ width) ^ (d + 4) := by rw [pow_add]
      _ = Q * 2 ^ (d * width + 4 * width) := by rw [← pow_mul]; congr 2; ring
  rw [hfour, radix_dyadic_identity]
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) hupper.le)

end Erdos790.Upper
