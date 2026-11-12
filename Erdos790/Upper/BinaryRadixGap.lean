import Erdos790.Upper.RadixSeparation
import Erdos790.Upper.FiniteRadix

/-!
# A leading binary difference dominates its lower radix digits
-/

namespace Erdos790.Upper

theorem binary_radix_gap {q : ℤ} {H : ℕ} (digit : ℕ → ℤ)
    (hq : 3 ≤ q) (hlead : digit H = 1) (hlow : ∀ h < H, |digit h| ≤ 1) :
    q ^ H ≤ 2 * (∑ h ∈ Finset.range (H + 1), digit h * q ^ h) ∧
      (∑ h ∈ Finset.range (H + 1), digit h * q ^ h) < 2 * q ^ H := by
  have hq0 : 0 ≤ q := by omega
  have hsum0 : 0 ≤ ∑ h ∈ Finset.range H, q ^ h :=
    Finset.sum_nonneg (fun h _ => pow_nonneg hq0 h)
  have hgeometric : (∑ h ∈ Finset.range H, q ^ h) * (q - 1) = q ^ H - 1 := geom_sum_mul _ _
  have htwice : 2 * (∑ h ∈ Finset.range H, q ^ h) ≤ q ^ H - 1 := by
    have h := mul_le_mul_of_nonneg_left (show (2 : ℤ) ≤ q - 1 by omega) hsum0
    nlinarith
  have htail : |∑ h ∈ Finset.range H, digit h * q ^ h| ≤ ∑ h ∈ Finset.range H, q ^ h := by
    calc
      _ ≤ ∑ h ∈ Finset.range H, |digit h * q ^ h| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ h ∈ Finset.range H, q ^ h := by
        apply Finset.sum_le_sum
        intro h hh
        rw [abs_mul, abs_of_nonneg (pow_nonneg hq0 h)]
        simpa using mul_le_mul_of_nonneg_right (hlow h (Finset.mem_range.mp hh)) (pow_nonneg hq0 h)
  obtain ⟨hlower, hupper⟩ := abs_le.mp htail
  have hpower : 0 < q ^ H := pow_pos (by omega) _
  rw [Finset.sum_range_succ, hlead, one_mul]
  constructor <;> nlinarith

theorem binary_radix_gap_of_higher_zero {q : ℤ} {H size : ℕ} (digit : ℕ → ℤ)
    (hq : 3 ≤ q) (hH : H < size) (hlead : digit H = 1)
    (hlow : ∀ h < H, |digit h| ≤ 1)
    (hhigh : ∀ h, H < h → h < size → digit h = 0) :
    q ^ H ≤ 2 * (∑ h ∈ Finset.range size, digit h * q ^ h) ∧
      (∑ h ∈ Finset.range size, digit h * q ^ h) < 2 * q ^ H := by
  have hsum : (∑ h ∈ Finset.range size, digit h * q ^ h) =
      ∑ h ∈ Finset.range (H + 1), digit h * q ^ h := by
    symm
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro h hh hnot
    have hsize := Finset.mem_range.mp hh
    have hlarge : H < h := by simpa using hnot
    rw [hhigh h hlarge hsize, zero_mul]
  rw [hsum]
  exact binary_radix_gap digit hq hlead hlow

theorem finite_binary_radix_gap {size : ℕ} {q : ℤ} (digit : Fin size → ℤ) (H : Fin size)
    (hq : 3 ≤ q) (hlead : digit H = 1)
    (hlow : ∀ h : Fin size, h < H → |digit h| ≤ 1)
    (hhigh : ∀ h : Fin size, H < h → digit h = 0) :
    q ^ H.val ≤ 2 * (∑ h : Fin size, digit h * q ^ h.val) ∧
      (∑ h : Fin size, digit h * q ^ h.val) < 2 * q ^ H.val := by
  have hlead' : extendFiniteDigit digit H.val = 1 := by
    simpa only [extendFiniteDigit, dif_pos H.isLt] using hlead
  have hlow' : ∀ n < H.val, |extendFiniteDigit digit n| ≤ 1 := by
    intro n hn
    have hns : n < size := hn.trans H.isLt
    simpa only [extendFiniteDigit, dif_pos hns] using hlow ⟨n, hns⟩ hn
  have hhigh' : ∀ n, H.val < n → n < size → extendFiniteDigit digit n = 0 := by
    intro n hn hns
    simpa only [extendFiniteDigit, dif_pos hns] using hhigh ⟨n, hns⟩ hn
  rw [sum_finite_digits]
  exact binary_radix_gap_of_higher_zero (extendFiniteDigit digit) hq H.isLt hlead' hlow' hhigh'

end Erdos790.Upper
