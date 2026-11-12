import Erdos790.Upper.RadixSeparation
import Mathlib.Algebra.BigOperators.Fin

/-!
# Leading-digit bounds with finite coordinate indices
-/

namespace Erdos790.Upper

def extendFiniteDigit {size : ℕ} (digit : Fin size → ℤ) (n : ℕ) : ℤ :=
  if hn : n < size then digit ⟨n, hn⟩ else 0

theorem sum_finite_digits {size : ℕ} (digit : Fin size → ℤ) (q : ℤ) :
    (∑ h : Fin size, digit h * q ^ h.val) =
      ∑ n ∈ Finset.range size, extendFiniteDigit digit n * q ^ n := by
  calc
    _ = ∑ h : Fin size, extendFiniteDigit digit h.val * q ^ h.val := by
      apply Finset.sum_congr rfl
      intro h _
      simp only [extendFiniteDigit, dif_pos h.isLt]
    _ = _ := (Finset.sum_range (n := size) (fun n => extendFiniteDigit digit n * q ^ n)).symm

theorem finite_radix_gap {size : ℕ} {q W : ℤ} (digit : Fin size → ℤ) (H : Fin size)
    (hq : 2 ≤ q) (hW : 0 < W)
    (hlower : 2 * W ≤ digit H) (hupper : digit H ≤ W * (q - 1))
    (hlow : ∀ h : Fin size, h < H → |digit h| ≤ W * (q - 1))
    (hhigh : ∀ h : Fin size, H < h → digit h = 0) :
    W * q ^ H.val ≤ ∑ h : Fin size, digit h * q ^ h.val ∧
      (∑ h : Fin size, digit h * q ^ h.val) < W * q ^ (H.val + 1) := by
  let extended := extendFiniteDigit digit
  have hsum : (∑ h : Fin size, digit h * q ^ h.val) =
      ∑ n ∈ Finset.range size, extended n * q ^ n := by
    exact sum_finite_digits digit q
  have hlower' : 2 * W ≤ extended H.val := by simpa [extended, extendFiniteDigit] using hlower
  have hupper' : extended H.val ≤ W * (q - 1) := by simpa [extended, extendFiniteDigit] using hupper
  have hlow' : ∀ n < H.val, |extended n| ≤ W * (q - 1) := by
    intro n hn
    have hnsize : n < size := hn.trans H.isLt
    simpa only [extended, extendFiniteDigit, dif_pos hnsize] using hlow ⟨n, hnsize⟩ hn
  have hhigh' : ∀ n, H.val < n → n < size → extended n = 0 := by
    intro n hn hnsize
    simpa only [extended, extendFiniteDigit, dif_pos hnsize] using hhigh ⟨n, hnsize⟩ hn
  rw [hsum]
  exact radix_gap_of_higher_zero extended hq hW H.isLt hlower' hupper' hlow' hhigh'

end Erdos790.Upper
