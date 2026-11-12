import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Numerical room for the mixed-mean seed
-/

namespace Erdos790.Upper

theorem seed_window_bounds {η M W g K B x c : ℝ}
    (hη : 0 < η) (hM : 0 ≤ M) (hW : η * M / 2 ≤ W) (hWM : W ≤ M)
    (hg0 : 0 ≤ g) (hB0 : 0 ≤ B)
    (hg : η * g ≤ 2) (hK : η * K ≤ 5) (hB : 100 ≤ η ^ 2 * B)
    (hxlow : W / 4 ≤ x) (hxhigh : x ≤ 3 * W / 4) (hc : |c| ≤ 2 * M) :
    K * W ≤ B * x - g * c ∧ B * x - g * c ≤ (B - g - K) * W := by
  have hW0 : 0 ≤ W := (by positivity : 0 ≤ η * M / 2).trans hW
  have hproduct1 := mul_le_mul_of_nonneg_right hW (mul_nonneg hη.le hB0)
  have hproduct2 := mul_le_mul_of_nonneg_right hB hM
  have hlarge : 50 * M ≤ η * B * W := by nlinarith
  have hgW := mul_le_mul_of_nonneg_right hg hW0
  have hKW := mul_le_mul_of_nonneg_right hK hW0
  have hgM := mul_le_mul_of_nonneg_right hg hM
  have hscaled : 0 ≤ η * (B * W / 4 - (K + g) * W - 2 * g * M) := by
    nlinarith
  have hroom : 0 ≤ B * W / 4 - (K + g) * W - 2 * g * M :=
    nonneg_of_mul_nonneg_right hscaled hη
  have hlower := mul_le_mul_of_nonneg_left hxlow hB0
  have hupper := mul_le_mul_of_nonneg_left hxhigh hB0
  have hcupper := mul_le_mul_of_nonneg_left ((le_abs_self c).trans hc) hg0
  have hclower := mul_le_mul_of_nonneg_left ((neg_le_abs c).trans hc) hg0
  have hgW0 := mul_nonneg hg0 hW0
  constructor <;> nlinarith

theorem seed_power_room {η : ℝ} {g K n : ℕ}
    (hη : 0 < η) (hηone : η ≤ 1) (hg : η * g ≤ 2) (hK : η * K ≤ 5)
    (hbudget : 100 ≤ η ^ 2 * (2 : ℝ) ^ n) : g + K < 2 ^ n := by
  have hηsquare : η ^ 2 ≤ η := by nlinarith
  have hscaled : 100 ≤ η * (2 : ℝ) ^ n :=
    hbudget.trans (mul_le_mul_of_nonneg_right hηsquare (by positivity))
  have hsum : η * ((g : ℝ) + K) ≤ 7 := by nlinarith
  have hlt : (g : ℝ) + K < (2 : ℝ) ^ n :=
    (mul_lt_mul_iff_of_pos_left hη).mp (lt_of_le_of_lt hsum (by linarith))
  exact_mod_cast hlt

end Erdos790.Upper
