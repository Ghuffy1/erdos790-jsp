import Erdos790.Upper.Recurrence
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Positivity

/-!
# Summability of the concrete cluster recurrence
-/

namespace Erdos790.Upper

theorem recurrence_summable_of_summable_forcing {f a : ℕ → ℝ}
    (hf : ∀ n, 0 ≤ f n) (ha : ∀ n, 0 ≤ a n) (hsum : Summable a)
    (hstep : ∀ n, f (n + 1) ≤ f n / 2 + a n) :
    Summable f ∧ ∑' n, f n ≤ 2 * (f 0 + ∑' n, a n) := by
  apply recurrence_summable hf hstep
  intro N
  exact Summable.sum_le_tsum (Finset.range N) (fun n _ => ha n) hsum

noncomputable def clusterForcing (C : ℝ) (n : ℕ) : ℝ :=
  (2 : ℝ) ^ (-(n : ℝ) / 4 - 4) / 2 +
    C * ((n + 1 : ℕ) : ℝ) ^ 2 * (1 / 2 : ℝ) ^ (n + 1)

theorem quarter_decay_norm_lt_one : ‖(2 : ℝ) ^ (-1 / 4 : ℝ)‖ < 1 := by
  have hpos : 0 < (2 : ℝ) ^ (-1 / 4 : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
  rw [Real.norm_eq_abs, abs_of_pos hpos]
  exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)

theorem quarter_decay_identity (n : ℕ) :
    (2 : ℝ) ^ (-(n : ℝ) / 4 - 4) / 2 =
      ((2 : ℝ) ^ (-1 / 4 : ℝ)) ^ n / 32 := by
  have hexponent : -(n : ℝ) / 4 - 4 = (-1 / 4 : ℝ) * n + (-4 : ℝ) := by ring
  rw [hexponent, Real.rpow_add (by norm_num), Real.rpow_mul_natCast (by norm_num)]
  norm_num [Real.rpow_neg, Real.rpow_natCast]
  ring

theorem clusterForcing_summable (C : ℝ) : Summable (clusterForcing C) := by
  have hgeom := summable_geometric_of_norm_lt_one quarter_decay_norm_lt_one
  have hpoly := summable_pow_mul_geometric_of_norm_lt_one 2
    (r := (1 / 2 : ℝ)) (by norm_num)
  have hshift := hpoly.comp_injective Nat.succ_injective
  have htotal := (hgeom.div_const 32).add (hshift.mul_left C)
  convert htotal using 1
  funext n
  simp only [clusterForcing, quarter_decay_identity, Function.comp_apply,
    Nat.succ_eq_add_one]
  ring

noncomputable def clusterSequence (C : ℝ) : ℕ → ℝ
  | 0 => 1
  | n + 1 => clusterSequence C n / 2 + clusterForcing C n

theorem clusterSequence_nonneg {C : ℝ} (hC : 0 ≤ C) : ∀ n, 0 ≤ clusterSequence C n := by
  intro n
  induction n with
  | zero => norm_num [clusterSequence]
  | succ n ih => dsimp [clusterSequence, clusterForcing]; positivity

theorem clusterSequence_summable {C : ℝ} (hC : 0 ≤ C) :
    Summable (clusterSequence C) ∧
      ∑' n, clusterSequence C n ≤ 2 * (1 + ∑' n, clusterForcing C n) := by
  apply recurrence_summable_of_summable_forcing (clusterSequence_nonneg hC)
    (fun n => by dsimp [clusterForcing]; positivity) (clusterForcing_summable C)
  intro n
  exact le_rfl

end Erdos790.Upper
