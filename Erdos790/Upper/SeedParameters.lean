import Erdos790.Upper.SeedBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Uniform seed budgets for the prescribed quarter-decay density
-/

namespace Erdos790.Upper

noncomputable def clusterDensity (s : ℕ) : ℝ := (2 : ℝ) ^ (-(s : ℝ) / 4 - 4)

theorem clusterDensity_pos (s : ℕ) : 0 < clusterDensity s :=
  Real.rpow_pos_of_pos (by norm_num) _

theorem clusterDensity_le_one (s : ℕ) : clusterDensity s ≤ 1 := by
  unfold clusterDensity
  exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
    (by have := Nat.cast_nonneg (α := ℝ) s; linarith)

theorem clusterDensity_square_power (s k : ℕ) :
    clusterDensity s ^ 2 * (2 : ℝ) ^ k = (2 : ℝ) ^ ((k : ℝ) - (s : ℝ) / 2 - 8) := by
  unfold clusterDensity
  rw [← Real.rpow_mul_natCast (by norm_num), ← Real.rpow_natCast (2 : ℝ) k,
    ← Real.rpow_add (by norm_num)]
  congr 1
  push_cast
  ring

theorem cluster_seed_delay_budget (s : ℕ) :
    100 ≤ clusterDensity s ^ 2 * (2 : ℝ) ^ (s + 16) := by
  rw [clusterDensity_square_power]
  have hexponent : (8 : ℝ) ≤ ((s + 16 : ℕ) : ℝ) - (s : ℝ) / 2 - 8 := by
    push_cast
    have := Nat.cast_nonneg (α := ℝ) s
    linarith
  calc
    (100 : ℝ) ≤ (2 : ℝ) ^ (8 : ℕ) := by norm_num
    _ = (2 : ℝ) ^ (8 : ℝ) := (Real.rpow_natCast _ _).symm
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) hexponent

theorem cluster_seed_lattice_room {s d M : ℕ} (hd : 16 ≤ d) (hs : 6 * s ≤ d)
    (hM : 2 ^ d ≤ M) : 64 ≤ clusterDensity s ^ 2 * M := by
  have hprod : clusterDensity s ^ 2 * (2 : ℝ) ^ d ≤ clusterDensity s ^ 2 * M :=
    mul_le_mul_of_nonneg_left (by exact_mod_cast hM) (sq_nonneg _)
  rw [clusterDensity_square_power] at hprod
  have hds : (16 : ℝ) ≤ d := by exact_mod_cast hd
  have hss : 6 * (s : ℝ) ≤ d := by exact_mod_cast hs
  have hexponent : (6 : ℝ) ≤ (d : ℝ) - (s : ℝ) / 2 - 8 := by linarith
  calc
    (64 : ℝ) = (2 : ℝ) ^ (6 : ℕ) := by norm_num
    _ = (2 : ℝ) ^ (6 : ℝ) := (Real.rpow_natCast _ _).symm
    _ ≤ (2 : ℝ) ^ ((d : ℝ) - (s : ℝ) / 2 - 8) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hexponent
    _ ≤ _ := hprod

theorem clusterDensity_fourth_power (s k : ℕ) :
    clusterDensity s ^ 4 * (2 : ℝ) ^ k = (2 : ℝ) ^ ((k : ℝ) - (s : ℝ) - 16) := by
  unfold clusterDensity
  rw [← Real.rpow_mul_natCast (by norm_num), ← Real.rpow_natCast (2 : ℝ) k,
    ← Real.rpow_add (by norm_num)]
  congr 1
  push_cast
  ring

theorem cluster_refinement_delay_budget (s : ℕ) :
    512 ≤ clusterDensity s ^ 4 * (2 : ℝ) ^ (s + 28) := by
  rw [clusterDensity_fourth_power]
  have heq : ((s + 28 : ℕ) : ℝ) - (s : ℝ) - 16 = 12 := by push_cast; ring
  rw [heq]
  norm_num

theorem cluster_refinement_lattice_room {s d M : ℕ} (hd : 48 ≤ d) (hs : 6 * s ≤ d)
    (hM : 2 ^ d ≤ M) : 1024 ≤ clusterDensity s ^ 4 * M := by
  have hprod : clusterDensity s ^ 4 * (2 : ℝ) ^ d ≤ clusterDensity s ^ 4 * M :=
    mul_le_mul_of_nonneg_left (by exact_mod_cast hM) (by positivity)
  rw [clusterDensity_fourth_power] at hprod
  have hds : (48 : ℝ) ≤ d := by exact_mod_cast hd
  have hss : 6 * (s : ℝ) ≤ d := by exact_mod_cast hs
  have hexponent : (10 : ℝ) ≤ (d : ℝ) - (s : ℝ) - 16 := by linarith
  calc
    (1024 : ℝ) = (2 : ℝ) ^ (10 : ℕ) := by norm_num
    _ = (2 : ℝ) ^ (10 : ℝ) := (Real.rpow_natCast _ _).symm
    _ ≤ (2 : ℝ) ^ ((d : ℝ) - (s : ℝ) - 16) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hexponent
    _ ≤ _ := hprod

theorem cluster_refinement_capacity {s g : ℕ} (hg : clusterDensity s * g ≤ 2) :
    g < 2 ^ (s + 28) := by
  have hbudget : 100 ≤ clusterDensity s ^ 2 * (2 : ℝ) ^ (s + 28) :=
    (cluster_seed_delay_budget s).trans
      (mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega : s + 16 ≤ s + 28))
        (sq_nonneg _))
  simpa only [add_zero] using
    seed_power_room (g := g) (K := 0) (clusterDensity_pos s) (clusterDensity_le_one s)
      hg (by norm_num) hbudget

end Erdos790.Upper
