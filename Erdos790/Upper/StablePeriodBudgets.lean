import Erdos790.Upper.SeedParameters

/-!
# Component sizes and the error term during a stable lattice period
-/

namespace Erdos790.Upper

theorem stable_period_error_budget {k m N : ℕ} (hm : 2 * k ≤ m) (hN : 2 * k ≤ N) :
    k * (N / m + 1) ≤ N := by
  have hdiv := Nat.div_mul_le_self N m
  have hmul := Nat.mul_le_mul_right (N / m) hm
  nlinarith

def stableComponentLength (d s width : ℕ) : ℕ := 2 ^ (d - s - width - 24)

theorem stable_component_exponent_bound {d s width : ℕ}
    (hd : 48 ≤ d) (hs : 6 * s ≤ d) (hwidth : 12 * width ≤ d) :
    2 * width ≤ d - s - width - 24 := by omega

theorem stable_component_lower {d s width : ℕ}
    (hd : 48 ≤ d) (hs : 6 * s ≤ d) (hwidth : 12 * width ≤ d) :
    2 * width ≤ stableComponentLength d s width := by
  have hpower : d - s - width - 24 ≤ 2 ^ (d - s - width - 24) :=
    Nat.le_of_lt Nat.lt_two_pow_self
  exact (stable_component_exponent_bound hd hs hwidth).trans hpower

theorem stable_component_at_least_two {d s width : ℕ}
    (hd : 48 ≤ d) (hs : 6 * s ≤ d) (hwidth : 12 * width ≤ d) (hpos : 0 < width) :
    2 ≤ stableComponentLength d s width := by
  have h := stable_component_lower hd hs hwidth
  omega

theorem stable_component_scaled {d s width : ℕ}
    (hd : 48 ≤ d) (hs : 6 * s ≤ d) (hwidth : 12 * width ≤ d) :
    stableComponentLength d s width * 2 ^ width = 2 ^ (d - s - 24) := by
  unfold stableComponentLength
  rw [← pow_add]
  congr 1
  have := stable_component_exponent_bound hd hs hwidth
  omega

theorem cluster_core_length_lower {d s M N : ℕ}
    (hd : s + 24 ≤ d) (hM : 2 ^ d ≤ M)
    (hcore : clusterDensity s ^ 4 * M / 64 ≤ (N : ℝ)) :
    2 ^ (d - s - 24) ≤ N := by
  have hcast : (d : ℝ) = (d - s - 24 : ℕ) + (s : ℝ) + 24 := by
    exact_mod_cast (show d = (d - s - 24) + s + 24 by omega)
  have hpower : 64 * (2 : ℝ) ^ (d - s - 24) ≤
      (2 : ℝ) ^ ((d : ℝ) - (s : ℝ) - 16) := by
    calc
      64 * (2 : ℝ) ^ (d - s - 24) =
          (2 : ℝ) ^ (((d - s - 24 : ℕ) : ℝ) + 6) := by
            rw [Real.rpow_add (by norm_num), Real.rpow_natCast]
            norm_num
            ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hmult : clusterDensity s ^ 4 * (2 : ℝ) ^ d ≤ clusterDensity s ^ 4 * M :=
    mul_le_mul_of_nonneg_left (by exact_mod_cast hM) (by positivity)
  rw [clusterDensity_fourth_power] at hmult
  have hreal : (2 : ℝ) ^ (d - s - 24) ≤ N := by linarith
  exact_mod_cast hreal

theorem stable_component_budget {d s width M N k ambient : ℕ}
    (hd : 48 ≤ d) (hs : 6 * s ≤ d) (hwidth : 12 * width ≤ d)
    (hpos : 0 < width) (hM : 2 ^ d ≤ M)
    (hcore : clusterDensity s ^ 4 * M / 64 ≤ (N : ℝ))
    (hk : k ≤ width) (hambient : N ≤ ambient) :
    2 ≤ stableComponentLength d s width ∧
      stableComponentLength d s width * 2 ^ k ≤ N ∧
      k * (ambient / stableComponentLength d s width + 1) ≤ ambient := by
  have hlength : 2 ^ (d - s - 24) ≤ N :=
    cluster_core_length_lower (by have := stable_component_exponent_bound hd hs hwidth; omega)
      hM hcore
  have hroom : stableComponentLength d s width * 2 ^ k ≤ N := by
    calc
      _ ≤ stableComponentLength d s width * 2 ^ width :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) hk)
      _ = 2 ^ (d - s - 24) := stable_component_scaled hd hs hwidth
      _ ≤ N := hlength
  have hm := stable_component_lower hd hs hwidth
  have htwoK : 2 * k ≤ stableComponentLength d s width := by omega
  have hN : stableComponentLength d s width ≤ N := by
    exact (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos k)).trans hroom
  exact ⟨stable_component_at_least_two hd hs hwidth hpos, hroom,
    stable_period_error_budget htwoK (htwoK.trans (hN.trans hambient))⟩

end Erdos790.Upper
