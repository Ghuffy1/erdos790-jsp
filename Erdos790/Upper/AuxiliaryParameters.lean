import Erdos790.Upper.SamplingBudget

/-!
# Explicit sample parameters

These bounds ensure that one finite sample works for every character and
every deterministic translation used in the base construction.
-/

namespace Erdos790.Upper

theorem log_factorial_square_le {v : ℕ} (hv : 1 ≤ v) :
    Real.log ((v ^ 2).factorial : ℝ) ≤ 2 * (v : ℝ) ^ 3 := by
  have hv0 : (0 : ℝ) < v := by exact_mod_cast (show 0 < v by omega)
  have hfact : (0 : ℝ) < (v ^ 2).factorial := by positivity
  have hbound : ((v ^ 2).factorial : ℝ) ≤ ((v : ℝ) ^ 2) ^ (v ^ 2) := by
    exact_mod_cast Nat.factorial_le_pow (v ^ 2)
  have hlog := Real.log_le_log hfact hbound
  rw [Real.log_pow, Real.log_pow, Nat.cast_pow] at hlog
  norm_num at hlog
  have hlogv : Real.log (v : ℝ) ≤ v := by
    have h := Real.log_le_sub_one_of_pos hv0
    linarith
  have hmul := mul_le_mul_of_nonneg_left hlogv (sq_nonneg (v : ℝ))
  nlinarith

namespace AuxiliaryParameters

def levelCount (d : ℕ) : ℕ := 6 * d ^ 2 + 1
def roughScale (d : ℕ) : ℕ := 100000 * levelCount d
def factorialModulus (d : ℕ) : ℕ := (roughScale d ^ 2).factorial
def baseRange (d : ℕ) : ℕ := factorialModulus d * 2 ^ (6 * d ^ 2)
def testCount (d : ℕ) : ℕ := 4 * baseRange d ^ 2 * 2 ^ (3 * d)
noncomputable def sampleExponent (d : ℕ) : ℕ := phaseSampleExponent (testCount d)
noncomputable def sampleSize (d : ℕ) : ℕ := 2 * levelCount d * sampleExponent d

theorem levelCount_pos (d : ℕ) : 0 < levelCount d := by unfold levelCount; omega
theorem roughScale_large (d : ℕ) : 100000 ≤ roughScale d := by
  unfold roughScale
  exact Nat.le_mul_of_pos_right _ (levelCount_pos d)
theorem factorialModulus_pos (d : ℕ) : 0 < factorialModulus d := Nat.factorial_pos _
theorem baseRange_pos (d : ℕ) : 0 < baseRange d := by
  unfold baseRange
  exact Nat.mul_pos (factorialModulus_pos d) (by positivity)
theorem testCount_pos (d : ℕ) : 0 < testCount d := by
  unfold testCount
  have h := baseRange_pos d
  positivity

theorem log_baseRange_le (d : ℕ) :
    Real.log (baseRange d : ℝ) ≤ 2 * (roughScale d : ℝ) ^ 3 + roughScale d := by
  have hv := roughScale_large d
  have hlogQ := log_factorial_square_le (v := roughScale d) (by omega)
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have hd : 6 * d ^ 2 ≤ roughScale d := by
    have hL := levelCount_pos d
    unfold roughScale levelCount
    omega
  have hdreal : 6 * (d : ℝ) ^ 2 ≤ roughScale d := by exact_mod_cast hd
  have hprod := mul_le_mul_of_nonneg_left hlog2 (show (0 : ℝ) ≤ 6 * d ^ 2 by positivity)
  have hQpos : (0 : ℝ) < factorialModulus d := by exact_mod_cast factorialModulus_pos d
  have hpowpos : (0 : ℝ) < 2 ^ (6 * d ^ 2) := by positivity
  unfold baseRange
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [Real.log_mul hQpos.ne' hpowpos.ne', Real.log_pow]
  push_cast
  change Real.log ((roughScale d ^ 2).factorial : ℝ) + _ ≤ _
  have hprod' : 6 * (d : ℝ) ^ 2 * Real.log 2 ≤ 6 * (d : ℝ) ^ 2 := by
    simpa using hprod
  exact add_le_add hlogQ (hprod'.trans hdreal)

theorem log_testCount_le (d : ℕ) :
    Real.log (testCount d : ℝ) ≤ 5 * (roughScale d : ℝ) ^ 3 := by
  have hv : (100000 : ℝ) ≤ roughScale d := by exact_mod_cast roughScale_large d
  have hdNat : 3 * d ≤ roughScale d := by
    have hd2 : d ≤ d ^ 2 := by nlinarith
    unfold roughScale levelCount
    omega
  have hd : 3 * (d : ℝ) ≤ roughScale d := by exact_mod_cast hdNat
  have hlogX := log_baseRange_le d
  have hlog4 : Real.log 4 ≤ 3 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
    norm_num at h
    exact h
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have hprod := mul_le_mul_of_nonneg_left hlog2 (show (0 : ℝ) ≤ 3 * d by positivity)
  have hcubic : 3 + 3 * (roughScale d : ℝ) ≤ (roughScale d : ℝ) ^ 3 := by
    have h := mul_nonneg (show (0 : ℝ) ≤ roughScale d - 3 by linarith)
      (sq_nonneg (roughScale d : ℝ))
    nlinarith [sq_nonneg ((roughScale d : ℝ) - 2)]
  have hXpos : (0 : ℝ) < baseRange d := by exact_mod_cast baseRange_pos d
  have hleftpos : (0 : ℝ) < 4 * (baseRange d : ℝ) ^ 2 :=
    mul_pos (by norm_num) (pow_pos hXpos 2)
  have hpowpos : (0 : ℝ) < 2 ^ (3 * d) := by positivity
  unfold testCount
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [Real.log_mul hleftpos.ne' hpowpos.ne',
    Real.log_mul (by norm_num) (pow_pos hXpos 2).ne',
    Real.log_pow, Real.log_pow]
  push_cast
  nlinarith

theorem sampleExponent_le (d : ℕ) : sampleExponent d ≤ 600 * roughScale d ^ 3 := by
  apply phaseSampleExponent_le
  have h := log_testCount_le d
  have hv : (1 : ℝ) ≤ (roughScale d : ℝ) ^ 3 := by
    have hv0 : 1 ≤ roughScale d := (by omega : 1 ≤ 100000).trans (roughScale_large d)
    exact_mod_cast (one_le_pow₀ (by exact_mod_cast hv0 : (1 : ℝ) ≤ roughScale d) :
      (1 : ℝ) ≤ (roughScale d : ℝ) ^ 3)
  push_cast
  nlinarith

theorem sampleSize_le_fourth_power (d : ℕ) : sampleSize d ≤ roughScale d ^ 4 := by
  have hk := sampleExponent_le d
  have hL : 1200 * levelCount d ≤ roughScale d := by unfold roughScale; omega
  calc
    sampleSize d ≤ 2 * levelCount d * (600 * roughScale d ^ 3) :=
      Nat.mul_le_mul_left _ hk
    _ = (1200 * levelCount d) * roughScale d ^ 3 := by ring
    _ ≤ roughScale d * roughScale d ^ 3 := Nat.mul_le_mul_right _ hL
    _ = roughScale d ^ 4 := by ring

theorem collision_budget (d : ℕ) :
    4 * sampleSize d ^ 2 ≤ (factorialModulus d).totient := by
  apply factorial_residue_collision_budget (by have h := roughScale_large d; omega)
  exact (sampleSize_le_fourth_power d).trans
    (Nat.pow_le_pow_right (by have h := roughScale_large d; omega) (by omega : 4 ≤ 5))

theorem test_budget (d : ℕ) : (testCount d : ℝ) *
    Real.exp (-(sampleExponent d : ℝ) / 2) ≤ 1 / 2 := by
  exact phaseSampleExponent_budget
    (by exact_mod_cast testCount_pos d) (by positivity) le_rfl

end AuxiliaryParameters
end Erdos790.Upper
