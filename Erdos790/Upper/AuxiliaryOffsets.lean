import Erdos790.Upper.AuxiliaryParameters
import Erdos790.Upper.PhaseSelection

/-!
# Instantiating the auxiliary offsets at the stated parameters
-/

namespace Erdos790.Upper.AuxiliaryParameters

def blockCount (d : ℕ) : ℕ := 2 ^ (6 * d ^ 2 - 2)

theorem baseRange_eq_four_blocks {d : ℕ} (hd : 0 < d) :
    baseRange d = 4 * (blockCount d * factorialModulus d) := by
  have hexp : 2 ≤ 6 * d ^ 2 := by nlinarith
  have hsum : 6 * d ^ 2 - 2 + 2 = 6 * d ^ 2 := Nat.sub_add_cancel hexp
  unfold baseRange blockCount
  rw [← hsum, pow_add]
  norm_num
  ring

theorem sampleExponent_pos (d : ℕ) : 0 < sampleExponent d := by
  have hS : (1 : ℝ) ≤ testCount d := by exact_mod_cast testCount_pos d
  have hlog : 0 ≤ Real.log (testCount d : ℝ) := Real.log_nonneg hS
  have hceil : 100 * (1 + Real.log (testCount d : ℝ)) ≤ (sampleExponent d : ℝ) :=
    Nat.le_ceil _
  have hreal : (0 : ℝ) < sampleExponent d := by linarith
  exact_mod_cast hreal

theorem auxiliary_offsets_exist {d : ℕ} (hd : 0 < d) (translations : Finset ℕ)
    (htranslations : translations.card ≤ 2 ^ (3 * d)) :
    ∃ offset : Fin (sampleSize d) → ℕ,
      (∀ i, offset i < blockCount d * factorialModulus d ∧
        Nat.Coprime (offset i) (factorialModulus d)) ∧
      Function.Injective (fun i => offset i % factorialModulus d) ∧
      ∀ (M : ℕ) [NeZero M], baseRange d ≤ M → M < 2 * baseRange d →
        Nat.Coprime M (factorialModulus d) →
        ∀ z ∈ translations, ∀ a : ZMod M, a ≠ 0 →
          (Finset.univ.filter (fun i : Fin (sampleSize d) =>
            ‖1 - ZMod.stdAddChar (-((baseRange d + offset i + z : ℕ) : ZMod M) * a)‖ <
              4 / (roughScale d ^ 2 : ℕ))).card < sampleExponent d := by
  apply phase_separated_offsets translations (by unfold blockCount; positivity)
    (by have h := roughScale_large d; omega) (levelCount_pos d) rfl
    (baseRange_eq_four_blocks hd)
    (by unfold roughScale; omega) (collision_budget d)
  have hcount : 4 * baseRange d ^ 2 * translations.card ≤ testCount d :=
    Nat.mul_le_mul_left _ htranslations
  exact (mul_le_mul_of_nonneg_right (by exact_mod_cast hcount)
    (Real.exp_pos _).le).trans (test_budget d)

end Erdos790.Upper.AuxiliaryParameters
