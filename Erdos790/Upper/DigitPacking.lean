import Mathlib.Data.Finset.Card
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Density bounds for the modulus and residue length
-/

namespace Erdos790.Upper

theorem divisor_card_bound {D : Finset ℕ} {g W : ℕ}
    (hD : ∀ d ∈ D, d ≤ W) (hdiv : ∀ d ∈ D, g ∣ d) :
    g * (D.card - 1) ≤ W := by
  have hinj : Set.InjOn (fun d : ℕ => d / g) (D : Set ℕ) := by
    intro d hd e he hde
    change d / g = e / g at hde
    calc
      d = d / g * g := (Nat.div_mul_cancel (hdiv d hd)).symm
      _ = e / g * g := by rw [hde]
      _ = e := Nat.div_mul_cancel (hdiv e he)
  have hsubset : D.image (fun d => d / g) ⊆ Finset.range (W / g + 1) := by
    intro x hx
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hx
    have hddiv : d / g ≤ W / g := Nat.div_le_div_right (hD d hd)
    exact Finset.mem_range.mpr (by omega)
  have hcard : D.card ≤ W / g + 1 := by
    calc
      D.card = (D.image (fun d => d / g)).card := (Finset.card_image_iff.mpr hinj).symm
      _ ≤ (Finset.range (W / g + 1)).card := Finset.card_le_card hsubset
      _ = W / g + 1 := Finset.card_range _
  have hcardPred : D.card - 1 ≤ W / g := by
    simpa only [Nat.add_sub_cancel] using Nat.sub_le_sub_right hcard 1
  calc
    g * (D.card - 1) ≤ g * (W / g) := Nat.mul_le_mul_left g hcardPred
    _ = W / g * g := Nat.mul_comm _ _
    _ ≤ W := Nat.div_mul_le_self _ _

theorem density_divisor_bound {D : Finset ℕ} {g W M : ℕ} {η : ℝ}
    (hD : ∀ d ∈ D, d ≤ W) (hdiv : ∀ d ∈ D, g ∣ d)
    (hsize : 2 ≤ η * M) (hdensity : η * M ≤ D.card) (hWM : W ≤ M) :
    η * g ≤ 2 := by
  have hcard : 2 ≤ D.card := by exact_mod_cast hsize.trans hdensity
  have hpack : (g : ℝ) * ((D.card : ℝ) - 1) ≤ W := by
    have h := divisor_card_bound hD hdiv
    have hreal : (g : ℝ) * ((D.card - 1 : ℕ) : ℝ) ≤ W := by exact_mod_cast h
    simpa only [Nat.cast_sub (by omega : 1 ≤ D.card), Nat.cast_one] using hreal
  have hhalf : η * M / 2 ≤ (D.card : ℝ) - 1 := by linarith
  have hmul := mul_le_mul_of_nonneg_left hhalf (Nat.cast_nonneg g : (0 : ℝ) ≤ g)
  have hWMreal : (W : ℝ) ≤ M := by exact_mod_cast hWM
  have hMpos : (0 : ℝ) < M := by
    by_contra! h
    have hz : (M : ℝ) = 0 := le_antisymm h (Nat.cast_nonneg _)
    rw [hz] at hsize
    norm_num at hsize
  apply (mul_le_mul_iff_of_pos_right hMpos).mp
  nlinarith

theorem residue_parameter_covers {D : Finset ℕ} {W : ℕ} (hcard : 2 ≤ D.card) :
    2 * W ≤ (2 * W / (D.card - 1) + 1) * (D.card - 1) := by
  have hb : 0 < D.card - 1 := by omega
  have hmod := Nat.mod_lt (2 * W) hb
  have hdecomp := Nat.mod_add_div (2 * W) (D.card - 1)
  nlinarith

theorem density_residue_parameter_bound {D : Finset ℕ} {W M : ℕ} {η : ℝ}
    (hηone : η ≤ 1) (hsize : 2 ≤ η * M)
    (hdensity : η * M ≤ D.card) (hWM : W ≤ M) :
    η * (2 * W / (D.card - 1) + 1 : ℕ) ≤ (5 : ℝ) := by
  have hcard : 2 ≤ D.card := by exact_mod_cast hsize.trans hdensity
  have hhalf : η * M / 2 ≤ ((D.card - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ D.card), Nat.cast_one]
    linarith
  have hquot := Nat.div_mul_le_self (2 * W) (D.card - 1)
  have hquotReal : ((2 * W / (D.card - 1) : ℕ) : ℝ) * (D.card - 1 : ℕ) ≤ 2 * W := by
    exact_mod_cast hquot
  have hmul := mul_le_mul_of_nonneg_left hhalf
    (Nat.cast_nonneg (2 * W / (D.card - 1)) : (0 : ℝ) ≤ (2 * W / (D.card - 1) : ℕ))
  have hWMreal : (W : ℝ) ≤ M := by exact_mod_cast hWM
  have hMpos : (0 : ℝ) < M := by
    by_contra! h
    have hz : (M : ℝ) = 0 := le_antisymm h (Nat.cast_nonneg _)
    rw [hz] at hsize
    norm_num at hsize
  have hq : η * (2 * W / (D.card - 1) : ℕ) ≤ (4 : ℝ) := by
    apply (mul_le_mul_iff_of_pos_right hMpos).mp
    nlinarith
  push_cast
  nlinarith

theorem density_width_bound {D : Finset ℕ} {W M : ℕ} {η : ℝ}
    (hD : ∀ d ∈ D, d ≤ W) (hsize : 2 ≤ η * M) (hdensity : η * M ≤ D.card) :
    η * M / 2 ≤ W := by
  have hsubset : D ⊆ Finset.range (W + 1) := by
    intro d hd
    exact Finset.mem_range.mpr (by have := hD d hd; omega)
  have hcard : D.card ≤ W + 1 := (Finset.card_le_card hsubset).trans_eq (Finset.card_range _)
  have hreal : (D.card : ℝ) ≤ W + 1 := by exact_mod_cast hcard
  linarith

end Erdos790.Upper
