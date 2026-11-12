import Erdos790.Upper.FourierCover

/-!
# Product bounds for independent coefficient choices
-/

open Finset

namespace Erdos790.Upper

theorem norm_prod_le_with_good {ι : Type*} [Fintype ι] (f : ι → ℂ)
    (good : Finset ι) (A ρ : ℝ)
    (hall : ∀ i, ‖f i‖ ≤ A) (hgood : ∀ i ∈ good, ‖f i‖ ≤ A * ρ) :
    ‖∏ i, f i‖ ≤ A ^ Fintype.card ι * ρ ^ good.card := by
  classical
  calc
    ‖∏ i, f i‖ = ∏ i, ‖f i‖ := norm_prod _ _
    _ ≤ ∏ i, A * (if i ∈ good then ρ else 1) := by
      apply Finset.prod_le_prod₀ (fun i _ => norm_nonneg (f i))
      intro i _
      by_cases hi : i ∈ good
      · simpa [hi] using hgood i hi
      · simpa [hi] using hall i
    _ = A ^ Fintype.card ι * ρ ^ good.card := by
      rw [Finset.prod_mul_distrib]
      simp

theorem character_factor_norm_le {M B : ℕ} [NeZero M] (a : ZMod M) :
    ‖∑ c : Fin B, ZMod.stdAddChar (-((c.val : ZMod M) * a))‖ ≤ B := by
  calc
    ‖∑ c : Fin B, ZMod.stdAddChar (-((c.val : ZMod M) * a))‖ ≤
        ∑ c : Fin B, ‖ZMod.stdAddChar (-((c.val : ZMod M) * a))‖ := norm_sum_le _ _
    _ = B := by simp

theorem character_product_tail_small {ι : Type*} [Fintype ι]
    {M B k : ℕ} [NeZero M] (value : ι → ZMod M) {ρ : ℝ}
    (hB : 0 < B) (hρ : 0 ≤ ρ) (hsmall : (M : ℝ) * ρ ^ k < 1)
    (hgood : ∀ a : ZMod M, a ≠ 0 → ∃ good : Finset ι,
      good.card = k ∧ ∀ i ∈ good,
        ‖∑ c : Fin B, ZMod.stdAddChar (-((c.val : ZMod M) * value i * a))‖ ≤ B * ρ) :
    (∑ a ∈ (Finset.univ : Finset (ZMod M)).erase 0,
      ‖∏ i, ∑ c : Fin B,
        ZMod.stdAddChar (-((c.val : ZMod M) * value i * a))‖) <
      (B : ℝ) ^ Fintype.card ι := by
  classical
  have hpower : (0 : ℝ) < (B : ℝ) ^ Fintype.card ι := by positivity
  have hbound : ∀ a ∈ (Finset.univ : Finset (ZMod M)).erase 0,
      ‖∏ i, ∑ c : Fin B, ZMod.stdAddChar (-((c.val : ZMod M) * value i * a))‖ ≤
        (B : ℝ) ^ Fintype.card ι * ρ ^ k := by
    intro a ha
    obtain ⟨good, hcard, hnorm⟩ := hgood a (Finset.ne_of_mem_erase ha)
    rw [← hcard]
    apply norm_prod_le_with_good _ good B ρ ?_ hnorm
    intro i
    simpa only [mul_assoc] using character_factor_norm_le (B := B) (value i * a)
  have hcard : (((Finset.univ : Finset (ZMod M)).erase 0).card : ℝ) ≤ M := by
    exact_mod_cast (Finset.card_le_card (Finset.erase_subset 0
      (Finset.univ : Finset (ZMod M)))).trans_eq (by simp)
  calc
    _ ≤ ∑ _a ∈ (Finset.univ : Finset (ZMod M)).erase 0,
        (B : ℝ) ^ Fintype.card ι * ρ ^ k := Finset.sum_le_sum hbound
    _ ≤ (M : ℝ) * ((B : ℝ) ^ Fintype.card ι * ρ ^ k) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = ((M : ℝ) * ρ ^ k) * (B : ℝ) ^ Fintype.card ι := by ring
    _ < (B : ℝ) ^ Fintype.card ι := by simpa using mul_lt_mul_of_pos_right hsmall hpower

end Erdos790.Upper
