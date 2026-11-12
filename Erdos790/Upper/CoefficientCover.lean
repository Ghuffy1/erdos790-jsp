import Erdos790.Upper.FourierProducts
import Erdos790.Upper.ResidueSums

/-!
# Complete residue coverage from independent bounded coefficients
-/

open Finset

namespace Erdos790.Upper

def coefficientSum {ι : Type*} [Fintype ι] {B : ℕ}
    (value : ι → ℕ) (c : ι → Fin B) : ℕ := ∑ i, (c i).val * value i

theorem coefficient_character_factorization {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M B : ℕ} [NeZero M] (value : ι → ℕ) (a : ZMod M) :
    (∑ z : ι → Fin B, ZMod.stdAddChar (-((coefficientSum value z : ZMod M) * a))) =
      ∏ i, ∑ c : Fin B,
        ZMod.stdAddChar (-((c.val : ZMod M) * (value i : ZMod M) * a)) := by
  calc
    _ = ∑ z : ι → Fin B, ZMod.stdAddChar
        (∑ i, -(((z i).val : ZMod M) * (value i : ZMod M) * a)) := by
      apply Finset.sum_congr rfl
      intro z _
      congr 1
      simp only [coefficientSum, Nat.cast_sum, Nat.cast_mul, Finset.sum_mul,
        Finset.sum_neg_distrib]
    _ = _ := independent_character_sum ZMod.stdAddChar
      (fun i (c : Fin B) => -((c.val : ZMod M) * (value i : ZMod M) * a))

theorem coefficient_residue_coverage {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M B : ℕ} [NeZero M] (value : ι → ℕ)
    (htail : (∑ a ∈ (Finset.univ : Finset (ZMod M)).erase 0,
      ‖∏ i, ∑ c : Fin B,
        ZMod.stdAddChar (-((c.val : ZMod M) * (value i : ZMod M) * a))‖) <
      (B : ℝ) ^ Fintype.card ι) (N : ℕ) :
    ∃ c : ι → Fin B, Nat.ModEq M (coefficientSum value c) N := by
  have htail' : (∑ a ∈ (Finset.univ : Finset (ZMod M)).erase 0,
      ‖∑ z : ι → Fin B,
        ZMod.stdAddChar (-((coefficientSum value z : ZMod M) * a))‖) <
        (Fintype.card (ι → Fin B) : ℝ) := by
    simpa only [coefficient_character_factorization, Fintype.card_fun,
      Fintype.card_fin, Nat.cast_pow] using htail
  obtain ⟨c, hc⟩ := finite_residue_coverage
    (fun z : ι → Fin B => (coefficientSum value z : ZMod M)) htail' (N : ZMod M)
  exact ⟨c, (ZMod.natCast_eq_natCast_iff _ _ M).mp hc⟩

theorem coefficient_residue_of_good {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M B k : ℕ} [NeZero M] (value : ι → ℕ) {ρ : ℝ}
    (hB : 0 < B) (hρ : 0 ≤ ρ) (hsmall : (M : ℝ) * ρ ^ k < 1)
    (hgood : ∀ a : ZMod M, a ≠ 0 → ∃ good : Finset ι,
      good.card = k ∧ ∀ i ∈ good,
        ‖∑ c : Fin B,
          ZMod.stdAddChar (-((c.val : ZMod M) * (value i : ZMod M) * a))‖ ≤ B * ρ)
    (N : ℕ) : ∃ c : ι → Fin B, Nat.ModEq M (coefficientSum value c) N := by
  apply coefficient_residue_coverage value
    (character_product_tail_small (fun i => (value i : ZMod M)) hB hρ hsmall hgood) N

theorem coefficient_coverage_gives_sums {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : Finset ℕ} {M X Y B : ℕ} (value : ι → ℕ)
    (hM : M ∈ S) (hMpos : 0 < M) (hX : 0 < X)
    (hS : ∀ x ∈ S, X ≤ x) (hvalue : ∀ i, value i ∈ S)
    (hupper : ∀ i, value i ≤ Y)
    (hcover : ∀ N : ℕ, ∃ c : ι → Fin B, Nat.ModEq M (coefficientSum value c) N) :
    ∀ N : ℕ, Fintype.card ι * (B * Y) ≤ N → ∃ T : List ℕ,
      (∀ x ∈ T, x ∈ S) ∧ T.sum = N ∧ T.length ≤ N / X := by
  apply residue_coverage_gives_sums hM hMpos hX hS
  intro N
  obtain ⟨c, hc⟩ := hcover N
  obtain ⟨L, _, hsum, hL⟩ := coefficient_list (Finset.univ : Finset ι) value
    (fun i => (c i).val)
  refine ⟨L, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, _, rfl⟩ := hL x hx
    exact hvalue i
  · rw [hsum]
    calc
      (∑ i, (c i).val * value i) ≤ ∑ _i : ι, B * Y := by
        apply Finset.sum_le_sum
        intro i _
        exact Nat.mul_le_mul (c i).isLt.le (hupper i)
      _ = Fintype.card ι * (B * Y) := by simp
  · simpa only [hsum, coefficientSum] using hc

end Erdos790.Upper
