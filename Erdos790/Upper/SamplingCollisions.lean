import Erdos790.Upper.ExponentialSampling
import Mathlib.Logic.Equiv.Prod

/-!
# Collision counts for independent finite samples

Swapping one sampled coordinate with an auxiliary independent value gives
the required uniform fiber bound without probability-space machinery.
-/

open Finset

namespace Erdos790.Upper

def swapSampleCoordinate {ι α : Type*} [DecidableEq ι] (i : ι) :
    ((ι → α) × α) ≃ ((ι → α) × α) where
  toFun p := (Function.update p.1 i p.2, p.1 i)
  invFun p := (Function.update p.1 i p.2, p.1 i)
  left_inv p := by
    rcases p with ⟨sample, a⟩
    apply Prod.ext
    · funext j
      by_cases hji : j = i
      · subst j
        simp
      · simp [Function.update_of_ne hji]
    · simp
  right_inv p := by
    rcases p with ⟨sample, a⟩
    apply Prod.ext
    · funext j
      by_cases hji : j = i
      · subst j
        simp
      · simp [Function.update_of_ne hji]
    · simp

set_option maxHeartbeats 800000 in
theorem coordinate_collision_bound {ι α β : Type*} [Fintype ι] [Fintype α]
    [DecidableEq ι] [DecidableEq β] (label : α → β) (H : ℕ)
    (hfiber : ∀ b, ((Finset.univ : Finset α).filter (fun a => label a = b)).card ≤ H)
    {i j : ι} (hij : i ≠ j) :
    Fintype.card α * (∑ sample : ι → α,
      if label (sample i) = label (sample j) then 1 else 0) ≤
        H * Fintype.card (ι → α) := by
  classical
  have hji : j ≠ i := Ne.symm hij
  have hswap :
      (∑ p : (ι → α) × α, if label (p.1 i) = label (p.1 j) then 1 else 0) =
        ∑ p : (ι → α) × α, if label p.2 = label (p.1 j) then 1 else 0 := by
    apply Fintype.sum_equiv (swapSampleCoordinate (α := α) i)
      (fun p : (ι → α) × α => if label (p.1 i) = label (p.1 j) then (1 : ℕ) else 0)
      (fun p : (ι → α) × α => if label p.2 = label (p.1 j) then (1 : ℕ) else 0)
    intro p
    simp [swapSampleCoordinate, Function.update_of_ne hji]
  have hcount (sample : ι → α) :
      (∑ a : α, if label a = label (sample j) then 1 else 0) ≤ H := by
    simpa only [Finset.card_filter] using hfiber (label (sample j))
  have hinner (sample : ι → α) :
      (∑ _a : α, if label (sample i) = label (sample j) then (1 : ℕ) else 0) =
        Fintype.card α * (if label (sample i) = label (sample j) then 1 else 0) := by
    by_cases h : label (sample i) = label (sample j) <;> simp [h]
  calc
    _ = ∑ sample : ι → α, Fintype.card α *
        (if label (sample i) = label (sample j) then 1 else 0) := Finset.mul_sum _ _ _
    _ = ∑ sample : ι → α, ∑ _a : α,
        if label (sample i) = label (sample j) then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro sample _
      exact (hinner sample).symm
    _ = ∑ p : (ι → α) × α, if label (p.1 i) = label (p.1 j) then 1 else 0 :=
      (Fintype.sum_prod_type (fun p : (ι → α) × α =>
        if label (p.1 i) = label (p.1 j) then (1 : ℕ) else 0)).symm
    _ = ∑ p : (ι → α) × α, if label p.2 = label (p.1 j) then 1 else 0 := hswap
    _ = ∑ sample : ι → α, ∑ a : α, if label a = label (sample j) then 1 else 0 :=
      Fintype.sum_prod_type (fun p : (ι → α) × α =>
        if label p.2 = label (p.1 j) then (1 : ℕ) else 0)
    _ ≤ ∑ _sample : ι → α, H := Finset.sum_le_sum (fun sample _ => hcount sample)
    _ = H * Fintype.card (ι → α) := by simp [Nat.mul_comm]

def sampleCollisionCount {ι α β : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq β]
    (label : α → β) (sample : ι → α) : ℕ :=
  ∑ p : ι × ι,
    if p.1 ≠ p.2 ∧ label (sample p.1) = label (sample p.2) then 1 else 0

theorem sampleCollisionCount_eq_zero_iff {ι α β : Type*} [Fintype ι]
    [DecidableEq ι] [DecidableEq β] (label : α → β) (sample : ι → α) :
    sampleCollisionCount label sample = 0 ↔ Function.Injective (fun i => label (sample i)) := by
  classical
  constructor
  · intro hzero i j heq
    by_contra hij
    have hsingle := Finset.single_le_sum
      (f := fun p : ι × ι =>
        if p.1 ≠ p.2 ∧ label (sample p.1) = label (sample p.2) then 1 else 0)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ (i, j))
    change (if i ≠ j ∧ label (sample i) = label (sample j) then 1 else 0) ≤
      sampleCollisionCount label sample at hsingle
    simp [hij, heq, hzero] at hsingle
  · intro hinj
    apply Finset.sum_eq_zero
    intro p _
    have hfalse : ¬(p.1 ≠ p.2 ∧ label (sample p.1) = label (sample p.2)) := by
      rintro ⟨hne, heq⟩
      exact hne (hinj heq)
    simp [hfalse]

theorem total_collision_bound {ι α β : Type*} [Fintype ι] [Fintype α]
    [DecidableEq ι] [DecidableEq β] (label : α → β) (H : ℕ)
    (hfiber : ∀ b, ((Finset.univ : Finset α).filter (fun a => label a = b)).card ≤ H) :
    Fintype.card α * (∑ sample : ι → α, sampleCollisionCount label sample) ≤
      (Fintype.card ι) ^ 2 * H * Fintype.card (ι → α) := by
  classical
  have hpair (p : ι × ι) :
      Fintype.card α * (∑ sample : ι → α,
        if p.1 ≠ p.2 ∧ label (sample p.1) = label (sample p.2) then 1 else 0) ≤
          H * Fintype.card (ι → α) := by
    by_cases hne : p.1 ≠ p.2
    · simpa [hne] using coordinate_collision_bound label H hfiber hne
    · simp [hne]
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (ι × ι))) (fun p _ => hpair p)
  simp only [← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_prod,
    Nat.nsmul_eq_mul] at hsum
  rw [Finset.sum_comm] at hsum
  change Fintype.card α * (∑ sample : ι → α, sampleCollisionCount label sample) ≤ _ at hsum
  simpa only [pow_two, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hsum

theorem collision_mass_le_quarter {ι α β : Type*} [Fintype ι] [Fintype α]
    [DecidableEq ι] [DecidableEq β] [Nonempty α] (label : α → β) (H : ℕ)
    (hfiber : ∀ b, ((Finset.univ : Finset α).filter (fun a => label a = b)).card ≤ H)
    (hsize : 4 * (Fintype.card ι) ^ 2 * H ≤ Fintype.card α) :
    (∑ sample : ι → α, (sampleCollisionCount label sample : ℝ)) ≤
      (Fintype.card (ι → α) : ℝ) / 4 := by
  have hbase := total_collision_bound (ι := ι) label H hfiber
  have hscaled : Fintype.card α * (4 * ∑ sample : ι → α,
      sampleCollisionCount label sample) ≤ Fintype.card α * Fintype.card (ι → α) := by
    calc
      _ = 4 * (Fintype.card α * ∑ sample : ι → α, sampleCollisionCount label sample) := by ring
      _ ≤ 4 * ((Fintype.card ι) ^ 2 * H * Fintype.card (ι → α)) :=
        Nat.mul_le_mul_left 4 hbase
      _ = (4 * (Fintype.card ι) ^ 2 * H) * Fintype.card (ι → α) := by ring
      _ ≤ Fintype.card α * Fintype.card (ι → α) := Nat.mul_le_mul_right _ hsize
  have hcount : 4 * (∑ sample : ι → α, sampleCollisionCount label sample) ≤
      Fintype.card (ι → α) := Nat.le_of_mul_le_mul_left hscaled Fintype.card_pos
  have hreal : (4 : ℝ) * (∑ sample : ι → α, (sampleCollisionCount label sample : ℝ)) ≤
      Fintype.card (ι → α) := by exact_mod_cast hcount
  linarith

theorem exists_injective_sample_with_few_bad
    {ι α β T : Type*} [Fintype ι] [Fintype α] [Fintype T]
    [DecidableEq ι] [DecidableEq α] [DecidableEq β] [Nonempty α]
    (bad : T → Finset α) (label : α → β) (H : ℕ) {L k : ℕ}
    (hL : 0 < L) (hcard : Fintype.card ι = 2 * L * k)
    (hbad : ∀ t, ((bad t).card : ℝ) ≤ Fintype.card α / (100 * (L : ℝ)))
    (hfiber : ∀ b, ((Finset.univ : Finset α).filter (fun a => label a = b)).card ≤ H)
    (hcollision : 4 * (Fintype.card ι) ^ 2 * H ≤ Fintype.card α)
    (htests : (Fintype.card T : ℝ) * Real.exp (-(k : ℝ) / 2) ≤ 1 / 2) :
    ∃ sample : ι → α, Function.Injective (fun i => label (sample i)) ∧
      ∀ t, sampleBadCount (bad t) sample < k := by
  obtain ⟨sample, hzero, htests'⟩ := simultaneous_sampling bad
    (sampleCollisionCount label) k (Real.exp (-(k : ℝ) / 2))
    (fun t => sampling_exponential_half_bound (bad t) hL hcard (hbad t))
    htests (collision_mass_le_quarter (ι := ι) label H hfiber hcollision)
  exact ⟨sample, (sampleCollisionCount_eq_zero_iff label sample).mp hzero, htests'⟩

end Erdos790.Upper
