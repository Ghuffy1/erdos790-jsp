import Erdos790.Upper.FourierCover
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Finite sampling with exponential penalties

The sample space is finite. A total penalty with average below one supplies
a sample with no collisions and fewer than the allowed number of bad indices
for every test.
-/

open Finset

namespace Erdos790.Upper

theorem exists_sample_with_small_penalties {Ω T : Type*} [Fintype Ω] [Fintype T]
    (penalty : T → Ω → ℝ) (collisions : Ω → ℕ)
    (hpenalty : ∀ t ω, 0 ≤ penalty t ω)
    (haverage : (∑ ω, ((∑ t, penalty t ω) + (collisions ω : ℝ))) < Fintype.card Ω) :
    ∃ ω : Ω, collisions ω = 0 ∧ ∀ t : T, penalty t ω < 1 := by
  classical
  have hexists : ∃ ω : Ω, (∑ t, penalty t ω) + (collisions ω : ℝ) < 1 := by
    by_contra hnone
    push Not at hnone
    have hbound : (Fintype.card Ω : ℝ) ≤
        ∑ ω, ((∑ t, penalty t ω) + (collisions ω : ℝ)) := by
      calc
        (Fintype.card Ω : ℝ) = ∑ _ω : Ω, (1 : ℝ) := by simp
        _ ≤ _ := Finset.sum_le_sum (fun ω _ => hnone ω)
    exact (not_le_of_gt haverage) hbound
  obtain ⟨ω, hω⟩ := hexists
  have hsum0 : 0 ≤ ∑ t, penalty t ω :=
    Finset.sum_nonneg (fun t _ => hpenalty t ω)
  have hcollision : (collisions ω : ℝ) < 1 := by linarith
  have hcollisionNat : collisions ω < 1 := by exact_mod_cast hcollision
  refine ⟨ω, by omega, ?_⟩
  intro t
  have hsingle : penalty t ω ≤ ∑ t', penalty t' ω :=
    Finset.single_le_sum (fun t' _ => hpenalty t' ω) (Finset.mem_univ t)
  have hc0 : (0 : ℝ) ≤ collisions ω := Nat.cast_nonneg _
  linarith

theorem exists_sample_from_exponential_bound {Ω T : Type*} [Fintype Ω] [Fintype T]
    (badCount : T → Ω → ℕ) (collisions : Ω → ℕ) (k : ℕ)
    (haverage : (∑ ω, ((∑ t, Real.exp ((badCount t ω : ℝ) - k)) +
      (collisions ω : ℝ))) < Fintype.card Ω) :
    ∃ ω : Ω, collisions ω = 0 ∧ ∀ t : T, badCount t ω < k := by
  obtain ⟨ω, hc, hbad⟩ := exists_sample_with_small_penalties
    (fun t ω => Real.exp ((badCount t ω : ℝ) - k)) collisions
    (fun _ _ => (Real.exp_pos _).le) haverage
  refine ⟨ω, hc, ?_⟩
  intro t
  have hlt : (badCount t ω : ℝ) < k := by
    have := Real.exp_lt_one_iff.mp (hbad t)
    linarith
  exact_mod_cast hlt

theorem independent_exponential_sum {ι α : Type*} [Fintype ι] [Fintype α]
    [DecidableEq ι] (weight : ι → α → ℝ) :
    (∑ z : ι → α, Real.exp (∑ i, weight i (z i))) =
      ∏ i, ∑ a, Real.exp (weight i a) := by
  let χ : AddChar ℝ ℝ :=
    { toFun := Real.exp
      map_zero_eq_one' := Real.exp_zero
      map_add_eq_mul' := Real.exp_add }
  exact independent_character_sum χ weight

def sampleBadCount {ι α : Type*} [Fintype ι] [DecidableEq α]
    (bad : Finset α) (sample : ι → α) : ℕ :=
  ((Finset.univ : Finset ι).filter (fun i => sample i ∈ bad)).card

theorem sampleBadCount_cast {ι α : Type*} [Fintype ι] [DecidableEq α]
    (bad : Finset α) (sample : ι → α) :
    (sampleBadCount bad sample : ℝ) =
      ∑ i : ι, if sample i ∈ bad then (1 : ℝ) else 0 := by
  simp only [sampleBadCount, Finset.card_filter, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp

theorem single_bad_exponential_sum {α : Type*} [Fintype α] [DecidableEq α]
    (bad : Finset α) :
    (∑ a : α, Real.exp (if a ∈ bad then (1 : ℝ) else 0)) =
      Fintype.card α + (Real.exp 1 - 1) * bad.card := by
  have hterm (a : α) : Real.exp (if a ∈ bad then (1 : ℝ) else 0) =
      1 + (Real.exp 1 - 1) * (if a ∈ bad then (1 : ℝ) else 0) := by
    split_ifs <;> simp
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  simp

theorem sampling_exponential_mass {ι α : Type*} [Fintype ι] [Fintype α]
    [DecidableEq ι] [DecidableEq α] (bad : Finset α) (k : ℕ) :
    (∑ sample : ι → α, Real.exp ((sampleBadCount bad sample : ℝ) - k)) =
      Real.exp (-(k : ℝ)) *
        (Fintype.card α + (Real.exp 1 - 1) * bad.card) ^ Fintype.card ι := by
  have hterm (sample : ι → α) :
      Real.exp ((sampleBadCount bad sample : ℝ) - k) =
        Real.exp (-(k : ℝ)) *
          Real.exp (∑ i : ι, if sample i ∈ bad then (1 : ℝ) else 0) := by
    rw [sampleBadCount_cast, sub_eq_add_neg, Real.exp_add]
    ring
  simp_rw [hterm]
  rw [← Finset.mul_sum, independent_exponential_sum
    (fun (_ : ι) (a : α) => if a ∈ bad then (1 : ℝ) else 0)]
  simp_rw [single_bad_exponential_sum]
  simp

theorem sampling_exponential_bound {ι α : Type*} [Fintype ι] [Fintype α]
    [DecidableEq ι] [DecidableEq α] (bad : Finset α) (k : ℕ) {δ : ℝ}
    (hbad : (bad.card : ℝ) ≤ δ * Fintype.card α) :
    (∑ sample : ι → α, Real.exp ((sampleBadCount bad sample : ℝ) - k)) ≤
      (Fintype.card α : ℝ) ^ Fintype.card ι *
        Real.exp (-(k : ℝ) + Fintype.card ι * δ * (Real.exp 1 - 1)) := by
  have hE : 0 ≤ Real.exp 1 - 1 := by
    have := Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)
    linarith
  have hZ : (0 : ℝ) ≤ Fintype.card α := Nat.cast_nonneg _
  have hbase0 : (0 : ℝ) ≤ Fintype.card α + (Real.exp 1 - 1) * bad.card := by positivity
  have hExp : 1 + δ * (Real.exp 1 - 1) ≤ Real.exp (δ * (Real.exp 1 - 1)) := by
    linarith [Real.add_one_le_exp (δ * (Real.exp 1 - 1))]
  have hbase : (Fintype.card α : ℝ) + (Real.exp 1 - 1) * bad.card ≤
      Fintype.card α * Real.exp (δ * (Real.exp 1 - 1)) := by
    calc
      (Fintype.card α : ℝ) + (Real.exp 1 - 1) * bad.card ≤
          Fintype.card α + (Real.exp 1 - 1) * (δ * Fintype.card α) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hbad hE)
      _ = Fintype.card α * (1 + δ * (Real.exp 1 - 1)) := by ring
      _ ≤ Fintype.card α * Real.exp (δ * (Real.exp 1 - 1)) :=
        mul_le_mul_of_nonneg_left hExp hZ
  rw [sampling_exponential_mass]
  calc
    _ ≤ Real.exp (-(k : ℝ)) *
        (Fintype.card α * Real.exp (δ * (Real.exp 1 - 1))) ^ Fintype.card ι :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hbase0 hbase _) (Real.exp_pos _).le
    _ = (Fintype.card α : ℝ) ^ Fintype.card ι *
        Real.exp (-(k : ℝ) + Fintype.card ι * δ * (Real.exp 1 - 1)) := by
      rw [mul_pow, ← Real.exp_nat_mul]
      rw [show (Fintype.card ι : ℝ) * (δ * (Real.exp 1 - 1)) =
        Fintype.card ι * δ * (Real.exp 1 - 1) by ring]
      rw [Real.exp_add]
      ring

theorem sampling_exponential_half_bound {ι α : Type*} [Fintype ι] [Fintype α]
    [DecidableEq ι] [DecidableEq α] (bad : Finset α) {L k : ℕ}
    (hL : 0 < L) (hcard : Fintype.card ι = 2 * L * k)
    (hbad : (bad.card : ℝ) ≤ Fintype.card α / (100 * (L : ℝ))) :
    (∑ sample : ι → α, Real.exp ((sampleBadCount bad sample : ℝ) - k)) ≤
      (Fintype.card (ι → α) : ℝ) * Real.exp (-(k : ℝ) / 2) := by
  have hLreal : (0 : ℝ) < L := by exact_mod_cast hL
  have hrate : (Fintype.card ι : ℝ) * (1 / (100 * (L : ℝ))) = (k : ℝ) / 50 := by
    rw [hcard]
    push_cast
    field_simp
    ring
  have hE : Real.exp 1 - 1 ≤ 2 := by linarith [Real.exp_one_lt_three]
  have hscale := mul_le_mul_of_nonneg_left hE (by positivity : (0 : ℝ) ≤ (k : ℝ) / 50)
  have hexponent : -(k : ℝ) + Fintype.card ι * (1 / (100 * (L : ℝ))) *
      (Real.exp 1 - 1) ≤ -(k : ℝ) / 2 := by rw [hrate]; linarith
  have hbound := sampling_exponential_bound (ι := ι) bad k
    (δ := 1 / (100 * (L : ℝ))) (by simpa [div_eq_mul_inv, mul_comm] using hbad)
  calc
    _ ≤ (Fintype.card α : ℝ) ^ Fintype.card ι *
        Real.exp (-(k : ℝ) + Fintype.card ι * (1 / (100 * (L : ℝ))) *
          (Real.exp 1 - 1)) := hbound
    _ ≤ (Fintype.card α : ℝ) ^ Fintype.card ι * Real.exp (-(k : ℝ) / 2) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexponent) (by positivity)
    _ = _ := by simp only [Fintype.card_fun, Nat.cast_pow]

theorem simultaneous_sampling {ι α T : Type*} [Fintype ι] [Fintype α] [Fintype T]
    [DecidableEq ι] [DecidableEq α] [Nonempty α]
    (bad : T → Finset α) (collisions : (ι → α) → ℕ) (k : ℕ) (bound : ℝ)
    (hmass : ∀ t, (∑ sample : ι → α,
      Real.exp ((sampleBadCount (bad t) sample : ℝ) - k)) ≤
        (Fintype.card (ι → α) : ℝ) * bound)
    (htests : (Fintype.card T : ℝ) * bound ≤ 1 / 2)
    (hcollisions : (∑ sample : ι → α, (collisions sample : ℝ)) ≤
      (Fintype.card (ι → α) : ℝ) / 4) :
    ∃ sample : ι → α, collisions sample = 0 ∧
      ∀ t, sampleBadCount (bad t) sample < k := by
  have hΩ : (0 : ℝ) < Fintype.card (ι → α) := by exact_mod_cast Fintype.card_pos
  apply exists_sample_from_exponential_bound
    (fun t sample => sampleBadCount (bad t) sample) collisions k
  rw [Finset.sum_add_distrib, Finset.sum_comm]
  have hsum : (∑ t : T, ∑ sample : ι → α,
      Real.exp ((sampleBadCount (bad t) sample : ℝ) - k)) ≤
        (Fintype.card T : ℝ) * ((Fintype.card (ι → α) : ℝ) * bound) := by
    calc
      _ ≤ ∑ _t : T, (Fintype.card (ι → α) : ℝ) * bound :=
        Finset.sum_le_sum (fun t _ => hmass t)
      _ = _ := by simp
  have hscale := mul_le_mul_of_nonneg_right htests hΩ.le
  nlinarith

end Erdos790.Upper
