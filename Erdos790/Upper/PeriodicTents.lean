import Erdos790.Upper.Tents

/-!
# Periodic integer tents and aligned cells

Each peak lies halfway between adjacent integers. A larger tent is affine
on the integer points of every aligned smaller cell whose length divides
the larger half-period.
-/

namespace Erdos790.Upper

def periodicTent (M t : ℕ) : ℕ :=
  min (2 * (t % (2 * M)) + 1) (4 * M - 2 * (t % (2 * M)) - 1)

theorem periodicTent_bounds {M t : ℕ} (hM : 0 < M) :
    0 < periodicTent M t ∧ periodicTent M t < 2 * M := by
  have hr := Nat.mod_lt t (by omega : 0 < 2 * M)
  unfold periodicTent
  constructor
  · omega
  · by_cases hhalf : t % (2 * M) < M
    · exact (min_le_left _ _).trans_lt (by omega)
    · exact (min_le_right _ _).trans_lt (by omega)

theorem periodicTent_int {M t : ℕ} (hM : 0 < M) :
    (periodicTent M t : ℤ) = integerTent M ((t % (2 * M) : ℕ) : ℤ) := by
  have hr := Nat.mod_lt t (by omega : 0 < 2 * M)
  have hsub1 : 2 * (t % (2 * M)) ≤ 4 * M := by omega
  have hsub2 : 1 ≤ 4 * M - 2 * (t % (2 * M)) := by omega
  unfold periodicTent integerTent
  rw [Nat.cast_min, Nat.cast_sub hsub2, Nat.cast_sub hsub1]
  push_cast
  rfl

theorem periodicTent_on_cell {M a t : ℕ} (hM : 0 < M) (ha : 2 * M ∣ a)
    (hat : a ≤ t) (hta : t < a + 2 * M) :
    (periodicTent M t : ℤ) = integerTent M ((t : ℤ) - a) := by
  have hdiff : t - a < 2 * M := by omega
  have hmod : t % (2 * M) = t - a := by
    calc
      t % (2 * M) = (a + (t - a)) % (2 * M) := by rw [Nat.add_sub_of_le hat]
      _ = t - a := by
        rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd ha, Nat.mod_eq_of_lt hdiff]
        simpa only [Nat.zero_add] using Nat.mod_eq_of_lt hdiff
  rw [periodicTent_int hM, hmod, Nat.cast_sub hat]

theorem quotient_constant_on_aligned_cell {C M a t : ℕ} (hC : 0 < C)
    (hCM : C ∣ M) (hCa : C ∣ a) (hat : a ≤ t) (hta : t < a + C) :
    t / M = a / M := by
  obtain ⟨r, hr⟩ := hCa
  have htC : t / C = r := by
    calc
      t / C = ((t - C * r) + C * r) / C := by congr 1; omega
      _ = (t - C * r) / C + r := Nat.add_mul_div_left _ _ hC
      _ = r := by rw [Nat.div_eq_of_lt (by omega)]; omega
  have haC : a / C = r := by rw [hr, Nat.mul_div_cancel_left _ hC]
  obtain ⟨s, hs⟩ := hCM
  rw [hs, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, htC, haC]

theorem periodicTent_halfcell_formula {M t q : ℕ} (hM : 0 < M) (htq : t / M = q) :
    (periodicTent M t : ℤ) =
      if q % 2 = 0 then 2 * (t : ℤ) + 1 - 2 * M * q
      else 2 * M * (q + 1) - 2 * t - 1 := by
  have hr : t % M < M := Nat.mod_lt t hM
  have hq : q % 2 < 2 := Nat.mod_lt q (by decide)
  have htdecomp : t % M + M * q = t := by
    simpa only [htq] using Nat.mod_add_div t M
  have hqdecomp := Nat.mod_add_div q 2
  have hdecomp : t = (M * (q % 2) + t % M) + (2 * M) * (q / 2) := by
    nlinarith
  have hsmall : M * (q % 2) + t % M < 2 * M := by
    nlinarith
  have hmod : t % (2 * M) = M * (q % 2) + t % M := by
    calc
      t % (2 * M) = ((M * (q % 2) + t % M) + (2 * M) * (q / 2)) % (2 * M) :=
        congrArg (fun n => n % (2 * M)) hdecomp
      _ = (M * (q % 2) + t % M) % (2 * M) := by simp
      _ = M * (q % 2) + t % M := Nat.mod_eq_of_lt hsmall
  have htInt : ((t % M : ℕ) : ℤ) + (M : ℤ) * q = t := by exact_mod_cast htdecomp
  have hrInt : ((t % M : ℕ) : ℤ) < M := by exact_mod_cast hr
  rw [periodicTent_int hM, hmod]
  by_cases hparity : q % 2 = 0
  · rw [if_pos hparity, hparity]
    simp only [Nat.mul_zero, Nat.zero_add]
    unfold integerTent
    rw [min_eq_left (by omega)]
    nlinarith
  · have hodd : q % 2 = 1 := by omega
    rw [if_neg hparity, hodd]
    simp only [Nat.mul_one, Nat.cast_add]
    unfold integerTent
    rw [min_eq_right (by omega)]
    nlinarith

theorem periodicTent_affine_on_cell {C M a : ℕ} (hC : 0 < C) (hM : 0 < M)
    (hCM : C ∣ M) (hCa : C ∣ a) :
    ∃ slope intercept : ℤ, (slope = 2 ∨ slope = -2) ∧
      ∀ t : ℕ, a ≤ t → t < a + C →
        (periodicTent M t : ℤ) = slope * t + intercept := by
  by_cases hparity : (a / M) % 2 = 0
  · refine ⟨2, 1 - 2 * M * ((a / M : ℕ) : ℤ), Or.inl rfl, ?_⟩
    intro t hat hta
    rw [periodicTent_halfcell_formula hM (quotient_constant_on_aligned_cell hC hCM hCa hat hta),
      if_pos hparity]
    ring
  · refine ⟨-2, 2 * M * (((a / M : ℕ) : ℤ) + 1) - 1, Or.inr rfl, ?_⟩
    intro t hat hta
    rw [periodicTent_halfcell_formula hM (quotient_constant_on_aligned_cell hC hCM hCa hat hta),
      if_neg hparity]
    ring

theorem dyadic_periodicTent_affine {d h h' a : ℕ} (hhh' : h < h')
    (ha : 2 * 2 ^ (d + h) ∣ a) :
    ∃ slope intercept : ℤ, (slope = 2 ∨ slope = -2) ∧
      ∀ t : ℕ, a ≤ t → t < a + 2 * 2 ^ (d + h) →
        (periodicTent (2 ^ (d + h')) t : ℤ) = slope * t + intercept := by
  apply periodicTent_affine_on_cell (by positivity) (by positivity) _ ha
  rw [← pow_succ']
  exact Nat.pow_dvd_pow 2 (by omega)

end Erdos790.Upper
