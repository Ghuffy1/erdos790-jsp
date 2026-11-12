import Erdos790.Upper.Packing
import Erdos790.Upper.GrowthBounds
import Mathlib.Data.Nat.Log

/-!
# Passing from exponentially sized witnesses to every large cardinality
-/

open Filter

namespace Erdos790.Upper

theorem packed_scaled_bound {N m n d : ℕ} {B : ℝ}
    (hN : 0 < N) (hB : 0 ≤ B)
    (hm : (m : ℝ) * ((d : ℝ) + 1) ^ 2 ≤ B * N)
    (hsize : N * (d + 1) ^ 2 ≤ n) :
    ((n / N * m + n % N : ℕ) : ℝ) * ((d : ℝ) + 1) ^ 2 ≤ (B + 1) * n := by
  have hquot : ((n / N : ℕ) : ℝ) * N ≤ n := by
    exact_mod_cast Nat.div_mul_le_self n N
  have hrem : ((n % N : ℕ) : ℝ) ≤ N := by
    exact_mod_cast (Nat.mod_lt n hN).le
  have hsizeReal : (N : ℝ) * ((d : ℝ) + 1) ^ 2 ≤ n := by exact_mod_cast hsize
  have hmain : ((n / N : ℕ) : ℝ) * m * ((d : ℝ) + 1) ^ 2 ≤ B * n := by
    calc
      _ = ((n / N : ℕ) : ℝ) * ((m : ℝ) * ((d : ℝ) + 1) ^ 2) := by ring
      _ ≤ ((n / N : ℕ) : ℝ) * (B * N) :=
        mul_le_mul_of_nonneg_left hm (by positivity)
      _ = B * (((n / N : ℕ) : ℝ) * N) := by ring
      _ ≤ B * n := mul_le_mul_of_nonneg_left hquot hB
  have hrest : ((n % N : ℕ) : ℝ) * ((d : ℝ) + 1) ^ 2 ≤ n :=
    (mul_le_mul_of_nonneg_right hrem (by positivity)).trans hsizeReal
  push_cast
  nlinarith

theorem eventual_upper_of_exponential_witnesses {B : ℝ} {K : ℕ}
    (hB : 0 < B) (hK : 0 < K)
    (hwitness : ∀ᶠ d : ℕ in atTop,
      ∃ A : Finset ℤ, ∃ m : ℕ,
        (∀ x ∈ A, 0 < x) ∧ 0 < A.card ∧ IndependentBound A m ∧
        A.card ≤ 2 ^ (K * d) ∧
        (m : ℝ) * ((d : ℝ) + 1) ^ 2 ≤ B * A.card) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ n : ℕ in atTop, (Erdos790.l n : ℝ) ≤ C * n / Real.log n ^ 2 := by
  let T : ℝ := 2 * K * Real.log 2
  have hT : 0 < T := by
    dsimp [T]
    exact mul_pos (by positivity) (Real.log_pos (by norm_num))
  refine ⟨(B + 1) * T ^ 2, by positivity, ?_⟩
  have hpoly := eventually_polynomial_le_power 1 2 2 (by decide)
  obtain ⟨d₀, hd₀⟩ := eventually_atTop.mp (hwitness.and hpoly)
  apply eventually_atTop.mpr
  refine ⟨max 2 (2 ^ (2 * K * d₀)), ?_⟩
  intro n hn
  have hn2 : 2 ≤ n := (le_max_left _ _).trans hn
  have hnpos : 0 < n := by omega
  let u := Nat.log 2 n
  let d := u / (2 * K)
  have hden : 0 < 2 * K := by positivity
  have hloglower : 2 * K * d₀ ≤ u :=
    Nat.le_log_of_pow_le (by decide) ((le_max_right _ _).trans hn)
  have hdlower : d₀ ≤ d := (Nat.le_div_iff_mul_le hden).mpr (by
    simpa only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hloglower)
  obtain ⟨⟨A, m, hpositive, hApos, hA, hAsize, hmscale⟩, hpolyD⟩ := hd₀ d hdlower
  have hdpow : (d + 1) ^ 2 ≤ 2 ^ (K * d) := by
    have hdK : d ≤ K * d := by nlinarith
    have hpoly' : (d + 1) ^ 2 ≤ 2 ^ d := by simpa only [one_mul] using hpolyD
    exact hpoly'.trans
      (Nat.pow_le_pow_right (by decide : 0 < 2) hdK)
  have hexponent : 2 * K * d ≤ u := by
    simpa only [d, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
      Nat.div_mul_le_self u (2 * K)
  have hnpow : 2 ^ (2 * K * d) ≤ n :=
    (Nat.pow_le_pow_right (by decide : 0 < 2) hexponent).trans
      (Nat.pow_log_le_self 2 hnpos.ne')
  have hsize : A.card * (d + 1) ^ 2 ≤ n := by
    calc
      _ ≤ 2 ^ (K * d) * 2 ^ (K * d) := Nat.mul_le_mul hAsize hdpow
      _ = 2 ^ (2 * K * d) := by rw [← pow_add]; congr 1; ring
      _ ≤ n := hnpow
  have hlogUpper : Real.log (n : ℝ) ≤ T * ((d : ℝ) + 1) := by
    have hdiv := Nat.mod_lt u hden
    have hdecomp := Nat.div_add_mod u (2 * K)
    have hu : u + 1 ≤ 2 * K * (d + 1) := by dsimp [d]; nlinarith
    have hnupper : n ≤ 2 ^ (2 * K * (d + 1)) :=
      (Nat.lt_pow_succ_log_self (by decide) n).le.trans
        (Nat.pow_le_pow_right (by decide : 0 < 2) hu)
    have hnposReal : (0 : ℝ) < n := by exact_mod_cast hnpos
    have hnupperReal : (n : ℝ) ≤ (2 : ℝ) ^ (2 * K * (d + 1)) := by exact_mod_cast hnupper
    have h := Real.log_le_log hnposReal hnupperReal
    rw [Real.log_pow] at h
    dsimp [T]
    push_cast at h
    nlinarith
  have hlogpos : 0 < Real.log (n : ℝ) := Real.log_pos (by
    exact_mod_cast (show 1 < n by omega))
  let a : ℝ := (n / A.card * m + n % A.card : ℕ)
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hascale : a * ((d : ℝ) + 1) ^ 2 ≤ (B + 1) * n :=
    packed_scaled_bound hApos hB.le hmscale hsize
  have hlogsq : Real.log (n : ℝ) ^ 2 ≤ T ^ 2 * ((d : ℝ) + 1) ^ 2 := by
    calc
      _ ≤ (T * ((d : ℝ) + 1)) ^ 2 := pow_le_pow_left₀ hlogpos.le hlogUpper 2
      _ = _ := by ring
  have hamain : a * Real.log (n : ℝ) ^ 2 ≤ (B + 1) * T ^ 2 * n := by
    calc
      _ ≤ a * (T ^ 2 * ((d : ℝ) + 1) ^ 2) := mul_le_mul_of_nonneg_left hlogsq ha
      _ = T ^ 2 * (a * ((d : ℝ) + 1) ^ 2) := by ring
      _ ≤ T ^ 2 * ((B + 1) * n) := mul_le_mul_of_nonneg_left hascale (by positivity)
      _ = _ := by ring
  have haBound : a ≤ (B + 1) * T ^ 2 * n / Real.log (n : ℝ) ^ 2 :=
    (le_div_iff₀ (pow_pos hlogpos 2)).mpr hamain
  exact (hA.all_sizes hpositive n).le.trans haBound

end Erdos790.Upper
