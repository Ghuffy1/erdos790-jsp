import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Elementary density of residues coprime to a factorial

Euler's product is bounded below by a product over all odd integers. A
telescoping square estimate gives the weak density needed by the sampling
construction.
-/

open Finset

namespace Erdos790.Upper

def oddDensity (n : ℕ) : ℚ :=
  ∏ k ∈ Finset.range n, (2 * (k : ℚ) + 2) / (2 * (k : ℚ) + 3)

theorem oddDensity_pos (n : ℕ) : 0 < oddDensity n := by
  apply Finset.prod_pos
  intro k _
  positivity

theorem oddDensity_succ (n : ℕ) :
    oddDensity (n + 1) = oddDensity n * ((2 * (n : ℚ) + 2) / (2 * (n : ℚ) + 3)) := by
  exact Finset.prod_range_succ _ n

theorem oddDensity_square_bound (n : ℕ) :
    1 ≤ (oddDensity n) ^ 2 * (2 * (n : ℚ) + 1) := by
  induction n with
  | zero => norm_num [oddDensity]
  | succ n ih =>
    have hden : (0 : ℚ) < 2 * n + 3 := by positivity
    have hscaled := mul_le_mul_of_nonneg_right ih hden.le
    have hbound : 2 * (n : ℚ) + 3 ≤ (oddDensity n) ^ 2 * (2 * n + 2) ^ 2 := by
      nlinarith [sq_nonneg (oddDensity n)]
    have hidentity : (oddDensity (n + 1)) ^ 2 * (2 * ((n + 1 : ℕ) : ℚ) + 1) =
        (oddDensity n) ^ 2 * (2 * (n : ℚ) + 2) ^ 2 / (2 * n + 3) := by
      rw [oddDensity_succ]
      push_cast
      field_simp
      ring
    rw [hidentity]
    exact (le_div_iff₀ hden).mpr (by simpa using hbound)

theorem factorial_prime_factors_subset (n : ℕ) :
    (n.factorial).primeFactors ⊆
      insert 2 ((Finset.range n).image (fun k : ℕ => 2 * k + 3)) := by
  intro p hp
  have hprime := Nat.prime_of_mem_primeFactors hp
  have hle : p ≤ n := hprime.dvd_factorial.mp (Nat.dvd_of_mem_primeFactors hp)
  rcases hprime.eq_two_or_odd' with rfl | hodd
  · exact Finset.mem_insert_self _ _
  · obtain ⟨k, hk⟩ := hodd
    have hkpos : 0 < k := by have := hprime.two_le; omega
    apply Finset.mem_insert_of_mem
    refine Finset.mem_image.mpr ⟨k - 1, Finset.mem_range.mpr (by omega), ?_⟩
    omega

theorem factorial_totient_ratio_lower (n : ℕ) :
    oddDensity n / 2 ≤ (n.factorial.totient : ℚ) / n.factorial := by
  let f := fun p : ℕ => ((p : ℚ) - 1) / p
  let S := insert 2 ((Finset.range n).image (fun k : ℕ => 2 * k + 3))
  have hge : ∀ p ∈ S, 2 ≤ p := by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact le_rfl
    · obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hp
      omega
  have hnonneg : ∀ p ∈ S, 0 ≤ f p := by
    intro p hp
    have h : (2 : ℚ) ≤ p := by exact_mod_cast hge p hp
    exact div_nonneg (by linarith) (by linarith)
  have hone : ∀ p ∈ S, f p ≤ 1 := by
    intro p hp
    have h : (2 : ℚ) ≤ p := by exact_mod_cast hge p hp
    exact (div_le_iff₀ (by linarith : (0 : ℚ) < p)).mpr (by linarith)
  have hprod : (∏ p ∈ S, f p) ≤ ∏ p ∈ (n.factorial).primeFactors, f p :=
    Finset.prod_le_prod_of_subset_of_le_one₀ (factorial_prime_factors_subset n)
      hnonneg (fun p hp _ => hone p hp)
  have hnot : 2 ∉ (Finset.range n).image (fun k : ℕ => 2 * k + 3) := by
    intro h
    obtain ⟨k, _, hk⟩ := Finset.mem_image.mp h
    omega
  have hleft : (∏ p ∈ S, f p) = oddDensity n / 2 := by
    rw [Finset.prod_insert hnot, Finset.prod_image]
    · have hfactor : ∀ k ∈ Finset.range n,
          f (2 * k + 3) = (2 * (k : ℚ) + 2) / (2 * k + 3) := by
        intro k _
        dsimp [f]
        push_cast
        congr 1 <;> ring
      rw [Finset.prod_congr rfl hfactor]
      change f 2 * oddDensity n = oddDensity n / 2
      norm_num [f]
      ring
    · intro a _ b _ hab
      change 2 * a + 3 = 2 * b + 3 at hab
      omega
  have hQ : (n.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hweights : (∏ p ∈ (n.factorial).primeFactors, f p) =
      ∏ p ∈ (n.factorial).primeFactors, (1 - (p : ℚ)⁻¹) := by
    apply Finset.prod_congr rfl
    intro p hp
    have hp0 : (p : ℚ) ≠ 0 := by
      exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
    dsimp [f]
    field_simp
  have hright : (∏ p ∈ (n.factorial).primeFactors, f p) =
      (n.factorial.totient : ℚ) / n.factorial := by
    rw [hweights, Nat.totient_eq_mul_prod_factors]
    field_simp
  rwa [hleft, hright] at hprod

theorem factorial_totient_density {n v : ℕ} (hv : 0 < v) (hnv : n ≤ v ^ 2) :
    n.factorial ≤ 4 * v * n.factorial.totient := by
  have hv1 : (1 : ℚ) ≤ v := by exact_mod_cast hv
  have hnvQ : (n : ℚ) ≤ (v : ℚ) ^ 2 := by exact_mod_cast hnv
  have hden : 2 * (n : ℚ) + 1 ≤ 4 * (v : ℚ) ^ 2 := by nlinarith
  have hlarge := oddDensity_square_bound n
  have hscaled := mul_le_mul_of_nonneg_left hden (sq_nonneg (oddDensity n))
  have hsquare : 1 ≤ (2 * (v : ℚ) * oddDensity n) ^ 2 := by nlinarith
  have hnonneg : 0 ≤ 2 * (v : ℚ) * oddDensity n := by
    have := (oddDensity_pos n).le
    positivity
  have hlinear : 1 ≤ 2 * (v : ℚ) * oddDensity n := by nlinarith
  have hratio : (1 : ℚ) ≤ 4 * v * ((n.factorial.totient : ℚ) / n.factorial) := by
    calc
      (1 : ℚ) ≤ 2 * (v : ℚ) * oddDensity n := hlinear
      _ = 4 * v * (oddDensity n / 2) := by ring
      _ ≤ 4 * v * ((n.factorial.totient : ℚ) / n.factorial) :=
        mul_le_mul_of_nonneg_left (factorial_totient_ratio_lower n) (by positivity)
  have hQ : (0 : ℚ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have hresult := mul_le_mul_of_nonneg_right hratio hQ.le
  have hidentity : (4 * (v : ℚ) * ((n.factorial.totient : ℚ) / n.factorial)) * n.factorial =
      4 * v * n.factorial.totient := by field_simp
  rw [hidentity, one_mul] at hresult
  exact_mod_cast hresult

end Erdos790.Upper
