import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Data.Int.GCD
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Exact sums in a complete lattice interval

A target in the correct residue class and between the endpoint sums has an
exact-length representation. Bézout's identity supplies the bounded number
of copies needed when the modulus decreases.
-/

namespace Erdos790.Upper

theorem sum_map_nat_affine (L : List ℕ) (p g : ℤ) :
    (L.map (fun x : ℕ => p + g * (x : ℤ))).sum =
      L.length * p + g * (L.sum : ℤ) := by
  induction L with
  | nil => simp
  | cons x L ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add,
      Nat.cast_one, ih]
    ring

theorem nat_interval_exact_sum (n W N : ℕ) (hN : N ≤ n * W) :
    ∃ L : List ℕ, L.length = n ∧ (∀ x ∈ L, x ≤ W) ∧ L.sum = N := by
  by_cases hn : n = 0
  · subst n
    have hzero : N = 0 := by omega
    exact ⟨[], by simp, by simp, by simp [hzero]⟩
  have hnpos : 0 < n := by omega
  let q := N / n
  let r := N % n
  have hr : r < n := Nat.mod_lt N hnpos
  have hdecomp : r + n * q = N := Nat.mod_add_div N n
  have hq : q ≤ W := by
    by_contra! h
    have hmul := Nat.mul_le_mul_left n (show W + 1 ≤ q by omega)
    nlinarith
  have hqsucc : 0 < r → q + 1 ≤ W := by
    intro hpos
    by_contra! h
    have hmul := Nat.mul_le_mul_left n (show W ≤ q by omega)
    nlinarith
  refine ⟨List.replicate r (q + 1) ++ List.replicate (n - r) q, ?_, ?_, ?_⟩
  · simp only [List.length_append, List.length_replicate]
    omega
  · intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨hpos, rfl⟩ := List.mem_replicate.mp hx
      exact hqsucc (by omega)
    · obtain ⟨_, rfl⟩ := List.mem_replicate.mp hx
      exact hq
  · simp only [List.sum_append, List.sum_replicate, Nat.nsmul_eq_mul]
    have hsub : n - r + r = n := by omega
    nlinarith

theorem exact_length_lattice_sum {g p q N : ℤ} {n : ℕ}
    (hg : 0 < g) (hpq : p ≤ q) (hq : g ∣ q - p)
    (hN : g ∣ N - n * p) (hlower : n * p ≤ N) (hupper : N ≤ n * q) :
    ∃ L : List ℤ, L.length = n ∧
      (∀ x ∈ L, p ≤ x ∧ x ≤ q ∧ g ∣ x - p) ∧ L.sum = N := by
  obtain ⟨W, hW⟩ := hq
  obtain ⟨K, hK⟩ := hN
  have hWnonneg : 0 ≤ W := by nlinarith
  have hKnonneg : 0 ≤ K := by nlinarith
  have hKupper : K ≤ n * W := by nlinarith
  have hcastW : (W.toNat : ℤ) = W := Int.toNat_of_nonneg hWnonneg
  have hcastK : (K.toNat : ℤ) = K := Int.toNat_of_nonneg hKnonneg
  have hnat : K.toNat ≤ n * W.toNat := by
    have h := hKupper
    rw [← hcastK, ← hcastW] at h
    exact_mod_cast h
  obtain ⟨L, hlength, hL, hsum⟩ := nat_interval_exact_sum n W.toNat K.toNat hnat
  refine ⟨L.map (fun x : ℕ => p + g * (x : ℤ)), by simp [hlength], ?_, ?_⟩
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
    have ha0 : (0 : ℤ) ≤ a := Int.natCast_nonneg a
    have hab : (a : ℤ) ≤ W := by
      rw [← hcastW]
      exact_mod_cast (hL a ha)
    refine ⟨by nlinarith, by nlinarith, ?_⟩
    exact ⟨a, by ring⟩
  · rw [sum_map_nat_affine, hlength, hsum, hcastK]
    nlinarith

theorem bounded_gcd_residue {g d target : ℤ} (hg : 0 < g)
    (hdiv : (Int.gcd g d : ℤ) ∣ target) :
    ∃ v : ℕ, (v : ℤ) < g ∧ g ∣ target - v * d := by
  obtain ⟨c, hc⟩ := hdiv
  let e := Int.gcdB g d * c
  have hnonneg : 0 ≤ e % g := Int.emod_nonneg e (ne_of_gt hg)
  have hcast : ((e % g).toNat : ℤ) = e % g := Int.toNat_of_nonneg hnonneg
  refine ⟨(e % g).toNat, ?_, ?_⟩
  · rw [hcast]
    exact Int.emod_lt_of_pos e hg
  · rw [hcast]
    have hrem : e - e % g = g * (e / g) := by
      have := Int.emod_add_mul_ediv e g
      omega
    refine ⟨Int.gcdA g d * c + d * (e / g), ?_⟩
    calc
      target - e % g * d =
          g * (Int.gcdA g d * c) + d * (e - e % g) := by
        rw [hc, Int.gcd_eq_gcd_ab]
        dsimp [e]
        ring
      _ = g * (Int.gcdA g d * c + d * (e / g)) := by rw [hrem]; ring

end Erdos790.Upper
