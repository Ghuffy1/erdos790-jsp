import Erdos790.Upper.SeedCore
import Erdos790.Upper.SeedParameters

/-!
# Seeding directly from a dense selected set in one half-cell
-/

namespace Erdos790.Upper

theorem dense_half_interval_seed {S : ℕ → Finset ℤ} {A : Finset ℤ}
    {cut left c : ℤ} {a n M cLevel : ℕ} {η : ℝ}
    (hA : A ⊆ Finset.Ico left (left + M))
    (hη : 0 < η) (hηone : η ≤ 1) (hsize : 2 ≤ η * M)
    (hdensity : η * M ≤ A.card) (hlarge : 64 ≤ η ^ 2 * M)
    (hbudget : 100 ≤ η ^ 2 * (2 : ℝ) ^ n) (hn : 0 < n)
    (hseen : ∀ t ∈ A, ∃ k ≤ a, t ∈ S k)
    (hcLevel : cLevel ≤ a) (hc : c ∈ S cLevel)
    (hside : (c < cut ∧ ∀ t ∈ A, cut ≤ t) ∨ (cut ≤ c ∧ ∀ t ∈ A, t < cut))
    (hcRange : ∀ t ∈ A, |c - t| ≤ 2 * (M : ℤ)) :
    ∃ u ∈ A, ∃ g : ℕ, 0 < g ∧ η * g ≤ 2 ∧ ∃ p q : ℤ,
      (g : ℤ) ∣ p - u ∧ (g : ℤ) ∣ q - u ∧
      left ≤ p ∧ q < left + M ∧ p ≤ q ∧ η * M / 8 ≤ ((q - p : ℤ) : ℝ) ∧
      ∀ t : ℤ, p ≤ t → t ≤ q → (g : ℤ) ∣ t - u → DyadicMean S cut (a + n) t := by
  classical
  have hcard : 2 ≤ A.card := by exact_mod_cast hsize.trans hdensity
  have hnonempty : A.Nonempty := Finset.card_pos.mp (by omega)
  let u := A.min' hnonempty
  let v := A.max' hnonempty
  have hu : u ∈ A := Finset.min'_mem A hnonempty
  have hv : v ∈ A := Finset.max'_mem A hnonempty
  have huv : u ≤ v := Finset.min'_le A v hv
  let W := (v - u).toNat
  have hWcast : (W : ℤ) = v - u := Int.toNat_of_nonneg (sub_nonneg.mpr huv)
  have hvEq : u + (W : ℤ) = v := by omega
  have hbounds : ∀ t ∈ A, u ≤ t ∧ t ≤ u + (W : ℤ) := by
    intro t ht
    exact ⟨Finset.min'_le A t ht, by rw [hvEq]; exact Finset.le_max' A t ht⟩
  have hWM : W ≤ M := by
    have hulo := (Finset.mem_Ico.mp (hA hu)).1
    have hvhi := (Finset.mem_Ico.mp (hA hv)).2
    have hreal : (W : ℤ) ≤ M := by omega
    exact_mod_cast hreal
  obtain ⟨g, hg, hgBound, p, q, hp, hq, hup, hqv, hpq, hspan, hmean⟩ :=
    dense_coordinate_seed_core hu (by simpa only [hvEq] using hv) hbounds
      hη hηone hsize hdensity hWM hlarge hbudget hn hseen hcLevel hc hside (hcRange u hu)
  refine ⟨u, hu, g, hg, hgBound, p, q, hp, hq, ?_, ?_, hpq, hspan, hmean⟩
  · exact (Finset.mem_Ico.mp (hA hu)).1.trans hup
  · have hvhi := (Finset.mem_Ico.mp (hA hv)).2
    rw [hvEq] at hqv
    exact hqv.trans_lt hvhi

theorem cluster_half_interval_seed {S : ℕ → Finset ℤ} {A : Finset ℤ}
    {cut left c : ℤ} {a M cLevel d s : ℕ}
    (hd : 16 ≤ d) (hs : 6 * s ≤ d) (hM : 2 ^ d ≤ M)
    (hA : A ⊆ Finset.Ico left (left + M))
    (hdensity : clusterDensity s * M ≤ A.card)
    (hseen : ∀ t ∈ A, ∃ k ≤ a, t ∈ S k)
    (hcLevel : cLevel ≤ a) (hc : c ∈ S cLevel)
    (hside : (c < cut ∧ ∀ t ∈ A, cut ≤ t) ∨ (cut ≤ c ∧ ∀ t ∈ A, t < cut))
    (hcRange : ∀ t ∈ A, |c - t| ≤ 2 * (M : ℤ)) :
    ∃ u ∈ A, ∃ g : ℕ, 0 < g ∧ clusterDensity s * g ≤ 2 ∧ ∃ p q : ℤ,
      (g : ℤ) ∣ p - u ∧ (g : ℤ) ∣ q - u ∧
      left ≤ p ∧ q < left + M ∧ p ≤ q ∧
      clusterDensity s * M / 8 ≤ ((q - p : ℤ) : ℝ) ∧
      ∀ t : ℤ, p ≤ t → t ≤ q → (g : ℤ) ∣ t - u → DyadicMean S cut (a + (s + 16)) t := by
  have hpos := clusterDensity_pos s
  have hone := clusterDensity_le_one s
  have hlarge := cluster_seed_lattice_room hd hs hM
  have hsq : clusterDensity s ^ 2 ≤ clusterDensity s := by nlinarith
  have hmul := mul_le_mul_of_nonneg_right hsq (by positivity : (0 : ℝ) ≤ M)
  have hsize : 2 ≤ clusterDensity s * M := by linarith
  exact dense_half_interval_seed hA hpos hone hsize hdensity hlarge
    (cluster_seed_delay_budget s) (by omega) hseen hcLevel hc hside hcRange

end Erdos790.Upper
