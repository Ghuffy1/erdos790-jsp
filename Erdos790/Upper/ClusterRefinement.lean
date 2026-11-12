import Erdos790.Upper.RefinementBudgets

/-!
# The fixed refinement delay in a cluster
-/

namespace Erdos790.Upper

theorem cluster_refined_dyadic_core {S : ℕ → Finset ℤ}
    {cut u p q b : ℤ} {d s j g M : ℕ}
    (hd : 48 ≤ d) (hs : 6 * s ≤ d) (hM : 2 ^ d ≤ M)
    (hg : 0 < g) (hgBound : clusterDensity s * g ≤ 2)
    (hp : (g : ℤ) ∣ p - u) (hq : (g : ℤ) ∣ q - u)
    (hcore : ∀ x : ℤ, p ≤ x → x ≤ q → (g : ℤ) ∣ x - u → DyadicMean S cut j x)
    (hb : b ∈ S j) (hoff : ¬ (g : ℤ) ∣ b - u)
    (hspan : clusterDensity s ^ 3 * M / 32 ≤ ((q - p : ℤ) : ℝ))
    (hbp : |b - p| ≤ 2 * (M : ℤ)) (hbq : |b - q| ≤ 2 * (M : ℤ)) :
    let g' : ℕ := Int.gcd (g : ℤ) (b - u)
    0 < g' ∧ 2 * g' ≤ g ∧
      ∃ p' q' : ℤ, (g' : ℤ) ∣ p' - u ∧ (g' : ℤ) ∣ q' - u ∧
        p ≤ p' ∧ q' ≤ q ∧ q - p ≤ 4 * (q' - p') ∧
        ∀ x : ℤ, p' ≤ x → x ≤ q' → (g' : ℤ) ∣ x - u →
          DyadicMean S cut (j + (s + 28)) x := by
  have hroomReal := refinement_core_room (clusterDensity_pos s) (clusterDensity_le_one s)
    hgBound hspan (cluster_refinement_lattice_room hd hs hM)
  have hroom : 8 * (g : ℤ) + 8 ≤ q - p := by exact_mod_cast hroomReal
  have hscaleReal := refinement_scale_room (clusterDensity_pos s)
    (by positivity : (0 : ℝ) ≤ M) (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (s + 28))
    hgBound hspan (cluster_refinement_delay_budget s)
  have hscale : 8 * (g : ℤ) * M ≤ (2 : ℤ) ^ (s + 28) * (q - p) := by
    exact_mod_cast hscaleReal
  exact refined_dyadic_core hg (by omega) (cluster_refinement_capacity hgBound).le
    hp hq hcore hb hoff hroom hbp hbq hscale

end Erdos790.Upper
