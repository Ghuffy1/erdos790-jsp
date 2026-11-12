import Mathlib.Algebra.Order.Ring.Int
import Lean.Elab.Tactic.Omega

/-!
# Rounding the central half of an integer interval to a lattice
-/

namespace Erdos790.Upper

def latticeFloor (g u x : ℤ) : ℤ := x - (x - u) % g

def latticeCeil (g u x : ℤ) : ℤ := x + (u - x) % g

theorem latticeFloor_spec {g u x : ℤ} (hg : 0 < g) :
    latticeFloor g u x ≤ x ∧ x < latticeFloor g u x + g ∧
      g ∣ latticeFloor g u x - u := by
  have hlo := Int.emod_nonneg (x - u) (ne_of_gt hg)
  have hhi := Int.emod_lt_of_pos (x - u) hg
  refine ⟨by dsimp [latticeFloor]; omega, by dsimp [latticeFloor]; omega, ?_⟩
  refine ⟨(x - u) / g, ?_⟩
  have := Int.emod_add_mul_ediv (x - u) g
  dsimp [latticeFloor]
  omega

theorem latticeCeil_spec {g u x : ℤ} (hg : 0 < g) :
    x ≤ latticeCeil g u x ∧ latticeCeil g u x < x + g ∧
      g ∣ latticeCeil g u x - u := by
  have hlo := Int.emod_nonneg (u - x) (ne_of_gt hg)
  have hhi := Int.emod_lt_of_pos (u - x) hg
  refine ⟨by dsimp [latticeCeil]; omega, by dsimp [latticeCeil]; omega, ?_⟩
  refine ⟨-((u - x) / g), ?_⟩
  have := Int.emod_add_mul_ediv (u - x) g
  dsimp [latticeCeil]
  rw [mul_neg]
  omega

theorem central_lattice_interval {g u p q : ℤ} (hg : 0 < g)
    (hroom : 8 * g + 8 ≤ q - p) :
    ∃ p' q' : ℤ, g ∣ p' - u ∧ g ∣ q' - u ∧
      p ≤ p' ∧ q' ≤ q ∧
      q - p ≤ 4 * (p' - p) ∧ q - p ≤ 4 * (q - q') ∧
      q - p ≤ 4 * (q' - p') := by
  let h := (q - p + 3) / 4
  let p' := latticeCeil g u (p + h)
  let q' := latticeFloor g u (q - h)
  obtain ⟨hpp, hpbound, hpclass⟩ := latticeCeil_spec (u := u) (x := p + h) hg
  obtain ⟨hqq, hqbound, hqclass⟩ := latticeFloor_spec (u := u) (x := q - h) hg
  refine ⟨p', q', hpclass, hqclass, ?_, ?_, ?_, ?_, ?_⟩ <;>
    dsimp [p', q', h] at * <;> omega

end Erdos790.Upper
