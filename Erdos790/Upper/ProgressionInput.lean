import OAI.Combinatorics.Progressions.Model
import Erdos790.Upper.AffineCounting
import Erdos790.Upper.QuantitativeDecay
import Erdos790.Upper.TentParameters
import Erdos790.Upper.HeavyLevels

/-!
# The quantitative progression input for the distinct-summand lift

The quantitative density statement and its definitions are from the pinned
OpenAI mathematics development. The bridge to centered pairs is proved here.
-/

open Filter

namespace Erdos790.Upper

theorem threeTermExtremal_of_extremalNumber {M k : ℕ}
    (hupper : OAI.Erdos3.extremalNumber 3 M ≤ k) : ThreeTermExtremalBound M k := by
  classical
  intro T hT hfree
  have hAPfree : OAI.Erdos3.APFree (T : Set ℕ) 3 := by
    intro hAP
    obtain ⟨a, q, hq, hmem⟩ := hAP
    have hx : a ∈ T := by simpa using hmem 0 (by decide)
    have hz : a + q ∈ T := by simpa using hmem 1 (by decide)
    have hy : a + 2 * q ∈ T := by simpa using hmem 2 (by decide)
    have hp : (a, a + q) ∈ natProgressionPairs T := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_product.mpr ⟨hx, hz⟩, by omega, a + 2 * q, hy, ?_⟩
      omega
    simp only [hfree, Finset.notMem_empty] at hp
  have hcard : T.card ≤ OAI.Erdos3.extremalNumber 3 M := by
    apply Finset.le_sup
    exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hT, hAPfree⟩
  exact hcard.trans hupper

namespace AuxiliaryParameters

def liftIntervalLength (d : ℕ) : ℕ := 2 ^ (100 * d)

theorem liftIntervalLength_pos (d : ℕ) : 0 < liftIntervalLength d := by
  unfold liftIntervalLength
  positivity

theorem eventual_center_rich_from_quantitative
    (hquantitative : OAI.Erdos3.QuantitativeDensityBound 3) :
    ∀ᶠ d : ℕ in atTop,
      CenterRich (arityLimit d) (liftIntervalLength d / levelCount d)
        (Finset.Icc 1 (liftIntervalLength d : ℤ)) := by
  obtain ⟨C, c, η, hC, hc, hη, hbound⟩ := hquantitative
  have hdecay := quantitative_density_polynomial_decay
    (OAI.Erdos3.extremalNumber 3) hC hc hη hbound 56 (by norm_num) 2
  filter_upwards [hdecay, eventually_ge_atTop 1] with d hdecay hd
  let M := 2 ^ d
  let D := 2 ^ (99 * d)
  let k := M / (8 * levelCount d)
  have hden : 0 < 8 * levelCount d := by have h := levelCount_pos d; positivity
  have hcoefficient : 8 * levelCount d ≤ 56 * (d + 1) ^ 2 := by
    unfold levelCount
    nlinarith
  have hdecayNat : 56 * (d + 1) ^ 2 * OAI.Erdos3.extremalNumber 3 M ≤ M := by
    exact_mod_cast hdecay
  have hextremal : OAI.Erdos3.extremalNumber 3 M ≤ k := by
    apply (Nat.le_div_iff_mul_le hden).mpr
    have h := (Nat.mul_le_mul_right (OAI.Erdos3.extremalNumber 3 M) hcoefficient).trans hdecayNat
    simpa only [Nat.mul_comm] using h
  have hsmall : 8 * levelCount d * k ≤ M := by
    simpa only [k, Nat.mul_comm] using Nat.div_mul_le_self M (8 * levelCount d)
  have hscale : 2 * (arityLimit d + 1) * M ≤ D := by
    have hone : 1 ≤ 2 ^ (36 * d) := Nat.one_le_pow _ _ (by decide)
    have hterm : arityLimit d + 1 ≤ 2 * 2 ^ (36 * d) := by unfold arityLimit; omega
    calc
      _ ≤ 2 * (2 * 2 ^ (36 * d)) * M :=
        Nat.mul_le_mul_right M (Nat.mul_le_mul_left 2 hterm)
      _ = 4 * 2 ^ (36 * d) * 2 ^ d := by dsimp [M]; ring
      _ = 2 ^ (37 * d + 2) := by
        rw [pow_add, show 37 * d = 36 * d + d by omega, pow_add]
        norm_num
        ring
      _ ≤ 2 ^ (99 * d) := Nat.pow_le_pow_right (by decide) (by omega)
  have hN : liftIntervalLength d = M * D := by
    dsimp [liftIntervalLength, M, D]
    rw [← pow_add]
    congr 1
    omega
  exact centerRich_of_extremal_bound (by dsimp [M]; positivity)
    (by dsimp [D]; positivity) (levelCount_pos d) hN hsmall hscale
    (threeTermExtremal_of_extremalNumber hextremal)

end AuxiliaryParameters
end Erdos790.Upper
