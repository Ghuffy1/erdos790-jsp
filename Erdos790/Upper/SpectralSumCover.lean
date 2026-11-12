import Erdos790.Upper.CoefficientCover
import Erdos790.Upper.GeometricCharacters

/-!
# Positive sums from a phase-separated fiber

This is the Fourier-to-integer-sum step of the base construction. The
phase-separated indices and their cardinality are explicit hypotheses.
-/

namespace Erdos790.Upper

theorem phase_separated_fiber_sums_of_fintype {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : Finset ℕ} {M X B J k : ℕ}
    [NeZero M] {p : ℝ} (value : ι → ℕ)
    (hX : 0 < X) (hp : 0 < p) (hB : 100 * p ≤ B) (hn : Fintype.card ι ≤ J)
    (hM : M ∈ S) (hS : ∀ x ∈ S, X ≤ x ∧ x < 2 * X)
    (hvalue : ∀ i, value i ∈ S)
    (hsmall : (M : ℝ) * (1 / 200 : ℝ) ^ k < 1)
    (hphase : ∀ a : ZMod M, a ≠ 0 → ∃ good : Finset ι,
      good.card = k ∧ ∀ i ∈ good,
        4 / p ≤ ‖1 - ZMod.stdAddChar (-((value i : ZMod M) * a))‖) :
    ∀ N : ℕ, 2 * J * B * X ≤ N → ∃ T : List ℕ,
      (∀ x ∈ T, x ∈ S) ∧ T.sum = N ∧ T.length ≤ N / X := by
  have hBreal : (0 : ℝ) < B := lt_of_lt_of_le (by positivity) hB
  have hBpos : 0 < B := by exact_mod_cast hBreal
  have hcover : ∀ N : ℕ, ∃ c : ι → Fin B,
      Nat.ModEq M (coefficientSum value c) N := by
    apply coefficient_residue_of_good value hBpos (by norm_num) hsmall
    intro a ha
    obtain ⟨good, hcard, hgood⟩ := hphase a ha
    refine ⟨good, hcard, ?_⟩
    intro i hi
    have hnorm := character_factor_bound_of_chord
      ((value i : ZMod M) * a) hp hB (hgood i hi)
    simpa only [mul_assoc, div_eq_mul_inv, one_mul] using hnorm
  have hbase := coefficient_coverage_gives_sums value hM
    (Nat.pos_of_ne_zero (NeZero.ne M)) hX (fun x hx => (hS x hx).1) hvalue
    (fun i => (hS (value i) (hvalue i)).2.le) hcover
  intro N hN
  apply hbase N
  calc
    Fintype.card ι * (B * (2 * X)) ≤ J * (B * (2 * X)) := Nat.mul_le_mul_right _ hn
    _ = 2 * J * B * X := by ring
    _ ≤ N := hN

theorem phase_separated_fiber_sums {S : Finset ℕ} {M X B J n k : ℕ}
    [NeZero M] {p : ℝ} (value : Fin n → ℕ)
    (hX : 0 < X) (hp : 0 < p) (hB : 100 * p ≤ B) (hn : n ≤ J)
    (hM : M ∈ S) (hS : ∀ x ∈ S, X ≤ x ∧ x < 2 * X)
    (hvalue : ∀ i, value i ∈ S)
    (hsmall : (M : ℝ) * (1 / 200 : ℝ) ^ k < 1)
    (hphase : ∀ a : ZMod M, a ≠ 0 → ∃ good : Finset (Fin n),
      good.card = k ∧ ∀ i ∈ good,
        4 / p ≤ ‖1 - ZMod.stdAddChar (-((value i : ZMod M) * a))‖) :
    ∀ N : ℕ, 2 * J * B * X ≤ N → ∃ T : List ℕ,
      (∀ x ∈ T, x ∈ S) ∧ T.sum = N ∧ T.length ≤ N / X :=
  phase_separated_fiber_sums_of_fintype value hX hp hB (by simpa using hn)
    hM hS hvalue hsmall hphase

end Erdos790.Upper
