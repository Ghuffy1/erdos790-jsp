import Erdos790.Upper.LatticeCoordinates
import Erdos790.Upper.StablePeriodBudgets

/-!
# The quantitative three-times-the-half-size bound for a stable period
-/

namespace Erdos790.Upper

theorem cluster_stable_lattice_period
    {A S : ℕ → Finset ℤ} {cut left u p q : ℤ} {d s width start k M g : ℕ}
    (hd : 48 ≤ d) (hs : 6 * s ≤ d) (hwidth : 12 * width ≤ d) (hwidthPos : 0 < width)
    (hM : 2 ^ d ≤ M) (hg : 0 < g) (hk : k ≤ width)
    (hp : (g : ℤ) ∣ p - u) (hq : (g : ℤ) ∣ q - u)
    (hpq : p ≤ q) (hleft : left ≤ p) (hright : q < left + M)
    (hgBound : clusterDensity s * g ≤ 2)
    (hspan : clusterDensity s ^ 3 * M / 32 ≤ ((q - p : ℤ) : ℝ))
    (hcore : ∀ x : ℤ, p ≤ x → x ≤ q → (g : ℤ) ∣ x - u → DyadicMean A cut start x)
    (hsubset : ∀ i < k, S (start + i) ⊆ A (start + i))
    (hinterval : ∀ i < k, S (start + i) ⊆ Finset.Ico left (left + M))
    (hclass : ∀ i < k, ∀ x ∈ S (start + i), (g : ℤ) ∣ x - u)
    (hforbidden : ∀ i < k, ∀ x ∈ S (start + i), ¬DyadicMean A cut (start + i) x) :
    (∑ i ∈ Finset.range k, (S (start + i)).card) ≤ 3 * M := by
  let T := latticeInterval u g p q
  let C := fun i => latticeCoordinates u g (S (start + i))
  let ambient := latticeInterval u g left (left + M - 1)
  have hgInt : (0 : ℤ) < g := by exact_mod_cast hg
  have hTsubset : T ⊆ ambient := latticeInterval_mono hgInt hleft (by omega)
  have hcoreSize : clusterDensity s ^ 4 * M / 64 ≤ (T.card : ℝ) :=
    lattice_core_card_lower (clusterDensity_pos s) hg hpq hp hq hgBound hspan
  obtain ⟨hm, hroom, herror⟩ := stable_component_budget hd hs hwidth hwidthPos hM hcoreSize hk
    (Finset.card_le_card hTsubset)
  have hmean : ∀ x ∈ T, DyadicMean A cut start (u + (g : ℤ) * x) :=
    lattice_core_means hg hp hq hcore
  have hC : ∀ i < k, ∀ y ∈ C i, u + (g : ℤ) * y ∈ A (start + i) := by
    intro i hi y hy
    exact hsubset i hi (latticeCoordinates_member (hclass i hi) hy)
  have hnotMean : ∀ i < k, ∀ y ∈ C i,
      ¬DyadicMean A cut (start + i) (u + (g : ℤ) * y) := by
    intro i hi y hy
    exact hforbidden i hi _ (latticeCoordinates_member (hclass i hi) hy)
  have hCinterval : ∀ i < k, C i ⊆ ambient := by
    intro i hi
    exact latticeCoordinates_subset_interval hgInt (hinterval i hi)
  have hperiod : (∑ i ∈ Finset.range k, (C i).card) ≤ 3 * ambient.card := by
    exact propagated_lattice_period_three_mul_bound
      (latticeInterval_nonempty hgInt hpq) (intervalCovered_Icc _ _) hm hroom
      hmean hC hnotMean hTsubset hCinterval herror
  have hambient : ambient.card ≤ M := latticeInterval_card_le hgInt
    ((Nat.two_pow_pos d).trans_le hM)
  calc
    (∑ i ∈ Finset.range k, (S (start + i)).card) =
        ∑ i ∈ Finset.range k, (C i).card := by
          apply Finset.sum_congr rfl
          intro i hi
          exact (latticeCoordinates_card u g (S (start + i))
            (hclass i (Finset.mem_range.mp hi))).symm
    _ ≤ 3 * ambient.card := hperiod
    _ ≤ 3 * M := Nat.mul_le_mul_left _ hambient

end Erdos790.Upper
