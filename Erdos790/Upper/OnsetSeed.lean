import Erdos790.Upper.DensityOnset
import Erdos790.Upper.HalfIntervalSeed
import Mathlib.Algebra.Order.Floor.Semiring

/-!
# From the first dense coordinate union to its lattice of mixed means
-/

namespace Erdos790.Upper

theorem exists_real_density_onset {d last : ℕ} (density : ℝ)
    (occurrences : Finset (ℕ × ℤ × (Fin d → Fin 2)))
    (hlevels : ∀ p ∈ occurrences, p.1 ≤ last)
    (hdense : density ≤ ((occurrences.image (fun p => p.2.1)).card : ℝ)) :
    ∃ a ≤ last, density ≤ ((cumulativeCoordinates occurrences a).card : ℝ) ∧
      ∀ j < a, ((cumulativeCoordinates occurrences j).card : ℝ) < density := by
  obtain ⟨a, ha, hdensity, hbefore⟩ := exists_density_onset occurrences hlevels
    (Nat.ceil_le.mpr hdense)
  refine ⟨a, ha, (Nat.le_ceil density).trans (by exact_mod_cast hdensity), ?_⟩
  intro j hj
  by_contra hnot
  exact (not_le_of_gt (hbefore j hj)) (Nat.ceil_le.mpr (le_of_not_gt hnot))

theorem before_onset_count_real {d start delay R a : ℕ} {B : Finset ℕ}
    (density : ℝ) (occurrences : Finset (ℕ × ℤ × (Fin d → Fin 2)))
    (free : Finset (Fin d)) (fixed : Fin d → Fin 2)
    (value : ℤ → (Fin d → Fin 2) → ℕ) (hDensity : 0 ≤ density)
    (hB : RepeatedSumFree R B) (hR : 2 ^ delay ≤ R)
    (hlevels : ∀ p ∈ occurrences, start ≤ p.1 ∧ p.1 < start + delay)
    (hfixed : ∀ p ∈ occurrences, ∀ h, h ∉ free → p.2.2 h = fixed h)
    (hselected : ∀ p ∈ occurrences, 2 ^ p.1 * value p.2.1 p.2.2 ∈ B)
    (honset : ∀ j < a, ((cumulativeCoordinates occurrences j).card : ℝ) < density) :
    ((occurrences.filter (fun p => p.1 < a)).card : ℝ) ≤ (2 : ℝ) ^ free.card * density := by
  classical
  by_cases ha : a = 0
  · simp only [ha, Nat.not_lt_zero, Finset.filter_false, Finset.card_empty, Nat.cast_zero]
    positivity
  have haprev : a - 1 < a := by omega
  have hcoordinates : ∀ p ∈ occurrences.filter (fun p => p.1 < a),
      p.2.1 ∈ cumulativeCoordinates occurrences (a - 1) := by
    intro p hp
    obtain ⟨hp, hpa⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_image.mpr ⟨p, Finset.mem_filter.mpr ⟨hp, by omega⟩, rfl⟩
  have hprefix := coordinate_occurrences_card_le
    (occurrences.filter (fun p => p.1 < a)) (cumulativeCoordinates occurrences (a - 1))
    free fixed value hB hR
    (fun p hp => hlevels p (Finset.mem_filter.mp hp).1) hcoordinates
    (fun p hp h hh => hfixed p (Finset.mem_filter.mp hp).1 h hh)
    (fun p hp => hselected p (Finset.mem_filter.mp hp).1)
  have hreal : ((occurrences.filter (fun p => p.1 < a)).card : ℝ) ≤
      (2 : ℝ) ^ free.card * (cumulativeCoordinates occurrences (a - 1)).card := by
    exact_mod_cast hprefix
  exact hreal.trans (mul_le_mul_of_nonneg_left (honset (a - 1) haprev).le (by positivity))

theorem onset_lattice_seed {wordSize d s a M cLevel : ℕ} {S : ℕ → Finset ℤ}
    {cut left c : ℤ} (occurrences : Finset (ℕ × ℤ × (Fin wordSize → Fin 2)))
    (hd : 16 ≤ d) (hs : 6 * s ≤ d) (hM : 2 ^ d ≤ M)
    (hinterval : ∀ p ∈ occurrences, left ≤ p.2.1 ∧ p.2.1 < left + M)
    (hselected : ∀ p ∈ occurrences, p.2.1 ∈ S p.1)
    (hdensity : clusterDensity s * M ≤ (cumulativeCoordinates occurrences a).card)
    (hcLevel : cLevel ≤ a) (hc : c ∈ S cLevel)
    (hside : (c < cut ∧ ∀ p ∈ occurrences, cut ≤ p.2.1) ∨
      (cut ≤ c ∧ ∀ p ∈ occurrences, p.2.1 < cut))
    (hcRange : ∀ p ∈ occurrences, |c - p.2.1| ≤ 2 * (M : ℤ)) :
    ∃ u ∈ cumulativeCoordinates occurrences a, ∃ g : ℕ,
      0 < g ∧ clusterDensity s * g ≤ 2 ∧ ∃ p q : ℤ,
      (g : ℤ) ∣ p - u ∧ (g : ℤ) ∣ q - u ∧
      left ≤ p ∧ q < left + M ∧ p ≤ q ∧
      clusterDensity s * M / 8 ≤ ((q - p : ℤ) : ℝ) ∧
      ∀ t : ℤ, p ≤ t → t ≤ q → (g : ℤ) ∣ t - u → DyadicMean S cut (a + (s + 16)) t := by
  have hsupport : ∀ t ∈ cumulativeCoordinates occurrences a,
      ∃ p ∈ occurrences, p.1 ≤ a ∧ p.2.1 = t := by
    intro t ht
    obtain ⟨p, hp, hpt⟩ := Finset.mem_image.mp ht
    obtain ⟨hp, hpa⟩ := Finset.mem_filter.mp hp
    exact ⟨p, hp, hpa, hpt⟩
  have hA : cumulativeCoordinates occurrences a ⊆ Finset.Ico left (left + M) := by
    intro t ht
    obtain ⟨p, hp, _, rfl⟩ := hsupport t ht
    exact Finset.mem_Ico.mpr (hinterval p hp)
  have hseen : ∀ t ∈ cumulativeCoordinates occurrences a, ∃ k ≤ a, t ∈ S k := by
    intro t ht
    obtain ⟨p, hp, hpa, rfl⟩ := hsupport t ht
    exact ⟨p.1, hpa, hselected p hp⟩
  have hsideA : (c < cut ∧ ∀ t ∈ cumulativeCoordinates occurrences a, cut ≤ t) ∨
      (cut ≤ c ∧ ∀ t ∈ cumulativeCoordinates occurrences a, t < cut) := by
    rcases hside with ⟨hleft, hAleft⟩ | ⟨hright, hAright⟩
    · refine Or.inl ⟨hleft, ?_⟩
      intro t ht
      obtain ⟨p, hp, _, rfl⟩ := hsupport t ht
      exact hAleft p hp
    · refine Or.inr ⟨hright, ?_⟩
      intro t ht
      obtain ⟨p, hp, _, rfl⟩ := hsupport t ht
      exact hAright p hp
  have hbound : ∀ t ∈ cumulativeCoordinates occurrences a, |c - t| ≤ 2 * (M : ℤ) := by
    intro t ht
    obtain ⟨p, hp, _, rfl⟩ := hsupport t ht
    exact hcRange p hp
  exact cluster_half_interval_seed hd hs hM hA hdensity hseen hcLevel hc hsideA hbound

end Erdos790.Upper
