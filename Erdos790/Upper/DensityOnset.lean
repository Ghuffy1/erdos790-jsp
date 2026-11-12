import Erdos790.Upper.CoordinateMultiplicity
import Mathlib.Data.Finset.Max

/-!
# The first level at which the coordinate union reaches a density threshold
-/

namespace Erdos790.Upper

def cumulativeCoordinates {d : ℕ} (occurrences : Finset (ℕ × ℤ × (Fin d → Fin 2)))
    (level : ℕ) : Finset ℤ :=
  (occurrences.filter (fun p => p.1 ≤ level)).image (fun p => p.2.1)

theorem cumulativeCoordinates_mono {d a b : ℕ}
    (occurrences : Finset (ℕ × ℤ × (Fin d → Fin 2))) (hab : a ≤ b) :
    cumulativeCoordinates occurrences a ⊆ cumulativeCoordinates occurrences b := by
  intro t ht
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ht
  obtain ⟨hp, hpa⟩ := Finset.mem_filter.mp hp
  exact Finset.mem_image.mpr ⟨p, Finset.mem_filter.mpr ⟨hp, hpa.trans hab⟩, rfl⟩

theorem exists_density_onset {d last threshold : ℕ}
    (occurrences : Finset (ℕ × ℤ × (Fin d → Fin 2)))
    (hlevels : ∀ p ∈ occurrences, p.1 ≤ last)
    (hdense : threshold ≤ (occurrences.image (fun p => p.2.1)).card) :
    ∃ a ≤ last, threshold ≤ (cumulativeCoordinates occurrences a).card ∧
      ∀ j < a, (cumulativeCoordinates occurrences j).card < threshold := by
  classical
  let candidates := (Finset.range (last + 1)).filter
    (fun j => threshold ≤ (cumulativeCoordinates occurrences j).card)
  have hlast : cumulativeCoordinates occurrences last = occurrences.image (fun p => p.2.1) := by
    unfold cumulativeCoordinates
    rw [Finset.filter_eq_self.mpr hlevels]
  have hnonempty : candidates.Nonempty :=
    ⟨last, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), by simpa only [hlast] using hdense⟩⟩
  let a := candidates.min' hnonempty
  have ha : a ∈ candidates := Finset.min'_mem candidates hnonempty
  obtain ⟨haRange, haDense⟩ := Finset.mem_filter.mp ha
  have haLast : a ≤ last := by have := Finset.mem_range.mp haRange; omega
  refine ⟨a, haLast, haDense, ?_⟩
  intro j hja
  by_contra hnot
  have hj : j ∈ candidates :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), by omega⟩
  have hmin : a ≤ j := Finset.min'_le candidates j hj
  omega

theorem before_onset_count {d start delay R a threshold : ℕ} {B : Finset ℕ}
    (occurrences : Finset (ℕ × ℤ × (Fin d → Fin 2)))
    (free : Finset (Fin d)) (fixed : Fin d → Fin 2)
    (value : ℤ → (Fin d → Fin 2) → ℕ)
    (hB : RepeatedSumFree R B) (hR : 2 ^ delay ≤ R)
    (hlevels : ∀ p ∈ occurrences, start ≤ p.1 ∧ p.1 < start + delay)
    (hfixed : ∀ p ∈ occurrences, ∀ h, h ∉ free → p.2.2 h = fixed h)
    (hselected : ∀ p ∈ occurrences, 2 ^ p.1 * value p.2.1 p.2.2 ∈ B)
    (honset : ∀ j < a, (cumulativeCoordinates occurrences j).card < threshold) :
    (occurrences.filter (fun p => p.1 < a)).card ≤ 2 ^ free.card * (threshold - 1) := by
  classical
  by_cases ha : a = 0
  · simp only [ha, Nat.not_lt_zero, Finset.filter_false, Finset.card_empty]
    exact Nat.zero_le _
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
  exact hprefix.trans (Nat.mul_le_mul_left _ (by have := honset (a - 1) haprev; omega))

end Erdos790.Upper
