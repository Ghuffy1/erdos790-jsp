import Erdos790.Upper.ProfileExclusion
import Mathlib.Data.Fintype.BigOperators

/-!
# Binary-word multiplicity within a short cluster of levels
-/

namespace Erdos790.Upper

theorem binary_occurrences_card_le {d start delay R : ℕ} {B : Finset ℕ}
    (occurrences : Finset (ℕ × (Fin d → Fin 2))) (free : Finset (Fin d))
    (fixed : Fin d → Fin 2) (value : (Fin d → Fin 2) → ℕ)
    (hB : RepeatedSumFree R B) (hR : 2 ^ delay ≤ R)
    (hlevels : ∀ p ∈ occurrences, start ≤ p.1 ∧ p.1 < start + delay)
    (hfixed : ∀ p ∈ occurrences, ∀ h, h ∉ free → p.2 h = fixed h)
    (hselected : ∀ p ∈ occurrences, 2 ^ p.1 * value p.2 ∈ B) :
    occurrences.card ≤ 2 ^ free.card := by
  classical
  let profile (p : ℕ × (Fin d → Fin 2)) : free → Fin 2 := fun h => p.2 h.val
  have hinj : Set.InjOn profile ↑occurrences := by
    intro a ha b hb hab
    have hword : a.2 = b.2 := by
      funext h
      by_cases hh : h ∈ free
      · exact congrFun hab ⟨h, hh⟩
      · rw [hfixed a ha h hh, hfixed b hb h hh]
    have hlevel : a.1 = b.1 := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have hgap : b.1 - a.1 ≤ delay := by
          have := hlevels a ha
          have := hlevels b hb
          omega
        exact hB.no_dyadic_repeat (hselected a ha)
          (by simpa only [hword] using hselected b hb) hlt
          ((Nat.pow_le_pow_right (by decide) hgap).trans hR)
      · have hgap : a.1 - b.1 ≤ delay := by
          have := hlevels a ha
          have := hlevels b hb
          omega
        exact hB.no_dyadic_repeat (hselected b hb)
          (by simpa only [hword] using hselected a ha) hgt
          ((Nat.pow_le_pow_right (by decide) hgap).trans hR)
    exact Prod.ext hlevel hword
  have hcard := Finset.card_le_card_of_injOn profile
    (t := Finset.univ) (fun _ _ => Finset.mem_univ _) hinj
  simpa only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_coe] using hcard

theorem selected_profiles_card_le_one {d q Q X j K threshold amplification constant step t : ℕ}
    (C B : Finset ℕ) (allowed : Finset (Fin d)) (fixed : Fin d → Fin 2)
    (words : Finset (Fin d → Fin 2)) (hq : 3 ≤ q) (hX : 0 < X)
    (hC : ∀ x ∈ C, X ≤ x ∧ x < 2 * X)
    (hcover : SumCover C K threshold) (hB : RepeatedSumFree (q ^ 6) B)
    (hthreshold : 2 * threshold ≤ q ^ 2 * X)
    (hdata : ∀ H ∈ allowed, ∃ i, i ≤ j ∧ K ≤ (levelSlice i C B).card ∧
      q ^ 2 * X ≤ Q * 2 ^ (j - i) * q ^ H.val ∧
      Q * 2 ^ (j - i) * q ^ H.val ≤ q ^ 4 * X)
    (hfixed : ∀ a ∈ words, ∀ h, h ∉ allowed → a h = fixed h)
    (hselected : ∀ a ∈ words, 2 ^ j * nativeTentValue amplification q constant Q step t a ∈ B) :
    words.card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro a ha b hb
  exact selected_profile_unique C B allowed a b hq hX hC hcover hB hthreshold hdata
    (fun h hh => (hfixed a ha h hh).trans (hfixed b hb h hh).symm)
    (hselected a ha) (hselected b hb)

end Erdos790.Upper
