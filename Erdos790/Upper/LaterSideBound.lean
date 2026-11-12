import Erdos790.Upper.CorePhases
import Erdos790.Upper.HalfIntervalSeed
import Erdos790.Upper.SelectionUnion

/-!
# Counting a selected family on the later side of a cell
-/

namespace Erdos790.Upper

theorem later_side_mass_bound
    {A S : ℕ → Finset ℤ} {cut left c : ℤ} {d s width M start stop cLevel : ℕ}
    (hd : 48 ≤ d) (hs : 6 * s ≤ d) (hwidth : 12 * width ≤ d)
    (hwidthPos : 0 < width) (hM : 2 ^ d ≤ M)
    (hstart : start ≤ stop) (hshort : stop - start ≤ width)
    (hpoint : ∀ j < stop, (S j).card ≤ M)
    (hsubset : ∀ j < stop, S j ⊆ A j)
    (hinterval : ∀ j < stop, S j ⊆ Finset.Ico left (left + M))
    (hforbidden : ∀ j < stop, ∀ x ∈ S j, ¬DyadicMean A cut j x)
    (hcount : ∀ x,
      ((selectionIncidences S start stop).filter (fun p => p.2 = x)).card ≤ 2 ^ s)
    (hcLevel : cLevel ≤ start) (hc : c ∈ A cLevel)
    (hside : (c < cut ∧ ∀ j, start ≤ j → j < stop → ∀ x ∈ S j, cut ≤ x) ∨
      (cut ≤ c ∧ ∀ j, start ≤ j → j < stop → ∀ x ∈ S j, x < cut))
    (hcRange : ∀ j, start ≤ j → j < stop → ∀ x ∈ S j, |c - x| ≤ 2 * (M : ℤ)) :
    (selectionMass S start stop : ℝ) ≤
      (M : ℝ) * ((2 : ℝ) ^ s * clusterDensity s + 600 * (s + 1 : ℝ) ^ 2) := by
  classical
  have hη := clusterDensity_pos s
  have hnonneg : 0 ≤ (M : ℝ) * ((2 : ℝ) ^ s * clusterDensity s +
      600 * (s + 1 : ℝ) ^ 2) := by positivity
  by_cases heq : start = stop
  · subst stop
    simpa only [selectionMass, Nat.sub_self, Finset.range_zero, Finset.sum_empty,
      Nat.cast_zero] using hnonneg
  have hlt : start < stop := by omega
  have hmass (finish : ℕ) (hfinish : finish ≤ stop) :
      (selectionMass S start finish : ℝ) ≤
        (2 : ℝ) ^ s * (selectionCoordinateUnion S start finish).card := by
    exact_mod_cast selectionMass_le_union hfinish hcount
  by_cases hdense : clusterDensity s * M ≤
      ((selectionCoordinateUnion S start stop).card : ℝ)
  · have hexists : ∃ a, start ≤ a ∧ a < stop ∧ clusterDensity s * M ≤
        ((selectionCoordinateUnion S start (a + 1)).card : ℝ) := by
      refine ⟨stop - 1, by omega, by omega, ?_⟩
      simpa only [show stop - 1 + 1 = stop by omega] using hdense
    obtain ⟨a, haStart, haStop, haDense, hbefore⟩ := first_bad_level
      (fun a => clusterDensity s * M ≤
        ((selectionCoordinateUnion S start (a + 1)).card : ℝ)) hexists
    have hpreCard : ((selectionCoordinateUnion S start a).card : ℝ) ≤
        clusterDensity s * M := by
      by_cases heq : a = start
      · subst a
        simp only [selectionCoordinateUnion_self, Finset.card_empty, Nat.cast_zero]
        positivity
      have haPred : start ≤ a - 1 := by omega
      have hsmall := not_le.mp (hbefore (a - 1) haPred (by omega))
      simpa only [show a - 1 + 1 = a by omega] using hsmall.le
    have hprefix : (selectionMass S start a : ℝ) ≤
        (2 : ℝ) ^ s * (clusterDensity s * M) :=
      (hmass a haStop.le).trans (mul_le_mul_of_nonneg_left hpreCard (by positivity))
    have htail : (selectionMass S a stop : ℝ) ≤ 600 * (s + 1 : ℝ) ^ 2 * M := by
      by_cases hdelay : stop ≤ a + (s + 16)
      · have htailNat : selectionMass S a stop ≤ (s + 16) * M :=
          (selectionMass_le hpoint).trans (Nat.mul_le_mul_right M (by omega))
        have htailReal : (selectionMass S a stop : ℝ) ≤ (s + 16 : ℝ) * M := by
          exact_mod_cast htailNat
        have hcharge : (s + 16 : ℝ) ≤ 600 * (s + 1 : ℝ) ^ 2 := by
          have := Nat.cast_nonneg (α := ℝ) s
          nlinarith [sq_nonneg (s : ℝ)]
        exact htailReal.trans (mul_le_mul_of_nonneg_right hcharge (by positivity))
      have hseedTime : a + (s + 16) < stop := by omega
      let U := selectionCoordinateUnion S start (a + 1)
      have hU : U ⊆ Finset.Ico left (left + M) := by
        intro x hx
        obtain ⟨j, hjStart, hjStop, hx⟩ := mem_selectionCoordinateUnion.mp hx
        exact hinterval j (by omega) hx
      have hseen : ∀ x ∈ U, ∃ j ≤ a, x ∈ A j := by
        intro x hx
        obtain ⟨j, hjStart, hjStop, hx⟩ := mem_selectionCoordinateUnion.mp hx
        exact ⟨j, by omega, hsubset j (by omega) hx⟩
      have hsideU : (c < cut ∧ ∀ x ∈ U, cut ≤ x) ∨
          (cut ≤ c ∧ ∀ x ∈ U, x < cut) := by
        rcases hside with ⟨hcCut, hselected⟩ | ⟨hcCut, hselected⟩
        · refine Or.inl ⟨hcCut, ?_⟩
          intro x hx
          obtain ⟨j, hjStart, hjStop, hx⟩ := mem_selectionCoordinateUnion.mp hx
          exact hselected j hjStart (by omega) x hx
        · refine Or.inr ⟨hcCut, ?_⟩
          intro x hx
          obtain ⟨j, hjStart, hjStop, hx⟩ := mem_selectionCoordinateUnion.mp hx
          exact hselected j hjStart (by omega) x hx
      have hrangeU : ∀ x ∈ U, |c - x| ≤ 2 * (M : ℤ) := by
        intro x hx
        obtain ⟨j, hjStart, hjStop, hx⟩ := mem_selectionCoordinateUnion.mp hx
        exact hcRange j hjStart (by omega) x hx
      obtain ⟨u, hu, g, hg, hgBound, p, q, hp, hq, hleft, hright, hpq, hspan, hcore⟩ :=
        cluster_half_interval_seed (by omega : 16 ≤ d) hs hM hU haDense hseen
          (hcLevel.trans haStart) hc hsideU hrangeU
      have hafter := seeded_later_mass_bound hd hs hwidth hwidthPos hM hg hgBound
        hseedTime.le (by omega) hp hq hpq hleft hright hspan hcore
        hpoint hsubset hinterval hforbidden
      have hdelayNat : selectionMass S a (a + (s + 16)) ≤ (s + 16) * M := by
        have h := selectionMass_le (S := S) (start := a) (stop := a + (s + 16))
          (fun j hj => hpoint j (by omega))
        simpa only [Nat.add_sub_cancel_left] using h
      have hcombined : selectionMass S a stop ≤
          ((s + 16) + (s + 16) * (s + 31)) * M := by
        rw [selectionMass_split S (show a ≤ a + (s + 16) by omega) hseedTime.le]
        nlinarith
      have hcombinedReal : (selectionMass S a stop : ℝ) ≤
          ((s + 16 : ℝ) + (s + 16 : ℝ) * (s + 31 : ℝ)) * M := by
        exact_mod_cast hcombined
      have hcharge : (s + 16 : ℝ) + (s + 16 : ℝ) * (s + 31 : ℝ) ≤
          600 * (s + 1 : ℝ) ^ 2 := by
        have := Nat.cast_nonneg (α := ℝ) s
        nlinarith [sq_nonneg (s : ℝ)]
      exact hcombinedReal.trans (mul_le_mul_of_nonneg_right hcharge (by positivity))
    have hsplit : (selectionMass S start stop : ℝ) =
        (selectionMass S start a : ℝ) + (selectionMass S a stop : ℝ) := by
      exact_mod_cast selectionMass_split S haStart haStop.le
    rw [hsplit]
    nlinarith
  · have hsmall : ((selectionCoordinateUnion S start stop).card : ℝ) ≤
        clusterDensity s * M := (not_le.mp hdense).le
    have htotal := (hmass stop le_rfl).trans
      (mul_le_mul_of_nonneg_left hsmall (by positivity : 0 ≤ (2 : ℝ) ^ s))
    nlinarith [show (0 : ℝ) ≤ 600 * (s + 1 : ℝ) ^ 2 * M by positivity]

end Erdos790.Upper
