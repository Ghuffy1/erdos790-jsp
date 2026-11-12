import Erdos790.Upper.CellMass
import Erdos790.Upper.DyadicCells

/-!
# The full recursive mass bound for a selected coordinate family
-/

namespace Erdos790.Upper

theorem recursive_occurrence_bound {d R start width : ℕ} {B : Finset ℕ}
    (value : ℤ → (Fin d → Fin 2) → ℕ)
    (hd : 48 ≤ d) (hwidth : 12 * width ≤ d) (hwidthPos : 0 < width)
    (hB : RepeatedSumFree R B) (hR : 2 ^ width ≤ R) :
    ∀ s (free : Finset (Fin d)) (fixed : Fin d → Fin 2)
      (E : Finset (ℕ × ℤ × (Fin d → Fin 2))) (left depth : ℕ),
      free.card = s → 6 * s ≤ d →
      (∀ H ∈ free, d + H.val + 1 ≤ depth) → 2 ^ depth ∣ left →
      (∀ p ∈ E, (left : ℤ) ≤ p.2.1 ∧ p.2.1 < (left : ℤ) + (2 ^ depth : ℕ)) →
      (∀ p ∈ E, start ≤ p.1 ∧ p.1 < start + width) →
      (∀ j t a b, (j, t, a) ∈ E → (j, t, b) ∈ E → a = b) →
      (∀ p ∈ E, ∀ h, h ∉ free → p.2.2 h = fixed h) →
      (∀ p ∈ E, 2 ^ p.1 * value p.2.1 p.2.2 ∈ B) → MixedExclusion free E →
      (E.card : ℝ) ≤ (2 : ℝ) ^ s * clusterSequence 1200 s * (2 : ℝ) ^ depth := by
  classical
  intro s
  induction s with
  | zero =>
      intro free fixed E left depth hcard _ _ _ hframe hlevels _ hfixed hselected _
      have hempty : free = ∅ := Finset.card_eq_zero.mp hcard
      have hfixedAll : ∀ p ∈ E, ∀ h, p.2.2 h = fixed h := by
        intro p hp h
        exact hfixed p hp h (by simp [hempty])
      have hbound := empty_profile_occurrence_bound fixed value hB hR hlevels hframe
        hfixedAll hselected
      have hreal : (E.card : ℝ) ≤ (2 : ℝ) ^ depth := by exact_mod_cast hbound
      simpa only [pow_zero, clusterSequence, mul_one, one_mul] using hreal
  | succ s ih =>
      intro free fixed E left depth hcard hfree hpositions hleft hframe hlevels hunique
        hfixed hselected hmixed
      have hnonempty : free.Nonempty := Finset.card_pos.mp (by omega)
      let H := free.max' hnonempty
      have hH : H ∈ free := Finset.max'_mem free hnonempty
      have hmax : ∀ h ∈ free, h ≤ H := fun h hh => Finset.le_max' free h hh
      let size := 2 ^ (d + H.val)
      let small := d + H.val + 1
      let cellWidth := 2 * size
      let count := 2 ^ (depth - small)
      have hsmall : small ≤ depth := hpositions H hH
      have hwidthPower : cellWidth = 2 ^ small := by
        dsimp [cellWidth, size, small]
        rw [pow_succ']
      have hgrid : count * cellWidth = 2 ^ depth := by
        dsimp [count]
        rw [hwidthPower]
        exact dyadic_grid_size hsmall
      have hcellWidth : 0 < cellWidth := by dsimp [cellWidth, size]; positivity
      have hsize : 2 ^ d ≤ size := by
        apply Nat.pow_le_pow_right (by decide)
        omega
      have hgridFrame : ∀ p ∈ E, (left : ℤ) ≤ p.2.1 ∧
          p.2.1 < (left : ℤ) + (count * cellWidth : ℕ) := by
        simpa only [hgrid] using hframe
      have hsum := cellOccurrences_card_sum E hcellWidth hgridFrame
      have hcell : ∀ i ∈ Finset.range count,
          ((cellOccurrences E (left : ℤ) cellWidth i).card : ℝ) ≤
            (2 : ℝ) ^ (s + 1) * clusterSequence 1200 (s + 1) * (2 * (size : ℝ)) := by
        intro i hi
        let C := cellOccurrences E (left : ℤ) cellWidth i
        let a := left + i * cellWidth
        have hCE : C ⊆ E := cellOccurrences_subset E _ _ _
        have hcellFrame : ∀ p ∈ C, (a : ℤ) ≤ p.2.1 ∧
            p.2.1 < (a : ℤ) + 2 * (size : ℤ) := by
          intro p hp
          have h := cellOccurrences_nat_interval hcellWidth (fun p hp => (hframe p hp).1) p hp
          simpa [a, cellWidth, Nat.cast_add, Nat.cast_mul] using h
        have halign : 2 ^ small ∣ a := by
          have h := grid_start_dvd (index := i) hsmall hleft
          simpa only [a, hwidthPower] using h
        have hfixedC : ∀ p ∈ C, ∀ h, h ∉ free → p.2.2 h = fixed h :=
          fun p hp h hh => hfixed p (hCE hp) h hh
        have hforbidden : ∀ p ∈ C,
            ¬DyadicMean (selectedCoordinates (occurrenceFamily C))
              ((a : ℤ) + (size : ℕ)) p.1 p.2.1 :=
          hmixed H hH C hCE a halign hcellFrame (higher_positions_agree hmax hfixedC)
        have hchildren : ∀ right : Bool, ∀ bit : Fin 2,
            ((bitOccurrences (halfOccurrences C ((a : ℤ) + size) right) H bit).card : ℝ) ≤
              (2 : ℝ) ^ s * clusterSequence 1200 s * size := by
          intro right bit
          let earlier := halfOccurrences C ((a : ℤ) + size) right
          let child := bitOccurrences earlier H bit
          let childLeft := halfCellStart a size right
          have hearlier : earlier ⊆ C := halfOccurrences_subset C _ right
          have hchildEarlier : child ⊆ earlier := bitOccurrences_subset earlier H bit
          have hchildE : child ⊆ E := hchildEarlier.trans (hearlier.trans hCE)
          have hchildCard : (free.erase H).card = s := by
            rw [Finset.card_erase_of_mem hH, hcard]
            omega
          have hchildPositions : ∀ h ∈ free.erase H, d + h.val + 1 ≤ d + H.val := by
            intro h hh
            have h := erased_position_index hmax hh
            omega
          have hsizeAlign : size ∣ a :=
            (natural_power_dvd (show d + H.val ≤ small by dsimp [small]; omega)).trans halign
          have hchildAlign : 2 ^ (d + H.val) ∣ childLeft :=
            halfCellStart_dvd hsizeAlign right
          have hchildFrame : ∀ p ∈ child, (childLeft : ℤ) ≤ p.2.1 ∧
              p.2.1 < (childLeft : ℤ) + (2 ^ (d + H.val) : ℕ) := by
            intro p hp
            have h := halfOccurrences_interval hcellFrame right p (hchildEarlier hp)
            simpa only [childLeft, halfCellStart_cast, size] using h
          have hchildFixed : ∀ p ∈ child, ∀ h, h ∉ free.erase H →
              p.2.2 h = Function.update fixed H bit h :=
            bitOccurrences_fixed H bit (fun p hp h hh => hfixedC p (hearlier hp) h hh)
          have hbound := ih (free.erase H) (Function.update fixed H bit) child childLeft
            (d + H.val) hchildCard (by omega) hchildPositions hchildAlign hchildFrame
            (fun p hp => hlevels p (hchildE hp))
            (fun j t x y hx hy => hunique j t x y (hchildE hx) (hchildE hy))
            hchildFixed (fun p hp => hselected p (hchildE hp))
            (hmixed.mono (Finset.erase_subset H free) hchildE)
          simpa only [child, earlier, size, Nat.cast_pow, Nat.cast_ofNat] using hbound
        exact cell_mass_bound C free fixed value H hd hcard (by simpa only [hcard] using hfree)
          hwidth hwidthPos hsize hB hR hcellFrame
          (fun p hp => hlevels p (hCE hp))
          (fun j t x y hx hy => hunique j t x y (hCE hx) (hCE hy))
          hfixedC (fun p hp => hselected p (hCE hp)) hforbidden hchildren
      have hsumReal : (E.card : ℝ) = ∑ i ∈ Finset.range count,
          ((cellOccurrences E (left : ℤ) cellWidth i).card : ℝ) := by exact_mod_cast hsum
      have hgridReal : (count : ℝ) * (2 * (size : ℝ)) = (2 : ℝ) ^ depth := by
        exact_mod_cast hgrid
      calc
        (E.card : ℝ) = ∑ i ∈ Finset.range count,
            ((cellOccurrences E (left : ℤ) cellWidth i).card : ℝ) := hsumReal
        _ ≤ ∑ _i ∈ Finset.range count,
            (2 : ℝ) ^ (s + 1) * clusterSequence 1200 (s + 1) * (2 * (size : ℝ)) :=
          Finset.sum_le_sum hcell
        _ = (count : ℝ) * ((2 : ℝ) ^ (s + 1) *
            clusterSequence 1200 (s + 1) * (2 * (size : ℝ))) := by simp
        _ = (2 : ℝ) ^ (s + 1) * clusterSequence 1200 (s + 1) *
            ((count : ℝ) * (2 * (size : ℝ))) := by ring
        _ = _ := by rw [hgridReal]

end Erdos790.Upper
