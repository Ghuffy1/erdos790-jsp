import Erdos790.Upper.SelectionMass
import Mathlib.Tactic.Linarith

/-!
# Finite stable periods separated by bounded refinement delays
-/

namespace Erdos790.Upper

theorem finite_phase_mass_bound {State : Type*}
    (S : ℕ → Finset ℤ) (Valid : ℕ → State → Prop) (rank : State → ℕ)
    (bad : ℕ → State → Prop) (stop width delay M : ℕ)
    (hpoint : ∀ j < stop, (S j).card ≤ M)
    (hpositive : ∀ t state, Valid t state → 0 < rank state)
    (hstable : ∀ t finish state, t ≤ finish → finish ≤ stop → finish - t ≤ width →
      Valid t state → (∀ j, t ≤ j → j < finish → ¬bad j state) →
      selectionMass S t finish ≤ 3 * M)
    (hadvance : ∀ t j state, Valid t state → t ≤ j → j < stop → bad j state →
      ∃ next, Valid (j + delay) next ∧ 2 * rank next ≤ rank state) :
    ∀ fuel start state, start ≤ stop → stop - start ≤ width → Valid start state →
      rank state < 2 ^ fuel → selectionMass S start stop ≤ fuel * (delay + 3) * M := by
  classical
  intro fuel
  induction fuel with
  | zero =>
    intro start state _ _ hv hrank
    have := hpositive start state hv
    norm_num at hrank
    omega
  | succ fuel ih =>
    intro start state hstart hshort hv hrank
    by_cases hexists : ∃ j, start ≤ j ∧ j < stop ∧ bad j state
    · obtain ⟨j, hsj, hjs, hbad, hclear⟩ := first_bad_level (fun j => bad j state) hexists
      have hprefix := hstable start j state hsj hjs.le (by omega) hv hclear
      have hsplit := selectionMass_split S hsj hjs.le
      by_cases hover : stop ≤ j + delay
      · have htail : selectionMass S j stop ≤ delay * M :=
          (selectionMass_le hpoint).trans (Nat.mul_le_mul_right M (by omega))
        have htotal : selectionMass S start stop ≤ (delay + 3) * M := by
          rw [hsplit]
          nlinarith
        calc
          selectionMass S start stop ≤ (delay + 3) * M := htotal
          _ ≤ (fuel + 1) * (delay + 3) * M := by
            have h := Nat.le_mul_of_pos_left ((delay + 3) * M) (Nat.succ_pos fuel)
            simpa only [Nat.mul_assoc] using h
      · have hnextTime : j + delay < stop := by omega
        obtain ⟨next, hvnext, hranknext⟩ := hadvance start j state hv hsj hjs hbad
        have hnextBound : rank next < 2 ^ fuel := by
          rw [pow_succ] at hrank
          omega
        have hrest := ih (j + delay) next hnextTime.le (by omega) hvnext hnextBound
        have hdelay : selectionMass S j (j + delay) ≤ delay * M := by
          have hbound := selectionMass_le (S := S) (start := j) (stop := j + delay)
            (fun i hi => hpoint i (by omega))
          simpa only [Nat.add_sub_cancel_left] using hbound
        have hsplitTail := selectionMass_split S (show j ≤ j + delay by omega) hnextTime.le
        rw [hsplit, hsplitTail]
        nlinarith
    · have hclear : ∀ j, start ≤ j → j < stop → ¬bad j state := by
        intro j hsj hjs hbad
        exact hexists ⟨j, hsj, hjs, hbad⟩
      have htotal := hstable start stop state hstart le_rfl hshort hv hclear
      calc
        selectionMass S start stop ≤ 3 * M := htotal
        _ ≤ (delay + 3) * M := Nat.mul_le_mul_right M (by omega)
        _ ≤ (fuel + 1) * (delay + 3) * M := by
          have h := Nat.le_mul_of_pos_left ((delay + 3) * M) (Nat.succ_pos fuel)
          simpa only [Nat.mul_assoc] using h

end Erdos790.Upper
