import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
# Separated predecessor levels and their assigned radix positions
-/

namespace Erdos790.Upper

def assignedDigit (d width start earlier : ℕ) : ℕ :=
  d - (start - earlier) / width + 2

theorem predecessor_quotient_strict {start width a b : ℕ} (hw : 0 < width)
    (ha : a ≤ start) (hb : b ≤ start) (hab : a + width ≤ b) :
    (start - b) / width < (start - a) / width := by
  have hdiff : start - b + width ≤ start - a := by omega
  have hdiv := Nat.div_le_div_right (c := width) hdiff
  have hstep : (start - b + width) / width = (start - b) / width + 1 := by
    simpa using Nat.add_div_right (start - b) hw
  rw [hstep] at hdiv
  omega

theorem assignedDigit_bounds {d width start earlier : ℕ} (hw : 0 < width)
    (hspan : start - earlier ≤ d * width) (hsep : 6 * width ≤ start - earlier) :
    2 ≤ assignedDigit d width start earlier ∧ assignedDigit d width start earlier ≤ d - 4 := by
  have hupper : (start - earlier) / width ≤ d := by
    have h := Nat.div_le_div_right (c := width) hspan
    simpa only [Nat.mul_div_cancel _ hw] using h
  have hlower : 6 ≤ (start - earlier) / width := (Nat.le_div_iff_mul_le hw).mpr hsep
  unfold assignedDigit
  omega

theorem assignedDigit_scale {d width start earlier j delay : ℕ} (hw : 0 < width)
    (hearlier : earlier ≤ start) (hstart : start ≤ j) (hj : j < start + delay)
    (hdelay : delay ≤ width) (hspan : start - earlier ≤ d * width) :
    d * width + 2 * width ≤ j - earlier + width * assignedDigit d width start earlier ∧
      j - earlier + width * assignedDigit d width start earlier < d * width + 4 * width := by
  have hquotient : (start - earlier) / width ≤ d := by
    have h := Nat.div_le_div_right (c := width) hspan
    simpa only [Nat.mul_div_cancel _ hw] using h
  have hdecomp := Nat.mod_add_div (start - earlier) width
  have hmod := Nat.mod_lt (start - earlier) hw
  have hsub := Nat.sub_add_cancel hquotient
  have hsubmul : width * (d - (start - earlier) / width) +
      width * ((start - earlier) / width) = width * d := by
    rw [← Nat.mul_add, hsub]
  have hlevels : j - earlier = start - earlier + (j - start) := by omega
  have hlate : j - start < width := by omega
  have hidentity : j - earlier + width * assignedDigit d width start earlier =
      d * width + 2 * width + (start - earlier) % width + (j - start) := by
    unfold assignedDigit
    nlinarith
  rw [hidentity]
  constructor <;> omega

theorem assignedDigit_strict {d width start a b : ℕ} (hw : 0 < width)
    (ha : a ≤ start) (hb : b ≤ start) (hab : a + width ≤ b)
    (hspan : start - a ≤ d * width) :
    assignedDigit d width start a < assignedDigit d width start b := by
  have hstrict := predecessor_quotient_strict hw ha hb hab
  have hupper : (start - a) / width ≤ d := by
    have h := Nat.div_le_div_right (c := width) hspan
    simpa only [Nat.mul_div_cancel _ hw] using h
  unfold assignedDigit
  omega

theorem separated_predecessors_card {start width : ℕ} (S : Finset ℕ) (hw : 0 < width)
    (hbefore : ∀ i ∈ S, i + width ≤ start)
    (hgap : ∀ i ∈ S, ∀ j ∈ S, i < j → i + width ≤ j) :
    S.card ≤ start / width := by
  let bucket := fun i => (start - i) / width
  have hinj : Set.InjOn bucket S := by
    intro i hi j hj hij
    by_contra hne
    rcases lt_or_gt_of_ne hne with hijlt | hjilt
    · have h := predecessor_quotient_strict (start := start) (a := i) (b := j) hw
        (by have h := hbefore i hi; omega)
        (by have h := hbefore j hj; omega) (hgap i hi j hj hijlt)
      exact (ne_of_gt h) hij
    · have h := predecessor_quotient_strict (start := start) (a := j) (b := i) hw
        (by have h := hbefore j hj; omega)
        (by have h := hbefore i hi; omega) (hgap j hj i hi hjilt)
      exact (ne_of_lt h) hij
  have hsubset : S.image bucket ⊆ Finset.Icc 1 (start / width) := by
    intro b hb
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hb
    have hprior := hbefore i hi
    apply Finset.mem_Icc.mpr
    constructor
    · apply (Nat.le_div_iff_mul_le hw).mpr
      omega
    · exact Nat.div_le_div_right (Nat.sub_le _ _)
  calc
    S.card = (S.image bucket).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Finset.Icc 1 (start / width)).card := Finset.card_le_card hsubset
    _ = start / width := by simp

end Erdos790.Upper
