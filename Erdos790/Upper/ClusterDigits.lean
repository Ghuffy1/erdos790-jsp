import Erdos790.Upper.ClusterArithmetic

/-!
# Distinct radix digits assigned to the earlier clusters
-/

namespace Erdos790.Upper

theorem predecessor_digit_data {d width start j delay : ℕ} (S : Finset ℕ)
    (hw : 0 < width) (hstartMem : start ∈ S) (hstartMax : start ≤ d * width)
    (hgap : ∀ a ∈ S, ∀ b ∈ S, a < b → a + 6 * width ≤ b)
    (hstart : start ≤ j) (hj : j < start + delay) (hdelay : delay ≤ width) :
    let previous := S.filter (fun i => i < start)
    (previous.image (assignedDigit d width start)).card = previous.card ∧
      previous.card ≤ d / 6 ∧
      ∀ i ∈ previous,
        2 ≤ assignedDigit d width start i ∧ assignedDigit d width start i ≤ d - 4 ∧
        d * width + 2 * width ≤ j - i + width * assignedDigit d width start i ∧
        j - i + width * assignedDigit d width start i < d * width + 4 * width := by
  let previous := S.filter (fun i => i < start)
  have hbefore : ∀ i ∈ previous, i + 6 * width ≤ start := by
    intro i hi
    obtain ⟨hiS, histart⟩ := Finset.mem_filter.mp hi
    exact hgap i hiS start hstartMem histart
  have hspan : ∀ i ∈ previous, start - i ≤ d * width :=
    fun i _ => (Nat.sub_le start i).trans hstartMax
  have hinj : Set.InjOn (assignedDigit d width start) previous := by
    intro a ha b hb heq
    by_contra hne
    rcases lt_or_gt_of_ne hne with hab | hba
    · have hsep := hgap a (Finset.mem_filter.mp ha).1 b (Finset.mem_filter.mp hb).1 hab
      have h := assignedDigit_strict (d := d) (width := width) (start := start) (a := a) (b := b) hw
        (by have h := hbefore a ha; omega) (by have h := hbefore b hb; omega)
        (by omega) (hspan a ha)
      exact (ne_of_lt h) heq
    · have hsep := hgap b (Finset.mem_filter.mp hb).1 a (Finset.mem_filter.mp ha).1 hba
      have h := assignedDigit_strict (d := d) (width := width) (start := start) (a := b) (b := a) hw
        (by have h := hbefore b hb; omega) (by have h := hbefore a ha; omega)
        (by omega) (hspan b hb)
      exact (ne_of_gt h) heq
  have hcount : previous.card ≤ start / (6 * width) :=
    separated_predecessors_card previous (by omega) hbefore
      (fun a ha b hb hab => hgap a (Finset.mem_filter.mp ha).1 b (Finset.mem_filter.mp hb).1 hab)
  have hquotient : start / (6 * width) ≤ d / 6 := by
    calc
      _ ≤ (d * width) / (6 * width) := Nat.div_le_div_right hstartMax
      _ = d / 6 := by
        rw [show d * width = width * d by ring, show 6 * width = width * 6 by ring,
          ← Nat.div_div_eq_div_mul, Nat.mul_div_cancel_left _ hw]
  refine ⟨Finset.card_image_of_injOn hinj, hcount.trans hquotient, ?_⟩
  intro i hi
  have hprior := hbefore i hi
  have hbounds := assignedDigit_bounds hw (hspan i hi) (by omega : 6 * width ≤ start - i)
  have hscale := assignedDigit_scale (d := d) (start := start) (earlier := i) (j := j) (delay := delay)
    hw (by omega : i ≤ start) hstart hj hdelay (hspan i hi)
  exact ⟨hbounds.1, hbounds.2, hscale.1, hscale.2⟩

end Erdos790.Upper
