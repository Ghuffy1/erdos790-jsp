import Erdos790.Upper.DeterministicTents
import Erdos790.Upper.WeightedDigits

/-!
# Leading and higher digits of a mixed tent average
-/

namespace Erdos790.Upper

def tentDigit {d : ℕ} (amplification t : ℕ) (bits : Fin d → Fin 2) (h : Fin d) : ℤ :=
  amplification * (periodicTent (2 ^ (d + h.val)) t : ℤ) + (bits h).val

theorem tentDigit_bounds {d : ℕ} (amplification t : ℕ) (bits : Fin d → Fin 2) (h : Fin d) :
    0 ≤ tentDigit amplification t bits h ∧
      tentDigit amplification t bits h ≤
        (amplification : ℤ) * AuxiliaryParameters.timeCount d + 1 := by
  have htent := (periodicTent_bounds (t := t) (by positivity : 0 < 2 ^ (d + h.val))).2
  have hperiod := AuxiliaryParameters.tent_period_le_timeCount h
  have hmul := Nat.mul_le_mul_left amplification (htent.le.trans hperiod)
  have hbit : (bits h).val ≤ 1 := by have h := (bits h).isLt; omega
  constructor
  · unfold tentDigit
    positivity
  · have h := Nat.add_le_add hmul hbit
    unfold tentDigit
    exact_mod_cast h

theorem tentDigit_higher_difference_zero {ι : Type*} {d : ℕ} (I : Finset ι)
    (w : ι → ℤ) (x : ι → ℕ) (bits : ι → Fin d → Fin 2)
    (head : ℕ) (headBits : Fin d → Fin 2) (amplification a : ℕ) (H h : Fin d)
    {W : ℤ} (hHh : H < h) (halign : 2 * 2 ^ (d + H.val) ∣ a)
    (hhead : a ≤ head ∧ head < a + 2 * 2 ^ (d + H.val))
    (hx : ∀ i ∈ I, a ≤ x i ∧ x i < a + 2 * 2 ^ (d + H.val))
    (hbits : ∀ i ∈ I, bits i h = headBits h)
    (hmass : ∑ i ∈ I, w i = W) (hmean : ∑ i ∈ I, w i * (x i : ℤ) = W * head) :
    W * tentDigit amplification head headBits h -
      (∑ i ∈ I, w i * tentDigit amplification (x i) (bits i) h) = 0 := by
  obtain ⟨slope, intercept, _, haffine⟩ := dyadic_periodicTent_affine hHh halign
  have hheadDigit : tentDigit amplification head headBits h =
      ((amplification : ℤ) * slope) * head +
        ((amplification : ℤ) * intercept + (headBits h).val) := by
    unfold tentDigit
    rw [haffine head hhead.1 hhead.2]
    ring
  have hsourceDigit : ∀ i ∈ I, tentDigit amplification (x i) (bits i) h =
      ((amplification : ℤ) * slope) * x i +
        ((amplification : ℤ) * intercept + (headBits h).val) := by
    intro i hi
    unfold tentDigit
    rw [haffine (x i) (hx i hi).1 (hx i hi).2, hbits i hi]
    ring
  rw [hheadDigit]
  have hsum : (∑ i ∈ I, w i * tentDigit amplification (x i) (bits i) h) =
      ∑ i ∈ I, w i * (((amplification : ℤ) * slope) * x i +
        ((amplification : ℤ) * intercept + (headBits h).val)) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [hsourceDigit i hi]
  rw [hsum]
  exact weighted_affine_digit_difference I w (fun i => (x i : ℤ)) hmass hmean

theorem tentDigit_leading_lower {ι : Type*} [DecidableEq ι] {d : ℕ} (I : Finset ι)
    (w : ι → ℤ) (x : ι → ℕ) (bits : ι → Fin d → Fin 2)
    (head : ℕ) (headBits : Fin d → Fin 2) (amplification a : ℕ) (H : Fin d)
    {W δ : ℤ} (hW : 0 < W) (hw : ∀ i ∈ I, 0 ≤ w i)
    (halign : 2 * 2 ^ (d + H.val) ∣ a)
    (hhead : a ≤ head ∧ head < a + 2 * 2 ^ (d + H.val))
    (hx : ∀ i ∈ I, a ≤ x i ∧ x i < a + 2 * 2 ^ (d + H.val))
    (hmass : ∑ i ∈ I, w i = W) (hmean : ∑ i ∈ I, w i * (x i : ℤ) = W * head)
    (hleft : ∃ i ∈ I, x i < a + 2 ^ (d + H.val) ∧ δ ≤ w i)
    (hright : ∃ i ∈ I, a + 2 ^ (d + H.val) ≤ x i ∧ δ ≤ w i)
    (hscale : 2 * W ≤ (amplification : ℤ) * δ) :
    2 * W ≤ W * tentDigit amplification head headBits H -
      ∑ i ∈ I, w i * tentDigit amplification (x i) (bits i) H := by
  let shifted := fun i => (x i : ℤ) - a
  have hmean' : (∑ i ∈ I, w i * shifted i) = W * ((head : ℤ) - a) := by
    simp only [shifted, mul_sub, Finset.sum_sub_distrib]
    rw [← Finset.sum_mul, hmass, hmean]
  have hleft' : ∃ i ∈ I, shifted i < (2 : ℤ) ^ (d + H.val) ∧ δ ≤ w i := by
    obtain ⟨i, hi, hx, hδ⟩ := hleft
    have hx' : (x i : ℤ) < (a : ℤ) + (2 : ℤ) ^ (d + H.val) := by exact_mod_cast hx
    exact ⟨i, hi, by dsimp [shifted]; omega, hδ⟩
  have hright' : ∃ i ∈ I, (2 : ℤ) ^ (d + H.val) ≤ shifted i ∧ δ ≤ w i := by
    obtain ⟨i, hi, hx, hδ⟩ := hright
    have hx' : (a : ℤ) + (2 : ℤ) ^ (d + H.val) ≤ (x i : ℤ) := by exact_mod_cast hx
    exact ⟨i, hi, by dsimp [shifted]; omega, hδ⟩
  have hgap := weighted_tent_digit_lower I w shifted (fun i => ((bits i H).val : ℤ))
    (head := (head : ℤ) - a) (M := (2 : ℤ) ^ (d + H.val))
    (amplification := (amplification : ℤ)) (headBit := ((headBits H).val : ℤ))
    hW (by positivity) hw hmass hmean' hleft' hright'
    (fun i _ => by have h := (bits i H).isLt; omega) (by positivity) hscale
  have hheadTent := periodicTent_on_cell (by positivity : 0 < 2 ^ (d + H.val))
    halign hhead.1 hhead.2
  have hheadDigit : tentDigit amplification head headBits H =
      (amplification : ℤ) * integerTent ((2 : ℤ) ^ (d + H.val)) ((head : ℤ) - a) +
        (headBits H).val := by
    unfold tentDigit
    rw [hheadTent]
    simp only [Nat.cast_pow, Nat.cast_ofNat]
  have hsource : ∀ i ∈ I, tentDigit amplification (x i) (bits i) H =
      (amplification : ℤ) * integerTent ((2 : ℤ) ^ (d + H.val)) (shifted i) + (bits i H).val := by
    intro i hi
    unfold tentDigit
    rw [periodicTent_on_cell (by positivity : 0 < 2 ^ (d + H.val)) halign (hx i hi).1 (hx i hi).2]
    simp only [Nat.cast_pow, Nat.cast_ofNat, shifted]
  rw [hheadDigit]
  have hsum : (∑ i ∈ I, w i * tentDigit amplification (x i) (bits i) H) =
      ∑ i ∈ I, w i * ((amplification : ℤ) *
        integerTent ((2 : ℤ) ^ (d + H.val)) (shifted i) + (bits i H).val) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [hsource i hi]
  rw [hsum]
  exact hgap

end Erdos790.Upper
