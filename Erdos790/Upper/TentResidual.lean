import Erdos790.Upper.TentDigits
import Erdos790.Upper.FiniteRadix
import Erdos790.Upper.WeightedRadix

/-!
# A mixed average has a positive residual in its first varying tent digit
-/

namespace Erdos790.Upper

def encodedTentValue {d : ℕ} (amplification q : ℕ) (constant step scale : ℤ)
    (t : ℕ) (bits : Fin d → Fin 2) : ℤ :=
  constant + step * t + scale * ∑ h : Fin d, tentDigit amplification t bits h * (q : ℤ) ^ h.val

theorem encodedTentValue_eq_rowOffset {d : ℕ} (amplification q C Q U : ℕ)
    (t : Fin (AuxiliaryParameters.timeCount d)) (bits : Fin d → Fin 2) :
    ((C + rowOffset Q U q (AuxiliaryParameters.tentRow d amplification) (t, bits) : ℕ) : ℤ) =
      encodedTentValue amplification q C ((Q : ℤ) * U) Q t.val bits := by
  unfold rowOffset AuxiliaryParameters.tentRow radixValue encodedTentValue tentDigit
  push_cast
  ring

theorem mixed_tent_residual_bounds {ι : Type*} [DecidableEq ι] {d : ℕ} (I : Finset ι)
    (w : ι → ℤ) (x : ι → ℕ) (bits : ι → Fin d → Fin 2)
    (head : ℕ) (headBits : Fin d → Fin 2) (amplification q a : ℕ) (H : Fin d)
    {W δ constant step scale : ℤ}
    (hW : 0 < W) (hscalePos : 0 < scale) (hq : 2 ≤ q)
    (hD : (amplification : ℤ) * AuxiliaryParameters.timeCount d + 1 ≤ (q : ℤ) - 1)
    (hw : ∀ i ∈ I, 0 ≤ w i)
    (halign : 2 * 2 ^ (d + H.val) ∣ a)
    (hhead : a ≤ head ∧ head < a + 2 * 2 ^ (d + H.val))
    (hx : ∀ i ∈ I, a ≤ x i ∧ x i < a + 2 * 2 ^ (d + H.val))
    (hfixed : ∀ h : Fin d, H < h → ∀ i ∈ I, bits i h = headBits h)
    (hmass : ∑ i ∈ I, w i = W) (hmean : ∑ i ∈ I, w i * (x i : ℤ) = W * head)
    (hleft : ∃ i ∈ I, x i < a + 2 ^ (d + H.val) ∧ δ ≤ w i)
    (hright : ∃ i ∈ I, a + 2 ^ (d + H.val) ≤ x i ∧ δ ≤ w i)
    (hgapScale : 2 * W ≤ (amplification : ℤ) * δ) :
    scale * W * (q : ℤ) ^ H.val ≤
        W * encodedTentValue amplification q constant step scale head headBits -
          ∑ i ∈ I, w i * encodedTentValue amplification q constant step scale (x i) (bits i) ∧
      (W * encodedTentValue amplification q constant step scale head headBits -
        ∑ i ∈ I, w i * encodedTentValue amplification q constant step scale (x i) (bits i)) <
        scale * W * (q : ℤ) ^ (H.val + 1) := by
  let digit := fun h : Fin d => W * tentDigit amplification head headBits h -
    ∑ i ∈ I, w i * tentDigit amplification (x i) (bits i) h
  have habs : ∀ h : Fin d, |digit h| ≤ W * ((q : ℤ) - 1) := by
    intro h
    have hbound := weighted_digit_difference_abs I w
      (fun i => tentDigit amplification (x i) (bits i) h) hW.le hw hmass
      (tentDigit_bounds amplification head headBits h)
      (fun i _ => tentDigit_bounds amplification (x i) (bits i) h)
    exact hbound.trans (mul_le_mul_of_nonneg_left hD hW.le)
  have hleading : 2 * W ≤ digit H := tentDigit_leading_lower I w x bits head headBits
    amplification a H hW hw halign hhead hx hmass hmean hleft hright hgapScale
  have hhigh : ∀ h : Fin d, H < h → digit h = 0 := by
    intro h hHh
    exact tentDigit_higher_difference_zero I w x bits head headBits amplification a H h
      hHh halign hhead hx (hfixed h hHh) hmass hmean
  have hrange := finite_radix_gap digit H (by exact_mod_cast hq) hW hleading
    (abs_le.mp (habs H)).2 (fun h _ => habs h) hhigh
  have hid : W * encodedTentValue amplification q constant step scale head headBits -
      (∑ i ∈ I, w i * encodedTentValue amplification q constant step scale (x i) (bits i)) =
      scale * ∑ h : Fin d, digit h * (q : ℤ) ^ h.val :=
    weighted_expansion_residual I Finset.univ Fin.val w (fun i => (x i : ℤ))
      (fun i h => tentDigit amplification (x i) (bits i) h)
      (fun h => tentDigit amplification head headBits h) hmass hmean
  rw [hid]
  constructor
  · simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hrange.1 hscalePos.le
  · simpa only [mul_assoc] using mul_lt_mul_of_pos_left hrange.2 hscalePos

end Erdos790.Upper
