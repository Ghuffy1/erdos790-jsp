import Erdos790.Upper.Lifting

/-!
# Separation of the integer fibers

The shift is chosen larger than the product of each coarse label and the
largest digit. This gives the disjointness used in the distinct-summand lift.
-/

open Finset

namespace Erdos790.Upper

theorem liftValue_strictMono_label {H T : ℤ} {a b : ℕ} {u v : ℤ}
    (hH : 0 ≤ H) (ha : 0 < a) (hab : a < b)
    (hu : u ≤ T) (hv : 0 ≤ v) (hshift : (a : ℤ) * T < H) :
    liftValue H a u < liftValue H b v := by
  have ha0 : (0 : ℤ) ≤ a := by positivity
  have hb0 : (0 : ℤ) ≤ b := by positivity
  have hab' : (a : ℤ) + 1 ≤ b := by exact_mod_cast hab
  calc
    liftValue H a u ≤ (a : ℤ) * (H + T) :=
      mul_le_mul_of_nonneg_left (by omega) ha0
    _ < ((a : ℤ) + 1) * H := by nlinarith
    _ ≤ (b : ℤ) * H := mul_le_mul_of_nonneg_right hab' hH
    _ ≤ liftValue H b v := mul_le_mul_of_nonneg_left (by omega) hb0

theorem fiberSeparated_of_bounds {H T : ℤ} {F : Finset ℕ} {D : Finset ℤ}
    (hH : 0 ≤ H) (hpos : ∀ a ∈ F, 0 < a)
    (hdigits : ∀ u ∈ D, 0 ≤ u ∧ u ≤ T)
    (hshift : ∀ a ∈ F, (a : ℤ) * T < H) : FiberSeparated H F D := by
  intro a ha u hu b hb v hv heq
  have hab : a = b := by
    rcases lt_trichotomy a b with hab | hab | hab
    · exact False.elim ((ne_of_lt (liftValue_strictMono_label hH (hpos a ha) hab
        (hdigits u hu).2 (hdigits v hv).1 (hshift a ha))) heq)
    · exact hab
    · exact False.elim ((ne_of_lt (liftValue_strictMono_label hH (hpos b hb) hab
        (hdigits v hv).2 (hdigits u hu).1 (hshift b hb))) heq.symm)
  refine ⟨hab, ?_⟩
  subst b
  exact liftValue_injective (hpos a ha) heq

end Erdos790.Upper
