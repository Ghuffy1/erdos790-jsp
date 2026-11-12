import Erdos790.Upper.RecursiveFamilies
import Erdos790.Upper.CellSides

/-!
# Mixed-mean exclusion inherited by recursive subfamilies
-/

namespace Erdos790.Upper

def MixedExclusion {d : ℕ} (free : Finset (Fin d))
    (E : Finset (ℕ × ℤ × (Fin d → Fin 2))) : Prop :=
  ∀ H ∈ free, ∀ F : Finset (ℕ × ℤ × (Fin d → Fin 2)), F ⊆ E →
    ∀ a : ℕ, 2 ^ (d + H.val + 1) ∣ a →
      (∀ p ∈ F, (a : ℤ) ≤ p.2.1 ∧ p.2.1 < a + 2 * (2 ^ (d + H.val) : ℕ)) →
      (∀ p ∈ F, ∀ q ∈ F, ∀ h : Fin d, H < h → p.2.2 h = q.2.2 h) →
      ∀ p ∈ F, ¬DyadicMean (selectedCoordinates (occurrenceFamily F))
        ((a : ℤ) + (2 ^ (d + H.val) : ℕ)) p.1 p.2.1

theorem MixedExclusion.mono {d : ℕ} {free small : Finset (Fin d)}
    {E F : Finset (ℕ × ℤ × (Fin d → Fin 2))}
    (h : MixedExclusion free E) (hfree : small ⊆ free) (hEF : F ⊆ E) :
    MixedExclusion small F := by
  intro H hH G hG a ha hframe hwords p hp
  exact h H (hfree hH) G (hG.trans hEF) a ha hframe hwords p hp

theorem higher_positions_agree {d : ℕ} {free : Finset (Fin d)} {H : Fin d}
    {E : Finset (ℕ × ℤ × (Fin d → Fin 2))} {fixed : Fin d → Fin 2}
    (hmax : ∀ h ∈ free, h ≤ H)
    (hfixed : ∀ p ∈ E, ∀ h, h ∉ free → p.2.2 h = fixed h) :
    ∀ p ∈ E, ∀ q ∈ E, ∀ h : Fin d, H < h → p.2.2 h = q.2.2 h := by
  intro p hp q hq h hH
  have hnot : h ∉ free := fun hmem => not_le_of_gt hH (hmax h hmem)
  exact (hfixed p hp h hnot).trans (hfixed q hq h hnot).symm

theorem erased_position_index {d : ℕ} {free : Finset (Fin d)} {H h : Fin d}
    (hmax : ∀ k ∈ free, k ≤ H) (hh : h ∈ free.erase H) : h.val + 1 ≤ H.val := by
  obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hh
  have hle := hmax h hmem
  have hlt : h < H := lt_of_not_ge (fun hge => hne (le_antisymm hle hge))
  have hval : h.val < H.val := hlt
  omega

end Erdos790.Upper
