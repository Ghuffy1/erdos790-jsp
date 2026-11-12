import Erdos790.Upper.ClusterMultiplicity

/-!
# Counting selected occurrences over a finite coordinate domain
-/

namespace Erdos790.Upper

theorem coordinate_occurrences_card_le {d start delay R : ℕ} {B : Finset ℕ}
    (occurrences : Finset (ℕ × ℤ × (Fin d → Fin 2)))
    (coordinates : Finset ℤ) (free : Finset (Fin d)) (fixed : Fin d → Fin 2)
    (value : ℤ → (Fin d → Fin 2) → ℕ)
    (hB : RepeatedSumFree R B) (hR : 2 ^ delay ≤ R)
    (hlevels : ∀ p ∈ occurrences, start ≤ p.1 ∧ p.1 < start + delay)
    (hcoordinates : ∀ p ∈ occurrences, p.2.1 ∈ coordinates)
    (hfixed : ∀ p ∈ occurrences, ∀ h, h ∉ free → p.2.2 h = fixed h)
    (hselected : ∀ p ∈ occurrences, 2 ^ p.1 * value p.2.1 p.2.2 ∈ B) :
    occurrences.card ≤ 2 ^ free.card * coordinates.card := by
  classical
  have hfiber (t : ℤ) : (occurrences.filter (fun p => p.2.1 = t)).card ≤ 2 ^ free.card := by
    let fiber := occurrences.filter (fun p => p.2.1 = t)
    let projected := fiber.image (fun p => (p.1, p.2.2))
    have hinj : Set.InjOn (fun p : ℕ × ℤ × (Fin d → Fin 2) => (p.1, p.2.2)) ↑fiber := by
      intro a ha b hb hab
      have hat := (Finset.mem_filter.mp ha).2
      have hbt := (Finset.mem_filter.mp hb).2
      have hlevel : a.1 = b.1 := congrArg (fun p : ℕ × (Fin d → Fin 2) => p.1) hab
      have hword : a.2.2 = b.2.2 := congrArg (fun p : ℕ × (Fin d → Fin 2) => p.2) hab
      exact Prod.ext hlevel (Prod.ext (hat.trans hbt.symm) hword)
    have hcard : projected.card = fiber.card := Finset.card_image_of_injOn hinj
    change fiber.card ≤ _
    rw [← hcard]
    apply binary_occurrences_card_le projected free fixed (value t) hB hR
    · intro p hp
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hp
      exact hlevels a (Finset.mem_filter.mp ha).1
    · intro p hp h hh
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hp
      exact hfixed a (Finset.mem_filter.mp ha).1 h hh
    · intro p hp
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hp
      have hat := (Finset.mem_filter.mp ha).2
      simpa only [hat] using hselected a (Finset.mem_filter.mp ha).1
  rw [Finset.card_eq_sum_card_fiberwise (s := occurrences) (t := coordinates)
    (f := fun p : ℕ × ℤ × (Fin d → Fin 2) => p.2.1) hcoordinates]
  calc
    (∑ t ∈ coordinates, (occurrences.filter (fun p => p.2.1 = t)).card) ≤
        ∑ _t ∈ coordinates, 2 ^ free.card := Finset.sum_le_sum (fun t _ => hfiber t)
    _ = 2 ^ free.card * coordinates.card := by simp [Nat.mul_comm]

end Erdos790.Upper
