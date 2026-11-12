import Erdos790.Upper.CyclicPhaseCount
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic.Ring

/-!
# A finite sample space of rough offsets

Each unit residue is paired with the same number of complete periods. This
makes the sample size and the bound for repeated residues exact.
-/

open Finset

namespace Erdos790.Upper

abbrev RoughChoice (m Q : ℕ) := Fin m × (ZMod Q)ˣ

def roughOffset {m Q : ℕ} (choice : RoughChoice m Q) : ℕ :=
  Q * choice.1.val + (choice.2 : ZMod Q).val

theorem roughOffset_mod {m Q : ℕ} [NeZero Q] (choice : RoughChoice m Q) :
    roughOffset choice % Q = (choice.2 : ZMod Q).val := by
  simp [roughOffset, Nat.add_mod, Nat.mod_eq_of_lt (ZMod.val_lt _)]

theorem roughOffset_lt {m Q : ℕ} [NeZero Q] (choice : RoughChoice m Q) :
    roughOffset choice < m * Q := by
  calc
    roughOffset choice < Q * choice.1.val + Q :=
      Nat.add_lt_add_left (ZMod.val_lt _) _
    _ = Q * (choice.1.val + 1) := by ring
    _ ≤ Q * m := Nat.mul_le_mul_left Q (by have := choice.1.isLt; omega)
    _ = m * Q := Nat.mul_comm _ _

theorem roughOffset_injective {m Q : ℕ} [NeZero Q] :
    Function.Injective (roughOffset (m := m) (Q := Q)) := by
  intro a b hab
  have hval : (a.2 : ZMod Q).val = (b.2 : ZMod Q).val := by
    have hmod := congrArg (fun n : ℕ => n % Q) hab
    simpa only [roughOffset_mod] using hmod
  have hunit : a.2 = b.2 := Units.ext (ZMod.val_injective Q hval)
  have hprod : Q * a.1.val = Q * b.1.val := by
    dsimp [roughOffset] at hab
    omega
  have hfirst : a.1 = b.1 := Fin.ext
    (Nat.eq_of_mul_eq_mul_left (NeZero.pos Q) hprod)
  exact Prod.ext hfirst hunit

theorem roughOffset_coprime {m Q : ℕ} [NeZero Q] (choice : RoughChoice m Q) :
    Nat.Coprime (roughOffset choice) Q := by
  rw [← ZMod.coprime_mod_iff_coprime, roughOffset_mod]
  exact ZMod.val_coe_unit_coprime choice.2

theorem roughChoice_card (m Q : ℕ) [NeZero Q] :
    Fintype.card (RoughChoice m Q) = m * Q.totient := by
  simp [RoughChoice, ZMod.card_units_eq_totient]

theorem roughChoice_residue_fiber (m Q : ℕ) [NeZero Q] (residue : (ZMod Q)ˣ) :
    ((Finset.univ : Finset (RoughChoice m Q)).filter (fun choice => choice.2 = residue)).card = m := by
  have hset : (Finset.univ : Finset (RoughChoice m Q)).filter (fun choice => choice.2 = residue) =
      (Finset.univ : Finset (Fin m)) ×ˢ {residue} := by
    ext choice
    rcases choice with ⟨a, r⟩
    simp [eq_comm]
  rw [hset]
  simp

theorem roughChoice_density {m Q v : ℕ} [NeZero Q] (hQ : Q ≤ 4 * v * Q.totient) :
    m * Q ≤ 4 * v * Fintype.card (RoughChoice m Q) := by
  rw [roughChoice_card]
  calc
    m * Q ≤ m * (4 * v * Q.totient) := Nat.mul_le_mul_left m hQ
    _ = 4 * v * (m * Q.totient) := by ring

def roughBadChoices (m Q : ℕ) [NeZero Q] (bad : Finset ℕ) : Finset (RoughChoice m Q) :=
  Finset.univ.filter (fun choice => roughOffset choice ∈ bad)

theorem roughBadChoices_card_le (m Q : ℕ) [NeZero Q] (bad : Finset ℕ) :
    (roughBadChoices m Q bad).card ≤ bad.card := by
  have hsubset : (roughBadChoices m Q bad).image roughOffset ⊆ bad := by
    intro x hx
    obtain ⟨choice, hchoice, rfl⟩ := Finset.mem_image.mp hx
    exact (Finset.mem_filter.mp hchoice).2
  calc
    (roughBadChoices m Q bad).card = ((roughBadChoices m Q bad).image roughOffset).card :=
      (Finset.card_image_of_injective _ roughOffset_injective).symm
    _ ≤ bad.card := Finset.card_le_card hsubset

theorem roughBadChoices_fraction {m Q v L : ℕ} [NeZero Q] (bad : Finset ℕ)
    (hv : 0 < v) (hQ : Q ≤ 4 * v * Q.totient) (hscale : 14400 * L ≤ v)
    (hbad : bad.card * v ^ 2 ≤ 36 * (m * Q)) :
    100 * L * (roughBadChoices m Q bad).card ≤ Fintype.card (RoughChoice m Q) := by
  apply conditioned_bad_count_bound hv ?_ (roughChoice_density hQ) hscale
  exact (Nat.mul_le_mul_right (v ^ 2) (roughBadChoices_card_le m Q bad)).trans hbad

end Erdos790.Upper
