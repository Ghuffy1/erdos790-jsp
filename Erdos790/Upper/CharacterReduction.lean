import Erdos790.Upper.CharacterPhases
import Mathlib.Data.Nat.Factorial.Basic

/-!
# Reducing a nontrivial character on a rough modulus

The reduced modulus exceeds the factorial cutoff. Multiplication by the
reduced character index permutes its residue classes.
-/

namespace Erdos790.Upper

theorem rough_character_reduction {M A p0 : ℕ} (hM : 0 < M)
    (hA : 0 < A) (hAM : A < M) (hrough : Nat.Coprime M p0.factorial) :
    ∃ p u g : ℕ, p0 < p ∧ 0 < g ∧ Nat.Coprime u p ∧ M = p * g ∧ A = u * g := by
  obtain ⟨p, u, hcoprime, hMprod, hAprod⟩ := Nat.exists_coprime M A
  let g := Nat.gcd M A
  have hg : 0 < g := Nat.gcd_pos_of_pos_left A hM
  have hu : 0 < u := by nlinarith
  have hpone : 1 < p := by
    by_contra h
    have hp : p ≤ 1 := by omega
    have hle : M ≤ g := by
      calc
        M = p * g := hMprod
        _ ≤ 1 * g := Nat.mul_le_mul_right g hp
        _ = g := by omega
    have hga : g ≤ A := by
      calc
        g ≤ u * g := Nat.le_mul_of_pos_left _ hu
        _ = A := hAprod.symm
    omega
  have hpdvd : p ∣ M := ⟨g, hMprod⟩
  have hpcoprime : Nat.Coprime p p0.factorial := hrough.of_dvd_left hpdvd
  have hlarge : p0 < p := by
    by_contra h
    have hfactorial : p ∣ p0.factorial := Nat.dvd_factorial (by omega) (by omega)
    have hone := hpcoprime.eq_one_of_dvd hfactorial
    omega
  exact ⟨p, u, g, hlarge, hg, hcoprime.symm, hMprod, hAprod⟩

theorem reduced_phase_injective {p u : ℕ} (hcoprime : Nat.Coprime u p)
    (shift : ℕ) :
    Function.Injective (fun b : ZMod p => -((u : ZMod p) * (shift + b))) := by
  intro b c h
  have hmul : (u : ZMod p) * ((shift : ZMod p) + b) =
      (u : ZMod p) * ((shift : ZMod p) + c) := neg_injective h
  have hu := (ZMod.unitOfCoprime u hcoprime).isUnit
  exact add_left_cancel (hu.mul_left_cancel hmul)

theorem reduced_character_identity {M A p u g : ℕ} [NeZero M] [NeZero p]
    (hg : 0 < g) (hM : M = p * g) (hA : A = u * g) (x : ℕ) :
    ZMod.stdAddChar (-((A : ZMod M) * (x : ZMod M))) =
      ZMod.stdAddChar (-((u : ZMod p) * (x : ZMod p))) := by
  have hcastM : -((A : ZMod M) * (x : ZMod M)) = ((-(A : ℤ) * x : ℤ) : ZMod M) := by
    push_cast
    ring
  have hcastp : -((u : ZMod p) * (x : ZMod p)) = ((-(u : ℤ) * x : ℤ) : ZMod p) := by
    push_cast
    ring
  rw [hcastM, hcastp, ZMod.stdAddChar_coe, ZMod.stdAddChar_coe]
  congr 1
  have hgC : (g : ℂ) ≠ 0 := by exact_mod_cast hg.ne'
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne p
  rw [hM, hA]
  push_cast
  field_simp

end Erdos790.Upper
