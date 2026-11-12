import Erdos790.Upper.RadixWords
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-!
# Separated rows of binary radix offsets
-/

namespace Erdos790.Upper

def rowOffset {d T : ℕ} (Q U q : ℕ) (row : Fin T → Fin d → ℕ)
    (p : Fin T × (Fin d → Fin 2)) : ℕ :=
  Q * (p.1.val * U + radixValue q (fun h => row p.1 h + (p.2 h).val))

def rowOffsets {d T : ℕ} (Q U q : ℕ) (row : Fin T → Fin d → ℕ) : Finset ℕ :=
  Finset.univ.image (rowOffset Q U q row)

theorem rowOffset_injective {d T Q U q : ℕ} (row : Fin T → Fin d → ℕ)
    (hQ : 0 < Q) (hq : 1 < q)
    (hdigit : ∀ t h, row t h + 1 < q)
    (hrow : ∀ t (bits : Fin d → Fin 2),
      radixValue q (fun h => row t h + (bits h).val) < U) :
    Function.Injective (rowOffset Q U q row) := by
  rintro ⟨t, bits⟩ ⟨s, other⟩ heq
  have heq' := Nat.eq_of_mul_eq_mul_left hQ heq
  change t.val * U + radixValue q (fun h => row t h + (bits h).val) =
    s.val * U + radixValue q (fun h => row s h + (other h).val) at heq'
  have ht := hrow t bits
  have hs := hrow s other
  have hU : 0 < U := by omega
  have htdiv : (t.val * U + radixValue q (fun h => row t h + (bits h).val)) / U = t.val := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hU, Nat.div_eq_of_lt ht, Nat.zero_add]
  have hsdiv : (s.val * U + radixValue q (fun h => row s h + (other h).val)) / U = s.val := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hU, Nat.div_eq_of_lt hs, Nat.zero_add]
  have hts : t = s := Fin.ext (htdiv.symm.trans ((congrArg (fun x => x / U) heq').trans hsdiv))
  subst s
  have hradix : radixValue q (fun h => row t h + (bits h).val) =
      radixValue q (fun h => row t h + (other h).val) := by omega
  have hvalues := radixValue_eq_of_bounded_digits hq
    (fun h => row t h + (bits h).val) (fun h => row t h + (other h).val)
    (fun h => by have hb := (bits h).isLt; have hd := hdigit t h; omega)
    (fun h => by have hb := (other h).isLt; have hd := hdigit t h; omega) hradix
  have hbits : bits = other := by
    funext h
    apply Fin.ext
    have hvalue := congrFun hvalues h
    omega
  subst other
  rfl

theorem rowOffsets_card {d T Q U q : ℕ} (row : Fin T → Fin d → ℕ)
    (hQ : 0 < Q) (hq : 1 < q)
    (hdigit : ∀ t h, row t h + 1 < q)
    (hrow : ∀ t (bits : Fin d → Fin 2),
      radixValue q (fun h => row t h + (bits h).val) < U) :
    (rowOffsets Q U q row).card = T * 2 ^ d := by
  rw [rowOffsets, Finset.card_image_of_injective _
    (rowOffset_injective row hQ hq hdigit hrow)]
  simp

theorem rowOffsets_dvd {d T Q U q z : ℕ} (row : Fin T → Fin d → ℕ)
    (hz : z ∈ rowOffsets Q U q row) : Q ∣ z := by
  obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hz
  exact ⟨_, rfl⟩

theorem rowOffsets_lt {d T Q U q z : ℕ} (row : Fin T → Fin d → ℕ) (hQ : 0 < Q)
    (hrow : ∀ t (bits : Fin d → Fin 2),
      radixValue q (fun h => row t h + (bits h).val) < U)
    (hz : z ∈ rowOffsets Q U q row) : z < Q * (T * U) := by
  obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hz
  have hsmall := hrow p.1 p.2
  have ht := Nat.mul_le_mul_right U (Nat.succ_le_of_lt p.1.isLt)
  have hbound : p.1.val * U + radixValue q (fun h => row p.1 h + (p.2 h).val) < T * U := by
    nlinarith
  exact Nat.mul_lt_mul_of_pos_left hbound hQ

theorem radixValue_lt_rowStep {d q D T : ℕ} (hd : 0 < d) (hD : 0 < D) (hT : 0 < T)
    (hmargin : 32 * D * T ≤ q) (digits : Fin d → ℕ) (hbound : ∀ h, digits h ≤ D) :
    radixValue q digits < q ^ d / (8 * T) := by
  have hDT : D ≤ D * T := Nat.le_mul_of_pos_right _ hT
  have hq : 2 ≤ q := by nlinarith
  have hpow : q ^ d = q ^ (d - 1) * q := by
    nth_rw 1 [← Nat.sub_add_cancel hd]
    rw [pow_succ]
  have hstep : 4 * D * q ^ (d - 1) ≤ q ^ d / (8 * T) := by
    apply (Nat.le_div_iff_mul_le (by omega : 0 < 8 * T)).mpr
    calc
      4 * D * q ^ (d - 1) * (8 * T) = (32 * D * T) * q ^ (d - 1) := by ring
      _ ≤ q * q ^ (d - 1) := Nat.mul_le_mul_right _ hmargin
      _ = q ^ d := by rw [hpow]; ring
  have hscale : 2 * D * q ^ (d - 1) ≤ 4 * D * q ^ (d - 1) := by
    simpa only [Nat.mul_assoc] using
      Nat.mul_le_mul_right (D * q ^ (d - 1)) (by decide : 2 ≤ 4)
  exact (radixValue_lt_scaled_power hq hD digits hbound).trans_le (hscale.trans hstep)

end Erdos790.Upper
