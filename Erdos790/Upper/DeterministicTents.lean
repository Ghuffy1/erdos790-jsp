import Erdos790.Upper.RowOffsets
import Erdos790.Upper.PeriodicTents
import Erdos790.Upper.AuxiliaryHost

/-!
# The deterministic tent translations

The only numerical hypothesis in the construction is the explicit radix
margin. The interval size, cardinality, divisibility, and uniform sum cover
are proved for the resulting finite integer host.
-/

namespace Erdos790.Upper.AuxiliaryParameters

def timeCount (d : ℕ) : ℕ := 2 ^ (2 * d)
def radixBase (d : ℕ) : ℕ := 2 ^ (6 * d)
def rowStep (d : ℕ) : ℕ := radixBase d ^ d / (8 * timeCount d)
def tentRow (d amplification : ℕ) (t : Fin (timeCount d)) (h : Fin d) : ℕ :=
  amplification * periodicTent (2 ^ (d + h.val)) t.val
def tentTranslations (d amplification : ℕ) : Finset ℕ :=
  rowOffsets (factorialModulus d) (rowStep d) (radixBase d) (tentRow d amplification)

theorem timeCount_pos (d : ℕ) : 0 < timeCount d := by unfold timeCount; positivity

theorem radixBase_pow (d : ℕ) : radixBase d ^ d = 2 ^ (6 * d ^ 2) := by
  unfold radixBase
  rw [← pow_mul]
  congr 1
  ring

theorem radixBase_pow_eq_four_blocks {d : ℕ} (hd : 0 < d) :
    radixBase d ^ d = 4 * blockCount d := by
  apply Nat.eq_of_mul_eq_mul_left (factorialModulus_pos d)
  calc
    factorialModulus d * radixBase d ^ d = baseRange d := by rw [radixBase_pow]; rfl
    _ = 4 * (blockCount d * factorialModulus d) := baseRange_eq_four_blocks hd
    _ = factorialModulus d * (4 * blockCount d) := by ring

theorem tent_period_le_timeCount {d : ℕ} (h : Fin d) :
    2 * 2 ^ (d + h.val) ≤ timeCount d := by
  rw [← pow_succ']
  exact Nat.pow_le_pow_right (by decide) (by omega)

theorem tentRow_bound (d amplification : ℕ) (t : Fin (timeCount d)) (h : Fin d) :
    tentRow d amplification t h ≤ amplification * timeCount d := by
  have htent := (periodicTent_bounds (t := t.val)
    (by positivity : 0 < 2 ^ (d + h.val))).2
  exact Nat.mul_le_mul_left amplification (htent.le.trans (tent_period_le_timeCount h))

theorem tent_row_separation {d amplification : ℕ} (hd : 0 < d)
    (hmargin : 32 * (amplification * timeCount d + 1) * timeCount d ≤ radixBase d) :
    (1 < radixBase d) ∧
      (∀ t h, tentRow d amplification t h + 1 < radixBase d) ∧
      (∀ t (bits : Fin d → Fin 2),
        radixValue (radixBase d) (fun h => tentRow d amplification t h + (bits h).val) < rowStep d) := by
  let D := amplification * timeCount d + 1
  have hT := timeCount_pos d
  have hD : 0 < D := by dsimp [D]; omega
  have hDT : D ≤ D * timeCount d := Nat.le_mul_of_pos_right _ hT
  have hlarge : D < radixBase d := by change 32 * D * timeCount d ≤ radixBase d at hmargin; nlinarith
  have hq : 1 < radixBase d := by omega
  refine ⟨hq, ?_, ?_⟩
  · intro t h
    exact (Nat.add_le_add_right (tentRow_bound d amplification t h) 1).trans_lt hlarge
  · intro t bits
    apply radixValue_lt_rowStep hd hD hT hmargin
    intro h
    have hrow := tentRow_bound d amplification t h
    have hbit := (bits h).isLt
    dsimp [D]
    omega

theorem tentTranslations_card {d amplification : ℕ} (hd : 0 < d)
    (hmargin : 32 * (amplification * timeCount d + 1) * timeCount d ≤ radixBase d) :
    (tentTranslations d amplification).card = 2 ^ (3 * d) := by
  obtain ⟨hq, hdigit, hrow⟩ := tent_row_separation hd hmargin
  rw [tentTranslations, rowOffsets_card _ (factorialModulus_pos d) hq hdigit hrow]
  unfold timeCount
  rw [← pow_add]
  congr 1
  omega

theorem tentTranslations_nonempty {d amplification : ℕ} (hd : 0 < d)
    (hmargin : 32 * (amplification * timeCount d + 1) * timeCount d ≤ radixBase d) :
    (tentTranslations d amplification).Nonempty := by
  apply Finset.card_pos.mp
  rw [tentTranslations_card hd hmargin]
  positivity

theorem tentTranslations_dvd {d amplification z : ℕ}
    (hz : z ∈ tentTranslations d amplification) : factorialModulus d ∣ z :=
  rowOffsets_dvd _ hz

theorem tentTranslations_bound {d amplification z : ℕ} (hd : 0 < d)
    (hmargin : 32 * (amplification * timeCount d + 1) * timeCount d ≤ radixBase d)
    (hz : z ∈ tentTranslations d amplification) :
    z < blockCount d * factorialModulus d := by
  obtain ⟨hq, hdigit, hrow⟩ := tent_row_separation hd hmargin
  have hzbound := rowOffsets_lt (tentRow d amplification) (factorialModulus_pos d) hrow hz
  have hdivision : rowStep d * (8 * timeCount d) ≤ radixBase d ^ d :=
    Nat.div_mul_le_self (radixBase d ^ d) (8 * timeCount d)
  have hstep : timeCount d * rowStep d ≤ blockCount d := by
    have hdivision' := hdivision.trans_eq (radixBase_pow_eq_four_blocks hd)
    nlinarith
  exact hzbound.trans_le (by
    have h := Nat.mul_le_mul_left (factorialModulus d) hstep
    simpa only [Nat.mul_comm] using h)

theorem tent_auxiliary_host_exists {d amplification : ℕ} (hd : 0 < d)
    (hmargin : 32 * (amplification * timeCount d + 1) * timeCount d ≤ radixBase d) :
    ∃ offset : Fin (sampleSize d) → ℕ,
      (∀ i, offset i < blockCount d * factorialModulus d ∧
        Nat.Coprime (offset i) (factorialModulus d)) ∧
      Function.Injective (fun i => offset i % factorialModulus d) ∧
      (translatedHost (baseRange d) offset (tentTranslations d amplification)).card =
        sampleSize d * (tentTranslations d amplification).card ∧
      (∀ x ∈ translatedHost (baseRange d) offset (tentTranslations d amplification),
        baseRange d ≤ x ∧ x < 2 * baseRange d ∧ Nat.Coprime x (factorialModulus d)) ∧
      SumCover (translatedHost (baseRange d) offset (tentTranslations d amplification))
        (2 * sampleExponent d * (tentTranslations d amplification).card) (sumThreshold d) := by
  apply auxiliary_host_exists hd _ (tentTranslations_nonempty hd hmargin)
    (by rw [tentTranslations_card hd hmargin])
  · intro z hz
    exact tentTranslations_dvd hz
  · intro z hz
    exact tentTranslations_bound hd hmargin hz

end Erdos790.Upper.AuxiliaryParameters
