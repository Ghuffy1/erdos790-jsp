import Erdos790.Upper.CharacterReduction
import Erdos790.Upper.RoughSampling

/-!
# Auxiliary offsets for all required characters

The finite tests include every admissible modulus, nonzero character index,
and prescribed translation. The output offsets are pairwise distinct modulo
the factorial, and each test has fewer than `k` exceptional indices.
-/

namespace Erdos790.Upper

theorem phase_separated_offsets {m X J v L k : ℕ} (translations : Finset ℕ)
    (hm : 0 < m) (hv : 0 < v) (hL : 0 < L) (hJ : J = 2 * L * k)
    (hX : X = 4 * (m * (v ^ 2).factorial))
    (hscale : 14400 * L ≤ v) (hcollisions : 4 * J ^ 2 ≤ (v ^ 2).factorial.totient)
    (htests : ((4 * X ^ 2 * translations.card : ℕ) : ℝ) *
      Real.exp (-(k : ℝ) / 2) ≤ 1 / 2) :
    ∃ offset : Fin J → ℕ,
      (∀ i, offset i < m * (v ^ 2).factorial ∧
        Nat.Coprime (offset i) (v ^ 2).factorial) ∧
      Function.Injective (fun i => offset i % (v ^ 2).factorial) ∧
      ∀ (M : ℕ) [NeZero M], X ≤ M → M < 2 * X →
        Nat.Coprime M (v ^ 2).factorial →
        ∀ z ∈ translations, ∀ a : ZMod M, a ≠ 0 →
          ((Finset.univ : Finset (Fin J)).filter (fun i =>
            ‖1 - ZMod.stdAddChar (-((X + offset i + z : ℕ) : ZMod M) * a)‖ <
              4 / (v ^ 2 : ℕ))).card < k := by
  classical
  let Q := (v ^ 2).factorial
  letI : NeZero Q := ⟨Nat.factorial_ne_zero _⟩
  have hXpos : 0 < X := by rw [hX]; positivity
  let raw := ((Finset.range (2 * X)) ×ˢ (Finset.range (2 * X))) ×ˢ translations
  let tests := raw.filter (fun t =>
    X ≤ t.1.1 ∧ 0 < t.1.2 ∧ t.1.2 < t.1.1 ∧ Nat.Coprime t.1.1 Q)
  let T := {t // t ∈ tests}
  have hdata : ∀ t : T, X ≤ t.val.1.1 ∧ 0 < t.val.1.2 ∧ t.val.1.2 < t.val.1.1 ∧
      Nat.Coprime t.val.1.1 Q := fun t => (Finset.mem_filter.mp t.property).2
  have hMsmall : ∀ t : T, t.val.1.1 < 2 * X := by
    intro t
    exact Finset.mem_range.mp
      (Finset.mem_product.mp (Finset.mem_product.mp
        (Finset.mem_filter.mp t.property).1).1).1
  have hreductions : ∀ t : T, ∃ p u g : ℕ, v ^ 2 < p ∧ 0 < g ∧
      Nat.Coprime u p ∧ t.val.1.1 = p * g ∧ t.val.1.2 = u * g := by
    intro t
    exact rough_character_reduction (lt_of_lt_of_le hXpos (hdata t).1)
      (hdata t).2.1 (hdata t).2.2.1 (hdata t).2.2.2
  choose p u g hp hg hcoprime hM hA using hreductions
  letI : ∀ t : T, NeZero (p t) := fun t => ⟨by have h := hp t; omega⟩
  let f := fun (t : T) (b : ZMod (p t)) =>
    -((u t : ZMod (p t)) * ((X + t.val.2 : ℕ) + b))
  have hcard : Fintype.card T ≤ 4 * X ^ 2 * translations.card := by
    calc
      Fintype.card T = tests.card := Fintype.card_coe _
      _ ≤ raw.card := Finset.card_filter_le _ _
      _ = 4 * X ^ 2 * translations.card := by
        simp only [raw, Finset.card_product, Finset.card_range]
        ring
  have htests' : (Fintype.card T : ℝ) * Real.exp (-(k : ℝ) / 2) ≤ 1 / 2 := by
    exact (mul_le_mul_of_nonneg_right (by exact_mod_cast hcard)
      (Real.exp_pos _).le).trans htests
  have hwindow : ∀ t : T, p t ≤ 8 * (m * Q) := by
    intro t
    have hle : p t ≤ t.val.1.1 := by
      rw [hM t]
      exact Nat.le_mul_of_pos_right _ (hg t)
    have hsmall := hMsmall t
    dsimp [Q]
    omega
  obtain ⟨offset, hoffset, hinjective, hbad⟩ := cyclic_tests_rough_offsets p f
    (fun t => reduced_phase_injective (hcoprime t) (X + t.val.2))
    hm hv hL hJ (factorial_totient_density hv le_rfl) hscale
    (fun t => (hp t).le) hwindow hcollisions htests'
  refine ⟨offset, hoffset, hinjective, ?_⟩
  intro M instM hXM hMX hrough z hz a ha
  have ha0 : 0 < a.val := by
    have haval : a.val ≠ 0 := by
      intro h
      apply ha
      rw [← ZMod.natCast_zmod_val a, h]
      simp
    omega
  let t : T := ⟨((M, a.val), z), Finset.mem_filter.mpr ⟨
    Finset.mem_product.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr hMX,
        Finset.mem_range.mpr ((ZMod.val_lt a).trans hMX)⟩, hz⟩,
    ⟨hXM, ha0, ZMod.val_lt a, hrough⟩⟩⟩
  have hsubset : (Finset.univ.filter (fun i : Fin J =>
      ‖1 - ZMod.stdAddChar (-((X + offset i + z : ℕ) : ZMod M) * a)‖ <
        4 / (v ^ 2 : ℕ))) ⊆
      Finset.univ.filter (fun i : Fin J =>
        f t (offset i : ZMod (p t)) ∈ nearZeroResidues (p t) (p t / v ^ 2 + 1)) := by
    intro i hi
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    by_contra hnot
    have hchord := not_nearZero_chord_lower (by positivity : 0 < v ^ 2)
      (f t (offset i : ZMod (p t))) hnot
    have hid := reduced_character_identity (hg t) (hM t) (hA t) (X + offset i + z)
    have hargM : -(((a.val : ℕ) : ZMod M) * ((X + offset i + z : ℕ) : ZMod M)) =
        -((X + offset i + z : ℕ) : ZMod M) * a := by
      rw [ZMod.natCast_zmod_val]
      ring
    have hargp : -((u t : ZMod (p t)) * ((X + offset i + z : ℕ) : ZMod (p t))) =
        f t (offset i : ZMod (p t)) := by
      dsimp [f, t]
      push_cast
      ring
    change ZMod.stdAddChar (-(((a.val : ℕ) : ZMod M) *
      ((X + offset i + z : ℕ) : ZMod M))) = _ at hid
    rw [hargM, hargp] at hid
    rw [← hid] at hchord
    exact (not_lt_of_ge hchord) (Finset.mem_filter.mp hi).2
  exact (Finset.card_le_card hsubset).trans_lt (hbad t)

end Erdos790.Upper
