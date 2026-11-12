import Erdos790.Upper.TranslatedHost

/-!
# Dense subsets of the translated host represent large integers
-/

namespace Erdos790.Upper

theorem exists_dense_translation {J Q X k : ℕ} (offset : Fin J → ℕ)
    (translations : Finset ℕ) (htranslations : translations.Nonempty)
    (hX : Q ∣ X) (hz : ∀ z ∈ translations, Q ∣ z)
    (hinjective : Function.Injective (fun i => offset i % Q))
    {S : Finset ℕ} (hS : S ⊆ translatedHost X offset translations)
    (hcard : 2 * k * translations.card ≤ S.card) :
    ∃ z ∈ translations,
      2 * k ≤ (Finset.univ.filter (fun i : Fin J => X + offset i + z ∈ S)).card := by
  classical
  let I := Fin J × ↥translations
  let value := fun p : I => X + offset p.1 + p.2.val
  let selected := Finset.univ.filter (fun p : I => value p ∈ S)
  have hinj : Function.Injective value :=
    translatedHost_injective offset translations hX hz hinjective
  have himage : selected.image value = S := by
    ext x
    constructor
    · intro hx
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
      exact (Finset.mem_filter.mp hp).2
    · intro hx
      obtain ⟨p, _, hp⟩ := Finset.mem_image.mp (hS hx)
      have hp' : value p = x := hp
      exact Finset.mem_image.mpr
        ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp'.symm ▸ hx⟩, hp⟩
  have hselected : selected.card = S.card := by
    rw [← himage, Finset.card_image_of_injective _ hinj]
  have hnonempty : (Finset.univ : Finset ↥translations).Nonempty := by
    obtain ⟨z, hz⟩ := htranslations
    exact ⟨⟨z, hz⟩, Finset.mem_univ _⟩
  obtain ⟨z, _, hlarge⟩ := Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to
    (s := selected) (t := (Finset.univ : Finset ↥translations)) (f := fun p : I => p.2)
    (n := 2 * k)
    (fun _ _ => Finset.mem_univ _) hnonempty
    (by simpa only [Finset.card_univ, Fintype.card_coe, hselected, Nat.mul_comm] using hcard)
  let indices := Finset.univ.filter (fun i : Fin J => X + offset i + z.val ∈ S)
  have hfiber : selected.filter (fun p : I => p.2 = z) =
      indices.image (fun i => (i, z)) := by
    ext p
    rcases p with ⟨i, z'⟩
    simp only [selected, value, indices, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_image]
    constructor
    · rintro ⟨hi, rfl⟩
      exact ⟨i, hi, rfl⟩
    · rintro ⟨i', hi, hpair⟩
      rcases Prod.mk.inj hpair with ⟨rfl, rfl⟩
      exact ⟨hi, rfl⟩
  rw [hfiber, Finset.card_image_of_injective _
    (fun i j h => congrArg Prod.fst h)] at hlarge
  exact ⟨z.val, z.property, hlarge⟩

theorem phase_separated_selected_fiber {J X k B : ℕ} {p : ℝ}
    (offset : Fin J → ℕ) (z : ℕ) {S : Finset ℕ}
    (hX : 0 < X) (hp : 0 < p) (hB : 100 * p ≤ B)
    (hS : ∀ x ∈ S, X ≤ x ∧ x < 2 * X)
    (hcard : 2 * k ≤ (Finset.univ.filter (fun i : Fin J => X + offset i + z ∈ S)).card)
    (hk : 0 < k)
    (hsmall : ∀ M ∈ S, (M : ℝ) * (1 / 200 : ℝ) ^ k < 1)
    (hphase : ∀ (M : ℕ) [NeZero M], M ∈ S → ∀ a : ZMod M, a ≠ 0 →
      (Finset.univ.filter (fun i : Fin J =>
        ‖1 - ZMod.stdAddChar (-((X + offset i + z : ℕ) : ZMod M) * a)‖ < 4 / p)).card < k) :
    ∀ N : ℕ, 2 * J * B * X ≤ N → ∃ T : List ℕ,
      (∀ x ∈ T, x ∈ S) ∧ T.sum = N ∧ T.length ≤ N / X := by
  classical
  let indices := Finset.univ.filter (fun i : Fin J => X + offset i + z ∈ S)
  have hindices : indices.Nonempty := Finset.card_pos.mp (by dsimp [indices]; omega)
  obtain ⟨i0, hi0⟩ := hindices
  let M := X + offset i0 + z
  have hM : M ∈ S := (Finset.mem_filter.mp hi0).2
  letI : NeZero M := ⟨by have h := (hS M hM).1; omega⟩
  let value := fun i : ↥indices => X + offset i.val + z
  have hcount : Fintype.card ↥indices ≤ J := by
    calc
      Fintype.card ↥indices = indices.card := Fintype.card_coe _
      _ ≤ (Finset.univ : Finset (Fin J)).card := Finset.card_filter_le _ _
      _ = J := by simp
  apply phase_separated_fiber_sums_of_fintype value hX hp hB
    hcount hM hS
    (fun i => (Finset.mem_filter.mp i.property).2) (hsmall M hM)
  intro a ha
  let bad := Finset.univ.filter (fun i : ↥indices =>
    ‖1 - ZMod.stdAddChar (-((value i : ZMod M) * a))‖ < 4 / p)
  let good := Finset.univ \ bad
  have hbad : bad.card < k := by
    have himage : bad.image (fun i : ↥indices => i.val) ⊆
        Finset.univ.filter (fun i : Fin J =>
          ‖1 - ZMod.stdAddChar (-((X + offset i + z : ℕ) : ZMod M) * a)‖ < 4 / p) := by
      intro i hi
      obtain ⟨i', hi', rfl⟩ := Finset.mem_image.mp hi
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      simpa only [value, neg_mul] using (Finset.mem_filter.mp hi').2
    have hle := Finset.card_le_card himage
    rw [Finset.card_image_of_injective _ Subtype.val_injective] at hle
    exact hle.trans_lt (hphase M hM a ha)
  have hgood : k ≤ good.card := by
    have hsum : good.card + bad.card = indices.card := by
      simpa only [good, Finset.card_univ, Fintype.card_coe] using
        Finset.card_sdiff_add_card_eq_card (Finset.subset_univ bad : bad ⊆ Finset.univ)
    change 2 * k ≤ indices.card at hcard
    omega
  obtain ⟨chosen, hchosen, hchosenCard⟩ := Finset.exists_subset_card_eq hgood
  refine ⟨chosen, hchosenCard, ?_⟩
  intro i hi
  have hnot := (Finset.mem_sdiff.mp (hchosen hi)).2
  have hge : 4 / p ≤ ‖1 - ZMod.stdAddChar (-((value i : ZMod M) * a))‖ := by
    simpa only [bad, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] using hnot
  simpa only [neg_mul] using hge

theorem translatedHost_sumCover {J Q X N k B : ℕ} {p : ℝ}
    (offset : Fin J → ℕ) (translations : Finset ℕ)
    (htranslations : translations.Nonempty) (hXpos : 0 < X) (hX : X = 4 * N)
    (hXdiv : Q ∣ X) (hzdiv : ∀ z ∈ translations, Q ∣ z)
    (hoffset : ∀ i, offset i < N ∧ Nat.Coprime (offset i) Q)
    (hz : ∀ z ∈ translations, z < N)
    (hinjective : Function.Injective (fun i => offset i % Q))
    (hk : 0 < k) (hp : 0 < p) (hB : 100 * p ≤ B)
    (htail : ((2 * X : ℕ) : ℝ) * (1 / 200 : ℝ) ^ k < 1)
    (hphase : ∀ (M : ℕ) [NeZero M], X ≤ M → M < 2 * X → Nat.Coprime M Q →
      ∀ z ∈ translations, ∀ a : ZMod M, a ≠ 0 →
        (Finset.univ.filter (fun i : Fin J =>
          ‖1 - ZMod.stdAddChar (-((X + offset i + z : ℕ) : ZMod M) * a)‖ < 4 / p)).card < k) :
    SumCover (translatedHost X offset translations) (2 * k * translations.card) (2 * J * B * X) := by
  intro S hS hcard target htarget
  obtain ⟨z, hzmem, hlarge⟩ := exists_dense_translation offset translations htranslations
    hXdiv hzdiv hinjective hS hcard
  have hbounds : ∀ x ∈ S, X ≤ x ∧ x < 2 * X := fun x hx =>
    translatedHost_bounds offset translations hX (fun i => (hoffset i).1) hz (hS hx)
  have hsmall : ∀ M ∈ S, (M : ℝ) * (1 / 200 : ℝ) ^ k < 1 := by
    intro M hM
    have hle : (M : ℝ) ≤ ((2 * X : ℕ) : ℝ) := by exact_mod_cast (hbounds M hM).2.le
    exact (mul_le_mul_of_nonneg_right hle (by positivity)).trans_lt htail
  have hphase' : ∀ (M : ℕ) [NeZero M], M ∈ S → ∀ a : ZMod M, a ≠ 0 →
      (Finset.univ.filter (fun i : Fin J =>
        ‖1 - ZMod.stdAddChar (-((X + offset i + z : ℕ) : ZMod M) * a)‖ < 4 / p)).card < k := by
    intro M instM hM a ha
    exact hphase M (hbounds M hM).1 (hbounds M hM).2
      (translatedHost_coprime offset translations hXdiv hzdiv
        (fun i => (hoffset i).2) (hS hM)) z hzmem a ha
  obtain ⟨terms, hterms, hsum, _⟩ := phase_separated_selected_fiber offset z hXpos hp hB
    hbounds hlarge hk hsmall hphase' target htarget
  exact ⟨terms, hterms, hsum⟩

end Erdos790.Upper
