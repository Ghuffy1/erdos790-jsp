import Erdos790.Upper.RoughChoices
import Erdos790.Upper.SamplingCollisions
import Erdos790.Upper.TotientDensity

/-!
# Simultaneously choosing rough, residue-distinct offsets
-/

namespace Erdos790.Upper

theorem rough_offsets_selection {T : Type*} [Fintype T]
    {m Q J v L k : ℕ} [NeZero Q] (bad : T → Finset ℕ)
    (hm : 0 < m) (hv : 0 < v) (hL : 0 < L) (hJ : J = 2 * L * k)
    (hQ : Q ≤ 4 * v * Q.totient) (hscale : 14400 * L ≤ v)
    (hbad : ∀ t, (bad t).card * v ^ 2 ≤ 36 * (m * Q))
    (hcollisions : 4 * J ^ 2 ≤ Q.totient)
    (htests : (Fintype.card T : ℝ) * Real.exp (-(k : ℝ) / 2) ≤ 1 / 2) :
    ∃ offset : Fin J → ℕ,
      (∀ i, offset i < m * Q ∧ Nat.Coprime (offset i) Q) ∧
      Function.Injective (fun i => offset i % Q) ∧
      ∀ t, ((Finset.univ : Finset (Fin J)).filter (fun i => offset i ∈ bad t)).card < k := by
  letI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have hbadFraction : ∀ t, ((roughBadChoices m Q (bad t)).card : ℝ) ≤
      Fintype.card (RoughChoice m Q) / (100 * (L : ℝ)) := by
    intro t
    have h := roughBadChoices_fraction (bad t) hv hQ hscale (hbad t)
    have hreal : 100 * (L : ℝ) * (roughBadChoices m Q (bad t)).card ≤
        Fintype.card (RoughChoice m Q) := by exact_mod_cast h
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 100 * L)).mpr
    nlinarith
  have hcollision : 4 * (Fintype.card (Fin J)) ^ 2 * m ≤
      Fintype.card (RoughChoice m Q) := by
    rw [Fintype.card_fin, roughChoice_card]
    simpa only [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm] using
      Nat.mul_le_mul_right m hcollisions
  obtain ⟨sample, hinjective, htests'⟩ := exists_injective_sample_with_few_bad
    (fun t => roughBadChoices m Q (bad t))
    (fun choice : RoughChoice m Q => choice.2) m hL
    (by simpa using hJ) hbadFraction
    (fun residue => (roughChoice_residue_fiber m Q residue).le) hcollision htests
  refine ⟨fun i => roughOffset (sample i), ?_, ?_, ?_⟩
  · intro i
    exact ⟨roughOffset_lt _, roughOffset_coprime _⟩
  · intro i j hij
    apply hinjective
    apply Units.ext
    apply ZMod.val_injective Q
    simpa only [roughOffset_mod] using hij
  · intro t
    simpa only [sampleBadCount, roughBadChoices, Finset.mem_filter,
      Finset.mem_univ, true_and] using htests' t

theorem cyclic_tests_rough_offsets {T : Type*} [Fintype T]
    {m Q J v L k : ℕ} [NeZero Q] (p : T → ℕ) [∀ t, NeZero (p t)]
    (f : ∀ t, ZMod (p t) → ZMod (p t))
    (hf : ∀ t, Function.Injective (f t))
    (hm : 0 < m) (hv : 0 < v) (hL : 0 < L) (hJ : J = 2 * L * k)
    (hQ : Q ≤ 4 * v * Q.totient) (hscale : 14400 * L ≤ v)
    (hp : ∀ t, v ^ 2 ≤ p t) (hwindow : ∀ t, p t ≤ 8 * (m * Q))
    (hcollisions : 4 * J ^ 2 ≤ Q.totient)
    (htests : (Fintype.card T : ℝ) * Real.exp (-(k : ℝ) / 2) ≤ 1 / 2) :
    ∃ offset : Fin J → ℕ,
      (∀ i, offset i < m * Q ∧ Nat.Coprime (offset i) Q) ∧
      Function.Injective (fun i => offset i % Q) ∧
      ∀ t, ((Finset.univ : Finset (Fin J)).filter
        (fun i => f t (offset i : ZMod (p t)) ∈ nearZeroResidues (p t) (p t / v ^ 2 + 1))).card < k := by
  let bad := fun t => residuePrefix (m * Q) (p t) (f t)
    (nearZeroResidues (p t) (p t / v ^ 2 + 1))
  obtain ⟨offset, hoffset, hinjective, hbad⟩ := rough_offsets_selection bad
    hm hv hL hJ hQ hscale
    (fun t => nearZero_prefix_window_bound (hp t) (hwindow t) (f t) (hf t))
    hcollisions htests
  refine ⟨offset, hoffset, hinjective, ?_⟩
  intro t
  have hset : ((Finset.univ : Finset (Fin J)).filter (fun i => offset i ∈ bad t)) =
      (Finset.univ : Finset (Fin J)).filter
        (fun i => f t (offset i : ZMod (p t)) ∈ nearZeroResidues (p t) (p t / v ^ 2 + 1)) := by
    ext i
    simp only [bad, residuePrefix, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_range, and_iff_right (hoffset i).1]
  rw [← hset]
  exact hbad t

end Erdos790.Upper
