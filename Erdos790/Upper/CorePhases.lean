import Erdos790.Upper.MeanCore
import Erdos790.Upper.StableLatticePeriod
import Erdos790.Upper.FinitePhases

/-!
# Complete counting after a lattice core has been seeded
-/

namespace Erdos790.Upper

theorem lattice_core_phase_mass_bound
    {A S : ℕ → Finset ℤ} {cut left u : ℤ}
    {d s width M initialModulus stop : ℕ} {initialSpan : ℝ}
    (hd : 48 ≤ d) (hs : 6 * s ≤ d) (hwidth : 12 * width ≤ d) (hwidthPos : 0 < width)
    (hM : 2 ^ d ≤ M) (hmodulus : clusterDensity s * initialModulus ≤ 2)
    (hseed : clusterDensity s * M / 8 ≤ initialSpan)
    (hpoint : ∀ j < stop, (S j).card ≤ M)
    (hsubset : ∀ j < stop, S j ⊆ A j)
    (hinterval : ∀ j < stop, S j ⊆ Finset.Ico left (left + M))
    (hforbidden : ∀ j < stop, ∀ x ∈ S j, ¬DyadicMean A cut j x) :
    ∀ fuel start core, start ≤ stop → stop - start ≤ width →
      MeanCoreValid A cut u left M initialModulus initialSpan start core →
      core.modulus < 2 ^ fuel →
      selectionMass S start stop ≤ fuel * (s + 28 + 3) * M := by
  apply finite_phase_mass_bound S
    (MeanCoreValid A cut u left M initialModulus initialSpan) MeanCoreData.modulus
    (fun j core => ∃ x ∈ S j, ¬(core.modulus : ℤ) ∣ x - u)
    stop width (s + 28) M hpoint
  · intro t core hv
    exact hv.positive
  · intro t finish core htf hfinish hshort hv hclear
    unfold selectionMass
    apply cluster_stable_lattice_period hd hs hwidth hwidthPos hM hv.positive hshort
      hv.lower_class hv.upper_class hv.ordered hv.inside_left hv.inside_right
      (hv.modulus_bound hmodulus) (hv.span_lower hmodulus hseed) hv.means
    · intro i hi
      exact hsubset (t + i) (by omega)
    · intro i hi
      exact hinterval (t + i) (by omega)
    · intro i hi x hx
      by_contra hoff
      exact hclear (t + i) (by omega) (by omega) ⟨x, hx, hoff⟩
    · intro i hi x hx
      exact hforbidden (t + i) (by omega) x hx
  · intro t j core hv ht hj hbad
    obtain ⟨x, hx, hoff⟩ := hbad
    exact hv.refine hd hs hM hmodulus hseed ht (hsubset j hj hx) (hinterval j hj hx) hoff

theorem seeded_later_mass_bound
    {A S : ℕ → Finset ℤ} {cut left u p q : ℤ} {d s width M g start stop : ℕ}
    (hd : 48 ≤ d) (hs : 6 * s ≤ d) (hwidth : 12 * width ≤ d) (hwidthPos : 0 < width)
    (hM : 2 ^ d ≤ M) (hg : 0 < g) (hmodulus : clusterDensity s * g ≤ 2)
    (hstart : start ≤ stop) (hshort : stop - start ≤ width)
    (hp : (g : ℤ) ∣ p - u) (hq : (g : ℤ) ∣ q - u)
    (hpq : p ≤ q) (hleft : left ≤ p) (hright : q < left + M)
    (hseed : clusterDensity s * M / 8 ≤ ((q - p : ℤ) : ℝ))
    (hcore : ∀ x : ℤ, p ≤ x → x ≤ q → (g : ℤ) ∣ x - u → DyadicMean A cut start x)
    (hpoint : ∀ j < stop, (S j).card ≤ M)
    (hsubset : ∀ j < stop, S j ⊆ A j)
    (hinterval : ∀ j < stop, S j ⊆ Finset.Ico left (left + M))
    (hforbidden : ∀ j < stop, ∀ x ∈ S j, ¬DyadicMean A cut j x) :
    selectionMass S start stop ≤ (s + 16) * (s + 31) * M := by
  let core : MeanCoreData := ⟨g, p, q⟩
  have hvalid : MeanCoreValid A cut u left M g ((q - p : ℤ) : ℝ) start core := {
    positive := hg
    modulus_le := le_rfl
    lower_class := hp
    upper_class := hq
    ordered := hpq
    inside_left := hleft
    inside_right := hright
    span_invariant := le_rfl
    means := hcore
  }
  have hpower : g < 2 ^ (s + 16) := by
    simpa only [add_zero] using seed_power_room (g := g) (K := 0)
      (clusterDensity_pos s) (clusterDensity_le_one s) hmodulus (by norm_num)
      (cluster_seed_delay_budget s)
  have h := lattice_core_phase_mass_bound hd hs hwidth hwidthPos hM hmodulus hseed
    hpoint hsubset hinterval hforbidden (s + 16) start core hstart hshort hvalid hpower
  simpa only [show s + 28 + 3 = s + 31 by omega] using h

end Erdos790.Upper
