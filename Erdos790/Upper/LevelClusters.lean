import Mathlib.Data.Finset.Max
import Mathlib.Tactic

/-!
# Canonical clusters for a finite set with a forbidden gap interval
-/

namespace Erdos790.Upper

def LevelClose (width a b : ℕ) : Prop := a < b + width ∧ b < a + width

instance (width a b : ℕ) : Decidable (LevelClose width a b) :=
  inferInstanceAs (Decidable (a < b + width ∧ b < a + width))

def MediumGapFree (S : Finset ℕ) (width separation : ℕ) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, a < b → width ≤ b - a → separation ≤ b - a

theorem levelClose_refl {width : ℕ} (hwidth : 0 < width) (a : ℕ) : LevelClose width a a := by
  constructor <;> omega

theorem LevelClose.symm {width a b : ℕ} (h : LevelClose width a b) : LevelClose width b a :=
  ⟨h.2, h.1⟩

theorem levelClose_trans {S : Finset ℕ} {width separation a b c : ℕ}
    (hwidth : 0 < width) (hseparation : 2 * width ≤ separation)
    (hgap : MediumGapFree S width separation)
    (ha : a ∈ S) (hc : c ∈ S)
    (hab : LevelClose width a b) (hbc : LevelClose width b c) : LevelClose width a c := by
  obtain ⟨hab, hba⟩ := hab
  obtain ⟨hbc, hcb⟩ := hbc
  constructor
  · by_contra hnot
    have hca : c < a := by omega
    have hlarge := hgap c hc a ha hca (by omega)
    omega
  · by_contra hnot
    have hac : a < c := by omega
    have hlarge := hgap a ha c hc hac (by omega)
    omega

def levelCluster (S : Finset ℕ) (width seed : ℕ) : Finset ℕ :=
  S.filter (LevelClose width seed)

theorem levelCluster_nonempty {S : Finset ℕ} {width seed : ℕ}
    (hwidth : 0 < width) (hseed : seed ∈ S) : (levelCluster S width seed).Nonempty :=
  ⟨seed, Finset.mem_filter.mpr ⟨hseed, levelClose_refl hwidth seed⟩⟩

noncomputable def clusterStart (S : Finset ℕ) (width : ℕ) (hwidth : 0 < width) (seed : ↥S) : ℕ :=
  (levelCluster S width seed.val).min' (levelCluster_nonempty hwidth seed.property)

theorem clusterStart_spec {S : Finset ℕ} {width : ℕ} (hwidth : 0 < width) (seed : ↥S) :
    clusterStart S width hwidth seed ∈ S ∧ clusterStart S width hwidth seed ≤ seed.val ∧
      LevelClose width seed.val (clusterStart S width hwidth seed) := by
  have hmem := Finset.min'_mem (levelCluster S width seed.val)
    (levelCluster_nonempty hwidth seed.property)
  have hle := Finset.min'_le (levelCluster S width seed.val) seed.val
    (Finset.mem_filter.mpr ⟨seed.property, levelClose_refl hwidth seed.val⟩)
  exact ⟨(Finset.mem_filter.mp hmem).1, hle, (Finset.mem_filter.mp hmem).2⟩

theorem levelCluster_eq_of_close {S : Finset ℕ} {width separation a b : ℕ}
    (hwidth : 0 < width) (hseparation : 2 * width ≤ separation)
    (hgap : MediumGapFree S width separation) (ha : a ∈ S) (hb : b ∈ S)
    (hab : LevelClose width a b) : levelCluster S width a = levelCluster S width b := by
  ext c
  simp only [levelCluster, Finset.mem_filter]
  constructor
  · rintro ⟨hc, hac⟩
    exact ⟨hc, levelClose_trans hwidth hseparation hgap hb hc hab.symm hac⟩
  · rintro ⟨hc, hbc⟩
    exact ⟨hc, levelClose_trans hwidth hseparation hgap ha hc hab hbc⟩

theorem clusterStart_eq_of_close {S : Finset ℕ} {width separation : ℕ}
    (hwidth : 0 < width) (hseparation : 2 * width ≤ separation)
    (hgap : MediumGapFree S width separation) (a b : ↥S)
    (hab : LevelClose width a.val b.val) :
    clusterStart S width hwidth a = clusterStart S width hwidth b := by
  have heq := levelCluster_eq_of_close hwidth hseparation hgap a.property b.property hab
  unfold clusterStart
  simp only [heq]

noncomputable def clusterStarts (S : Finset ℕ) (width : ℕ) (hwidth : 0 < width) : Finset ℕ :=
  Finset.univ.image (clusterStart S width hwidth)

theorem clusterStarts_subset {S : Finset ℕ} {width : ℕ} (hwidth : 0 < width) :
    clusterStarts S width hwidth ⊆ S := by
  intro a ha
  obtain ⟨seed, _, rfl⟩ := Finset.mem_image.mp ha
  exact (clusterStart_spec hwidth seed).1

theorem clusterStarts_separated {S : Finset ℕ} {width separation a b : ℕ}
    (hwidth : 0 < width) (hseparation : 2 * width ≤ separation)
    (hgap : MediumGapFree S width separation)
    (ha : a ∈ clusterStarts S width hwidth) (hb : b ∈ clusterStarts S width hwidth)
    (hab : a < b) : a + separation ≤ b := by
  obtain ⟨sa, _, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨sb, _, rfl⟩ := Finset.mem_image.mp hb
  have hsa := clusterStart_spec hwidth sa
  have hsb := clusterStart_spec hwidth sb
  have hfar : width ≤ clusterStart S width hwidth sb - clusterStart S width hwidth sa := by
    by_contra hnot
    have hclose : LevelClose width (clusterStart S width hwidth sa) (clusterStart S width hwidth sb) := by
      constructor <;> omega
    have hmiddle := levelClose_trans hwidth hseparation hgap sa.property hsb.1 hsa.2.2 hclose
    have hseeds := levelClose_trans hwidth hseparation hgap sa.property sb.property hmiddle hsb.2.2.symm
    have heq := clusterStart_eq_of_close hwidth hseparation hgap sa sb hseeds
    omega
  have hlarge := hgap _ hsa.1 _ hsb.1 hab hfar
  omega

theorem cluster_member_bounds {S : Finset ℕ} {width separation start j : ℕ}
    (hwidth : 0 < width) (hseparation : 2 * width ≤ separation)
    (hgap : MediumGapFree S width separation)
    (hstart : start ∈ clusterStarts S width hwidth)
    (hj : j ∈ levelCluster S width start) : start ≤ j ∧ j < start + width := by
  obtain ⟨seed, _, rfl⟩ := Finset.mem_image.mp hstart
  obtain ⟨hjS, hclose⟩ := Finset.mem_filter.mp hj
  have hseed := clusterStart_spec hwidth seed
  have hseedj := levelClose_trans hwidth hseparation hgap seed.property hjS hseed.2.2 hclose
  have heq := clusterStart_eq_of_close hwidth hseparation hgap seed ⟨j, hjS⟩ hseedj
  have hmin := (clusterStart_spec hwidth (⟨j, hjS⟩ : ↥S)).2.1
  rw [← heq] at hmin
  exact ⟨hmin, hclose.2⟩

end Erdos790.Upper
