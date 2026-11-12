import Erdos790.Upper.LevelClusters
import Erdos790.Upper.ClusterRecurrence

/-!
# Partitioning the heavy-level mass and summing distinct cluster ranks
-/

namespace Erdos790.Upper

theorem levelClusters_cover (S : Finset ℕ) {width : ℕ} (hwidth : 0 < width) :
    (clusterStarts S width hwidth).biUnion (levelCluster S width) = S := by
  classical
  ext j
  constructor
  · intro hj
    obtain ⟨a, ha, hj⟩ := Finset.mem_biUnion.mp hj
    exact (Finset.mem_filter.mp hj).1
  · intro hj
    let seed : ↥S := ⟨j, hj⟩
    let a := clusterStart S width hwidth seed
    have ha : a ∈ clusterStarts S width hwidth :=
      Finset.mem_image.mpr ⟨seed, Finset.mem_univ _, rfl⟩
    have hclose := (clusterStart_spec hwidth seed).2.2
    exact Finset.mem_biUnion.mpr ⟨a, ha, Finset.mem_filter.mpr ⟨hj, hclose.symm⟩⟩

theorem levelClusters_pairwise_disjoint {S : Finset ℕ} {width separation : ℕ}
    (hwidth : 0 < width) (hseparation : 2 * width ≤ separation)
    (hgap : MediumGapFree S width separation) :
    (clusterStarts S width hwidth : Set ℕ).PairwiseDisjoint (levelCluster S width) := by
  intro a ha b hb hab
  apply Finset.disjoint_left.mpr
  intro j hja hjb
  have hca := (Finset.mem_filter.mp hja).2
  have hcb := (Finset.mem_filter.mp hjb).2
  have hac : a ∈ S := clusterStarts_subset hwidth ha
  have hbc : b ∈ S := clusterStarts_subset hwidth hb
  have hclose := levelClose_trans hwidth hseparation hgap hac hbc hca hcb.symm
  rcases lt_or_gt_of_ne hab with hlt | hgt
  · have hfar := clusterStarts_separated hwidth hseparation hgap ha hb hlt
    obtain ⟨_, hclose⟩ := hclose
    omega
  · have hfar := clusterStarts_separated hwidth hseparation hgap hb ha hgt
    obtain ⟨hclose, _⟩ := hclose
    omega

theorem levelClusters_sum {S : Finset ℕ} {width separation : ℕ}
    (hwidth : 0 < width) (hseparation : 2 * width ≤ separation)
    (hgap : MediumGapFree S width separation) (weight : ℕ → ℝ) :
    (∑ j ∈ S, weight j) = ∑ a ∈ clusterStarts S width hwidth,
      ∑ j ∈ levelCluster S width a, weight j := by
  classical
  have h := Finset.sum_biUnion (f := weight)
    (levelClusters_pairwise_disjoint hwidth hseparation hgap)
  rw [levelClusters_cover S hwidth] at h
  exact h

theorem preceding_count_strict {S : Finset ℕ} {a b : ℕ} (ha : a ∈ S) (hab : a < b) :
    (S.filter (fun i => i < a)).card < (S.filter (fun i => i < b)).card := by
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨?_, ?_⟩
  · intro i hi
    obtain ⟨hi, hia⟩ := Finset.mem_filter.mp hi
    exact Finset.mem_filter.mpr ⟨hi, hia.trans hab⟩
  · intro heq
    have hamem : a ∈ S.filter (fun i => i < b) := Finset.mem_filter.mpr ⟨ha, hab⟩
    rw [← heq] at hamem
    exact (Nat.lt_irrefl a) (Finset.mem_filter.mp hamem).2

theorem preceding_count_injective (S : Finset ℕ) :
    Set.InjOn (fun a => (S.filter (fun i => i < a)).card) ↑S := by
  intro a ha b hb heq
  by_contra hne
  rcases lt_or_gt_of_ne hne with hab | hba
  · exact (ne_of_lt (preceding_count_strict ha hab)) heq
  · exact (ne_of_lt (preceding_count_strict hb hba)) heq.symm

theorem cluster_rank_sum_le_tsum (S : Finset ℕ) {weight : ℕ → ℝ}
    (hnonneg : ∀ n, 0 ≤ weight n) (hsummable : Summable weight) :
    (∑ a ∈ S, weight (S.filter (fun i => i < a)).card) ≤ ∑' n, weight n := by
  classical
  rw [← Finset.sum_image (preceding_count_injective S)]
  exact Summable.sum_le_tsum _ (fun n hn => hnonneg n) hsummable

end Erdos790.Upper
