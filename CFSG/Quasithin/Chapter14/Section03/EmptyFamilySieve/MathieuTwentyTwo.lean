module
public import CFSG.Quasithin.Chapter14.Section03.EmptyFamilySieve.InvariantCubicPlacement
public import CFSG.Quasithin.Chapter14.Section03.EmptyFamilySieve.PerfectImageRank
public import Theory.Mathieu.M22.CubicHexadCover
public import Theory.Mathieu.M22.TripleCover

/-!
# The M₂₂ rows of the original empty-family sieve

The two Sylow-invariant cubic subgroups of M₂₂ generate its perfect hexad
section. Their canonical lifts through the genuine central-three cover
retain a perfect subgroup of three-rank at least two. Original 14.3.5 puts
these cubic lifts in the image of M. Original 14.1.18 bounds every perfect
subgroup of that image by three-rank one, giving the contradiction.

The ambient Sylow only normalizes K. The final two exports consume the
literal source equality K = ⟨K^T⟩. Source: Aschbacher--Smith 14.3.6(6) and
the nonsolvable branch of 14.3.15, printed pp.992--994.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section03.EmptyFamilySieve
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Sporadic.Mathieu
variable {G : Type*} [Group G] [Finite G]

private theorem source_normalized_hexad_rank_false
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (K : Subgroup G) (hK : K ∈ MainForward.localComponents T)
    (hn : (T : Subgroup G) ≤ normalizer (K : Set G))
    {B : Type} [Group B] [Finite B]
    (eK : (K ⧸ pCore 2 K) ≃* B)
    (hmodel : ∀ (P : Sylow 2 B) (N : Subgroup B),
      (∀ L : Subgroup B, (P : Subgroup B) ≤ L → (P : Subgroup B).relIndex L = 3 →
        (∀ a : MulAut B, (P : Subgroup B).map a.toMonoidHom = P → L.map a.toMonoidHom = L) → L ≤ N) →
      ∃ D : Subgroup B, D ≤ N ∧ Group.IsPerfect D ∧ 2 ≤ primeRank 3 D) : False := by
  obtain ⟨P,hP⟩ := NormalSylowQuotientAction.intersection_sylow T K hn
  let q := eK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  have hq : Function.Surjective q := eK.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : q.ker = pCore 2 K := by
    ext k
    change eK (QuotientGroup.mk k) = 1 ↔ k ∈ pCore 2 K
    rw [eK.map_eq_one_iff,QuotientGroup.eq_one_iff]
  let Pq := P.mapSurjective hq
  obtain ⟨D,hD,hperf,hr⟩ := hmodel Pq ((M.subgroupOf K).map q) (by
    intro L hPL hi hinv
    exact source_invariant_cubic_le_image hG T hempty hM hu hmany hcard e hnot K hK hn eK P hP L hPL hi hinv)
  let := hperf
  have hb := source_perfect_image_threeRank_le_one hG T hempty hM hu hmany hcard e K q
    (hker.symm ▸ pCore_isPGroup) D hD
  omega

/-- Exclusion of the genuine central-three-cover row for a T-normalized component. -/
theorem source_normalized_triple_m22_false
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (K : Subgroup G) (hK : K ∈ MainForward.localComponents T)
    (hn : (T : Subgroup G) ≤ normalizer (K : Set G))
    (eK : (K ⧸ pCore 2 K) ≃* M22TripleCover) : False := by
  apply source_normalized_hexad_rank_false hG T hempty hM hu hmany hcard e hnot K hK hn eK
  intro P N hN
  exact CubicHexadCover.central_quotient_invariant_cubic_rank M22TripleCover.centralQuotientEquiv
    (by rw [M22TripleCover.center_card]) P N hN

/-- Exclusion of the native M₂₂ row for a T-normalized component. -/
theorem source_normalized_m22_false
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (K : Subgroup G) (hK : K ∈ MainForward.localComponents T)
    (hn : (T : Subgroup G) ≤ normalizer (K : Set G))
    (eK : (K ⧸ pCore 2 K) ≃* M22) : False := by
  apply source_normalized_hexad_rank_false hG T hempty hM hu hmany hcard e hnot K hK hn eK
  intro P N hN
  exact CubicHexadCover.invariant_cubic_rank (MonoidHom.id M22) Function.surjective_id
    (by simp) (by simp) (fun a => ⟨a,fun _ => rfl⟩) P N hN

/-- The central-three-cover row with the actual source conjugate-closure mark. -/
theorem source_orbit_triple_m22_false
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (K : Subgroup G) (hK : K ∈ MainForward.localComponents T)
    (horbit : K = conjugateSpanBy K (T : Subgroup G))
    (eK : (K ⧸ pCore 2 K) ≃* M22TripleCover) : False := by
  have hn : (T : Subgroup G) ≤ normalizer (K : Set G) := by
    have hh := le_normalizer_conjugateSpanBy K (T : Subgroup G)
    rwa [←horbit] at hh
  exact source_normalized_triple_m22_false hG T hempty hM hu hmany hcard e hnot K hK hn eK

/-- The native M₂₂ row with the actual source conjugate-closure mark. -/
theorem source_orbit_m22_false
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (K : Subgroup G) (hK : K ∈ MainForward.localComponents T)
    (horbit : K = conjugateSpanBy K (T : Subgroup G))
    (eK : (K ⧸ pCore 2 K) ≃* M22) : False := by
  have hn : (T : Subgroup G) ≤ normalizer (K : Set G) := by
    have hh := le_normalizer_conjugateSpanBy K (T : Subgroup G)
    rwa [←horbit] at hh
  exact source_normalized_m22_false hG T hempty hM hu hmany hcard e hnot K hK hn eK

end CFSG.Quasithin.Chapter14.Section03.EmptyFamilySieve
