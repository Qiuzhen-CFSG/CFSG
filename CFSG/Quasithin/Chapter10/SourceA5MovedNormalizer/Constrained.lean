module
public import CFSG.Quasithin.Chapter10.SourceA5ComponentNormalizer.QuotientStructure
public import CFSG.Quasithin.Chapter10.SourceA5ComponentNormalizer.StarRankReduction
public import CFSG.Quasithin.Chapter10.SourceA5ComponentNormalizer.RankOneExclusion

/-!
# The constrained branch for the original moved-factor normalizer

Let H contain the original component orbit and R = O₂(L₀T), with the
original half-Sylow T ∩ N_G(L) Sylow in H. If H ∩ M normalizes L, C.2.6
forces the quotient of a normal constrained C-component containing L to be
quasisimple: otherwise its Fitting preimage normalizes L, which contradicts
the Fitting-normalizer quotient criterion.

The literal source pushing setup then supplies all of C.2.7. Its full star
catalogue, three-rank at most one and the surviving factor five force a
binary SL₂ quotient. The original local-component condition for the full
Sylow excludes a strict enlargement of L in that rank-one cover.

This is the constrained branch of the direct H = N_G([V,L]) argument in
Aschbacher–Smith, Lemma 10.2.6, printed pp.748–749. The source assembly owns
the explicit orbit, radical, Sylow, intersection and component hypotheses.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter1 ChapterA.Section03
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
include D

/-- C.2.6 and the actual intersection control force the literal two-core quotient. -/
theorem source_moved_normalizer_component_quotient_quasisimple
    {H K : Subgroup G}
    (hH : IsSQTK KnownSimple.IsKnownSimple H)
    (hXH : localOrbit T L ≤ H) (hRH : (localJoin T L).pCoreIn 2 ≤ H)
    (hHM : H ⊓ D.maximalLocal ≤ normalizer (L : Set G))
    (hK : K ∈ cComponentsIn H) (hKN : (K.subgroupOf H).Normal)
    (hLK : L ≤ K) (hF : generalizedFitting K = pCore 2 K) :
    IsQuasisimple (K ⧸ pCore 2 K) := by
  classical
  by_contra hnq
  have hfit := ChapterC.Section02Source.fittingCore_le_of_nonquasisimple_component_setup
    (source_join_core_pushing_setup D hH hXH hRH) hK hF
    ((normal_subgroupOf_iff_le_normalizer hK.1).mp hKN) hnq
  let B := L.subgroupOf K
  have htop : (⊤ : Subgroup K).IsCComponent := by
    simpa only [subgroupOf_self] using hK.2.subgroupOf_of_le le_rfl hK.1
  have hB : IsQuasisimple (B ⧸ pCore 2 B) := by
    let := D.quasisimple
    let e : L ≃* B := (subgroupOfEquivOfLe hLK).symm
    exact IsQuasisimple.of_mulEquiv
      (QuotientGroup.congr (pCore 2 L) (pCore 2 B) e (pCore_map_iso 2 e))
  have hFn : twoFittingCore K ≤ normalizer (B : Set K) := by
    rw [← subgroupOf_normalizer_eq hLK]
    intro x hx
    exact hHM (hfit (mem_map_of_mem K.subtype hx))
  exact hnq (quasisimple_quotient_of_fitting_normalizes htop B hB hFn)

private theorem strict_component_outside
    {H K : Subgroup G} (hK : K ∈ cComponentsIn H) (hLK : L < K) :
    ¬ K ≤ D.maximalLocal := by
  intro hKM
  have hLc := D.component_in_maximalLocal.subgroupOf_of_le hLK.le hKM
  have htop : (⊤ : Subgroup K).IsCComponent := by
    simpa only [subgroupOf_self] using hK.2.subgroupOf_of_le le_rfl hK.1
  have he := congrArg (map K.subtype) (hLc.eq_of_le htop le_top)
  rw [map_subgroupOf_eq_of_le hLK.le, ← MonoidHom.range_eq_map, range_subtype] at he
  exact hLK.ne he

private theorem component_c27_input
    {H K : Subgroup G}
    (hH : IsSQTK KnownSimple.IsKnownSimple H)
    (hXH : localOrbit T L ≤ H) (hRH : (localJoin T L).pCoreIn 2 ≤ H)
    (hHM : H ⊓ D.maximalLocal ≤ normalizer (L : Set G))
    (hK : K ∈ cComponentsIn H) (hKN : (K.subgroupOf H).Normal)
    (hLK : L < K) (hF : generalizedFitting K = pCore 2 K) :
    Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.Input
      KnownSimple.IsKnownSimple H ((localJoin T L).pCoreIn 2)
      (H ⊓ D.maximalLocal) K := by
  refine ⟨source_join_core_pushing_setup D hH hXH hRH, hK,
    source_moved_normalizer_component_quotient_quasisimple D hH hXH hRH hHM
      hK hKN hLK.le hF, hF, ?_, ?_⟩
  · exact fun h => strict_component_outside D hK hLK (h.trans inf_le_right)
  · exact hRH.trans ((normal_subgroupOf_iff_le_normalizer hK.1).mp hKN)

private theorem strict_component_not_binary_rank_one
    {H K : Subgroup G}
    (hSyl : IsSylowIn 2 ((T : Subgroup G) ⊓ normalizer (L : Set G)) H)
    (hK : K ∈ cComponentsIn H) (hLK : L < K)
    (hQ : IsQuasisimple (K ⧸ pCore 2 K))
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (d : (K ⧸ pCore 2 K) ≃* SL(2,F)) : False := by
  let R := (T : Subgroup G) ⊓ normalizer (L : Set G)
  obtain ⟨S,hS⟩ := Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal
    hSyl hK.1 hK.2.subnormal
  have hSe : (S : Subgroup K) = R.subgroupOf K := by
    apply map_injective K.subtype_injective
    rw [hS,subgroupOf_map_subtype]
  have hlocal : L.subgroupOf K ∈ localCComponents S := by
    rw [hSe]
    apply ChapterA.Section03.SourceEmbeddings.local_restrict
      (localCComponents_antitone inf_le_left D.maximal.1.1) hLK.le
  have htop : (⊤ : Subgroup K).IsCComponent := by
    simpa only [subgroupOf_self] using hK.2.subgroupOf_of_le le_rfl hK.1
  let : IsQuasisimple (K ⧸ pCore 2 K) := hQ
  let : Group.IsPerfect K := Group.IsPerfect.top_iff.mp htop.perfect
  let f : K →* SL(2,F) := d.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  have hf : Function.Surjective f := d.surjective.comp (QuotientGroup.mk'_surjective _)
  let P := L.subgroupOf K ⊔ (S : Subgroup K)
  have hp : ¬ Group.IsSolvable P := by
    intro hs
    let := hs
    exact hlocal.not_isSolvable inferInstance
  have heP : P = ⊤ := Matrix.SpecialLinearGroup.sylow_overgroup_eq_top_of_component_cover
    htop f hf S P le_sup_right hp
  have hLc : (L.subgroupOf K).IsCComponent := by
    change ((L.subgroupOf K).subgroupOf P).IsCComponent at hlocal
    rw [heP] at hlocal
    simpa only [map_subgroupOf_eq_of_le le_top] using
      hlocal.map_subtype (show (⊤ : Subgroup K).IsSubnormal from .top)
  have heL := hLc.eq_of_le htop le_top
  exact hLK.ne (le_antisymm hLK.le (subgroupOf_eq_top.mp heL))

/-- The original A₅ factor has no strict constrained normal-component enlargement
in an overgroup with the original pushing and full-Sylow data. -/
theorem source_a5_moved_normalizer_strict_component_not_constrained
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    {H K : Subgroup G}
    (hH : IsSQTK KnownSimple.IsKnownSimple H)
    (hXH : localOrbit T L ≤ H) (hRH : (localJoin T L).pCoreIn 2 ≤ H)
    (hSyl : IsSylowIn 2 ((T : Subgroup G) ⊓ normalizer (L : Set G)) H)
    (hHM : H ⊓ D.maximalLocal ≤ normalizer (L : Set G))
    (hK : K ∈ cComponentsIn H) (hKN : (K.subgroupOf H).Normal)
    (hLK : L < K) (h3 : primeRank 3 K ≤ 1) :
    generalizedFitting K ≠ pCore 2 K := by
  intro hF
  have hinput := component_c27_input D hH hXH hRH hHM hK hKN hLK hF
  have hfive : 5 ∣ Nat.card (K ⧸ pCore 2 K) := by
    apply source_a5_conjugate_overgroup_five e (t := 1)
    have hf : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by
      ext x
      change 1 * x * (1 : G)⁻¹ = x
      simp
    simpa only [hf, map_id] using hLK.le
  obtain ⟨F,⟨d⟩⟩ := source_rank_one_coreQuotient_linearTwo hinput h3 hfive
  exact strict_component_not_binary_rank_one D hSyl hK hLK hinput.quasisimple d

end CFSG.Quasithin.Chapter10
