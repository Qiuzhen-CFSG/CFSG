module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.Classification.Sieve.SourceOrbit
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.Classification.Sieve.BinaryG2
public import CFSG.Quasithin.Chapter14.Section06.SourcePlacedQuadraticActor
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.SourceModels.QuadraticActor

/-!
# The F.9.18 normal-component model clause on the Chapter14 setup

For a relative normal C-component K of H, the actual subgroup KT remains
outside M by SourceOrbit. Restrict K to KT, construct the faithful action
on its literal span quotient, and use the source placed quadratic actor.
Since K is the two-residual of KT, that actor acts faithfully on its
component image. The image is simple and centerless by 14.6.19; the genuine
small-quadratic component theorem then gives the complete F.9.18 model list.
Transport uses the original two-core quotient of K throughout.

The final consumer applies the existing exceptional and binary G₂ sieve,
so the normal branch retains no F.9.18 model callback. The reduction to KT
is used only for group models: it does not identify its module with the
whole Mc-span when Mc has two normal components. That module recognition
and the remaining Lie-model exclusions belong to
qt-e-suitable-component-supports. Original 14.6.18 remains with
qt-e-14625-source.

Source: Aschbacher--Smith F.9.18(4), printed pp.325--326, and 14.6.19--20,
printed p.1037. The reusable model theorem is the completed output of
qt-d-138-f918-models-source.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Classification.Sieve
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open Chapter13.Section08.Components.Models Chapter13.Section08.Components.SourceModels
variable {G : Type*} [Group G] [Finite G]
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (hsolv : ∀ J ∈ Chapter1.HOver G (T : Set G), Group.IsSolvable J → J ≤ M)
include hG hempty hM hunique hmany hcard e hab hsolv

/-- The genuine F.9.18 normal-component model clause on the Chapter14 setup.
The reduction to KT preserves the original component quotient. -/
theorem source_normal_component_f918_models
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hn : (K.subgroupOf H).Normal) : F918Models (K ⧸ pCore 2 K) := by
  let J := K ⊔ (T : Subgroup G)
  have hJH : J ≤ H := sup_le hKH hH.1.2
  have hKJ : K ≤ J := le_sup_left
  have hTJ : (T : Subgroup G) ≤ J := le_sup_right
  have hJ : J ∈ Chapter1.HOutside G (T : Set G) (M : Set G) :=
    ⟨Chapter3.mem_HOver_of_sylow_interval T hTJ hJH hH.1,
      fun hj => source_component_not_le hG T hempty hM hunique hmany hcard e hab hsolv
        H hH K hKH hK (hKJ.trans hj)⟩
  have hc : (K.subgroupOf J).IsCComponent := hK.subgroupOf_of_le hKJ hJH
  have hnc : (K.subgroupOf J).Normal := (normal_subgroupOf_iff_le_normalizer hKJ).mpr
    (hJH.trans ((normal_subgroupOf_iff_le_normalizer hKH).mp hn))
  have hgen : K.subgroupOf J ⊔ (T : Subgroup G).subgroupOf J = ⊤ := by
    rw [←subgroupOf_sup hKJ hTJ]
    change J.subgroupOf J = ⊤
    simp only [subgroupOf_self]
  obtain ⟨hU,a,A,hA,hAE,hAQ,hbound,_,_⟩ :=
    source_rankTwo_bounded_placed_action hG T hempty hM hunique hmany hcard e hab J hJ
  let := hU
  let q := QuotientGroup.mk' (pCore 2 J)
  let : Group.IsNilpotent (pCore 2 J) := pCore_isPGroup.isNilpotent
  let D := (K.subgroupOf J).map q
  let ec := (QuotientGroup.congr _ _ (subgroupOfEquivOfLe hKJ)
    (pCore_map_iso 2 (subgroupOfEquivOfLe hKJ))).symm.trans (cComponentTwoCoreQuotientEquiv hc)
  let : IsSimpleGroup (K ⧸ pCore 2 K) := source_component_quotient_simple
    hG T hempty hM hunique hmany hcard e hab hsolv J hJ K hKJ hc
  let : IsSimpleGroup D := ec.symm.isSimpleGroup
  let : Group.IsPerfect D := (hc.map_quotient (pCore 2 J)).perfect
  have hz : center D = ⊥ := by
    rcases (inferInstance : (center D).Normal).eq_bot_or_eq_top with hz | hz
    · exact hz
    · exact (Group.IsPerfect.not_isMulCommutative D (center_eq_top_iff.mp hz)).elim
  let : IsQuasisimple D := ⟨((QuotientGroup.quotientMulEquivOfEq hz).trans
    QuotientGroup.quotientBot).isSimpleGroup⟩
  let : D.Normal := hnc.map q (QuotientGroup.mk'_surjective _)
  have hs : IsSQTK KnownSimple.IsKnownSimple (J ⧸ pCore 2 J) := by
    have hsJ := Chapter3.sqtk_of_mem_H hG hJ.1.1
    refine ⟨?_,hsJ.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
      (hsJ.stronglyQuasithin p hp ho)
  have hAD : A.map q ⊓ centralizer (D : Set (J ⧸ pCore 2 J)) = ⊥ :=
    source_placed_actor_faithful_on_normal_cComponent T hTJ A hA
      (K.subgroupOf J) hc hnc hgen
  apply f918Models_transport ec
  exact f918Models_of_quadratic_actor a.representation D (A.map q) a.faithful
    (Or.inl (by rw [hz,card_bot])) hs hAE hAQ hbound hAD

/-- On the normal branch, the reduced Lie-model sieve has no F.9.18 callback. -/
theorem source_normal_component_remaining_lie_models
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hn : (K.subgroupOf H).Normal) : RemainingLieQuotientModels (K ⧸ pCore 2 K) :=
  source_component_remaining_lie_models_of_f918 hG T hempty hM hunique hmany hcard e hab hsolv
    H hH K hKH hK
    (source_normal_component_f918_models hG T hempty hM hunique hmany hcard e hab hsolv H hH K hKH hK hn)
end CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Classification.Sieve
