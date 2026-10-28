module

public import CFSG.Quasithin.Chapter3.Section02.QrcInput
public import CFSG.Quasithin.Chapter3.Section01.CenterAlternative
public import CFSG.Quasithin.Chapter3.Section01.OffenderBranch
public import Theory.GroupTheory.CenterFreeOddImageCore

/-!
# The center obstruction for the original Fundamental Setup

The original V_M lies in the supplied Sylow group. A nontrivial
C_{V_M}(L₀) therefore meets its center nontrivially and yields a nontrivial
center of L₀T. Combining this with the proved central branch of 3.1.7
excludes centralization of the Sylow omega-center by every original H*
when this fixed subgroup is nontrivial. The actual FF branch is also
connected to the original module V and its faithful conjugation image.

The remaining Baumann alternative is needed to force J(T) to move V;
the separate commutator conclusion of 3.2.2(6) remains a source obligation.
Source: Aschbacher–Smith, Lemma 3.2.2(6), combined manuscript of
1 March 2004, printed p.579.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter3.Section02.FundamentalSetup
universe u
variable {G : Type u} [Group G] [Finite G] {K : GroupClass.{u}}
  {T : Sylow 2 G} {L : Subgroup G} (D : FundamentalSetup K T L)

theorem fullModule_le_sylow
    (h127 : Chapter1.Section02.NonsolvableUniquenessConclusion T L) :
    D.fullModule ≤ (T : Subgroup G) := by
  have hc : D.fullModule ≤ D.maximalLocal.pCoreIn 2 :=
    (D.fullModule_le_reduced h127).trans (map_mono (reducedPSubgroup_le_pCore 2 _))
  apply hc.trans
  simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le
    (le_normalizer_componentOrbit L T)] using
    pCoreIn_le_sylow D.maximalLocal D.ambientSylow

theorem center_join_ne_bot_of_fullCentralizer_ne_bot
    (h127 : Chapter1.Section02.NonsolvableUniquenessConclusion T L)
    (hc : D.fullCentralizer ≠ ⊥) : center (localJoin T L) ≠ ⊥ := by
  intro hcenter
  let H := localJoin T L
  let X := (localOrbit T L).subgroupOf H
  let Q := D.fullModule.subgroupOf H
  let S : Sylow 2 H := T.subtype le_sup_right
  have hVH : D.fullModule ≤ H := (D.fullModule_le_sylow h127).trans le_sup_right
  have hnX : X.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le (localOrbit T L).le_normalizer (le_normalizer_componentOrbit L T))
  let := hnX
  have hnQ : Q.Normal := normal_subgroupOf_of_le_normalizer
    ((D.lemma_3_2_3_uniqueness h127).2.1.trans D.maximalLocal_normalizes_fullModule)
  let := hnQ
  let := D.fullModule_elementary h127
  have hp : IsPGroup 2 Q := (IsElementaryAbelian.isPGroup 2 D.fullModule).comap_of_injective
    H.subtype H.subtype_injective
  have hgen : X ⊔ (S : Subgroup H) = ⊤ := by
    change (localOrbit T L).subgroupOf H ⊔ (T : Subgroup G).subgroupOf H = ⊤
    rw [← subgroupOf_sup le_sup_left le_sup_right, subgroupOf_self]
  have he : Q ⊓ centralizer (X : Set H) = ⊥ :=
    inf_centralizer_eq_bot_of_centerfree_sylow_supplement S X Q hgen hp hcenter
  apply hc
  apply le_bot_iff.mp
  intro x hx
  let xH : H := ⟨x, hVH x.property⟩
  have hxH : xH ∈ Q ⊓ centralizer (X : Set H) := by
    refine ⟨x.property, ?_⟩
    intro y hy
    exact Subtype.ext (hx y hy)
  have hx1 : xH = 1 := mem_bot.mp (he ▸ hxH)
  exact Subtype.ext (congrArg H.subtype hx1)

/-- The central branch of 3.1.7 cannot occur in the nonzero-fixed-space
case of the original FSU. -/
theorem omega_center_not_le_center_of_fullCentralizer_ne_bot
    (h127 : Chapter1.Section02.NonsolvableUniquenessConclusion T L)
    (hc : D.fullCentralizer ≠ ⊥) {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal) :
    ¬ Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ≤ (center H).map H.subtype := by
  intro hz
  apply D.center_join_ne_bot_of_fullCentralizer_ne_bot h127 hc
  exact (D.qrcHypotheses h127 hH).center_eq_bot_of_omega_center_centralizes
    (D.simpleQTKE.evenCharacteristic T) (D.lemma_3_2_3_uniqueness h127).1
    (D.lemma_3_2_3_uniqueness h127).2.2 hz

/-- The literal faithful action on the original V is an FF-module
whenever the original J(T) moves V, the first branch of 3.1.8(3). -/
theorem module_isFF_of_thompson_not_centralizes
    (hJ : ¬ Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (D.moduleSubgroup : Set G)) :
    letI := D.module_elementary
    Representation.BinaryOffender.IsFFModule
      (ChapterD.UniqueFactor.imageRepresentation (localJoin T L) D.moduleSubgroup
        D.join_normalizes_module) := by
  let := D.module_elementary
  exact Chapter3.internalActionImage_isFFModule_of_thompson_not_le T
    (localJoin T L) D.moduleSubgroup le_sup_right D.module_le_sylow
    D.join_normalizes_module hJ

end CFSG.Quasithin.Chapter3.Section02.FundamentalSetup
