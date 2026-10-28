module
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.PairSymmetric.Fixer
public import CFSG.Quasithin.ChapterB.Section06To07.RankOneBaumann.PairedLayerSource
public import Theory.Representation.BinaryPermutation.FivePairFaithful

/-!
# The faithful full action from the paired S₅ source quotient

The marked paired quotient has kernel exactly the residual fixed space. Its
normal self-centralizing layer yields a faithful full ambient action by the
standard quotient construction. The factor exchanger and factor-permutation
source prove the original action on that layer, so no ambient equivariance is
added as a premise.

Source: Aschbacher–Smith B.6.10 and E.2.3(3), pp.117 and216–217.
-/

public section
open Subgroup Stellmacher Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
set_option backward.isDefEq.respectTransparency false
namespace CFSG.Quasithin.ChapterB.SourceInduction.SourceTwoFactorCase.MarkedProduct
open BinaryPermutation
variable {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]

theorem source_full_faithful_action
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U] (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set G))
    (d : SourceTwoFactorCase ((NormalElementaryQuotient.representation U q hq hker).comp
      (offenderSubgroup (NormalElementaryQuotient.representation U q hq hker)).subtype))
    (c : d.MarkedProduct (naturalRepresentation (Fin 5))) :
    pCore 2 (offenderSubgroup (NormalElementaryQuotient.representation U q hq hker)) = ⊥ ∧
    ∃ ρ : Representation (ZMod 2) H (FivePair.Core × FivePair.Core),
      Function.Injective ρ ∧
      (∀ g v, c.symmetricCoreMap (NormalElementaryQuotient.representation U q hq hker g v) =
        ρ g (c.symmetricCoreMap v)) ∧
      ∀ (g : offenderSubgroup (NormalElementaryQuotient.representation U q hq hker)) v,
        ρ (g : H) v = FivePair.action (c.action.groupEquiv g) v := by
  let α := NormalElementaryQuotient.representation U q hq hker
  let Y := offenderSubgroup α
  let := offenderSubgroup_normal α
  have hcore : pCore 2 H = ⊥ := by
    let e := (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective q hq)
    rw [←pCore_map_iso 2 e,hU.quotient_pCore_eq_bot,Subgroup.map_bot]
  have hcoreY : pCore 2 Y = ⊥ := by
    have hle : (pCore 2 Y).map Y.subtype ≤ pCore 2 H :=
      le_sSup ⟨inferInstance,pCore_isPGroup.map Y.subtype⟩
    rw [hcore] at hle
    apply (map_eq_bot_iff_of_injective (pCore 2 Y) Y.subtype_injective).mp
    exact le_bot_iff.mp hle
  refine ⟨hcoreY,?_⟩
  have hUT : U ≤ T := hU.le_pCore.trans (pCore_isPGroup.le_sylow_of_normal T)
  have hJL := RankOneBaumann.thompson_image_le_offender_layer T U q hq hker hUT Y le_rfl
  have hres := RankOneBaumann.residual_image_le_normal_thompson_layer T hP U hU hJ q hq hker Y hJL
  have hY : centralizer (Y : Set H) ≤ Y := by
    rw [map_pResidual_of_surjective 2 q hq] at hres
    exact (centralizer_le hres).trans ((centralizer_pResidual_le_of_pCore_eq_bot hcore).trans hres)
  let τ := FivePair.action.comp c.action.groupEquiv.toMonoidHom
  have ht : Function.Injective τ := FivePair.action_injective.comp c.action.groupEquiv.injective
  apply exists_faithful_action_of_normal_layer_quotient α Y hY τ ht
    c.symmetricCoreMap c.symmetricCoreMap_surjective
  · exact c.symmetricCoreMap_ker
  · exact c.symmetricCoreMap_action
end CFSG.Quasithin.ChapterB.SourceInduction.SourceTwoFactorCase.MarkedProduct
