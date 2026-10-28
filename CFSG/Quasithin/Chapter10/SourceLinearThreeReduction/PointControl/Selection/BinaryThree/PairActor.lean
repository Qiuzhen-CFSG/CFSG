module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.BinaryThree.Actor
public import CFSG.Quasithin.ChapterD.Section01.UniqueFactor.PairedSupportBounds
public import Mathlib.GroupTheory.IndexNormal

/-!
# Sharp bounds on the selected full binary-three module

The half-Sylow normalizes both original moved factors and is normalized by
the exchanger. The normalizer bound on the first positive central cover
therefore transports to the second. Since those factors generate the full
module, the spanning-support inequality proves that its actual half-Sylow
action image has no strong offenders, without assuming a trivial intersection.

Source: Aschbacher--Smith, 10.1.1 and the FF step in 10.2.8, pp.741,749.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.PointControl.Selection.BinaryThree
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
local instance : IsElementaryAbelian 2 (⁅D.fullModule,L⁆ : Subgroup G) :=
  source_original_full_moved_elementary D

/-- The half-Sylow faithful action on the full selected module has no strong
offender in the positive-kernel binary-three row. -/
theorem half_sylow_full_not_strong (hmodel : BinaryThreeNatural D)
    (hne : sourceMovedFixed D ≠ ⊥)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G))
    [IsElementaryAbelian 2 D.fullModule] :
    ¬ IsStrongFFModule (ChapterD.UniqueFactor.imageRepresentation
      ((T : Subgroup G) ⊓ normalizer (L : Set G)) D.fullModule
      ((inf_le_left.trans (le_normalizer_componentOrbit L T)).trans
        D.maximalLocal_normalizes_fullModule)) := by
  let S := (T : Subgroup G) ⊓ normalizer (L : Set G)
  let W := ⁅D.fullModule,L⁆
  let f := MulAut.conj t
  let U := W.map f.toMonoidHom
  have hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G) := fun h => htn (h ht)
  have hSM : S ≤ D.maximalLocal := inf_le_left.trans (le_normalizer_componentOrbit L T)
  have hSW : S ≤ normalizer (W : Set G) :=
    (le_inf hSM inf_le_right).trans (source_moved_normalizer_local_containment D)
  have hgen : D.fullModule = W ⊔ U := by
    obtain ⟨s,_,_,_,hV,hpair⟩ := source_nonnormal_fullModule_pair D hn
    have hdiff : U ≠ W := by
      intro he
      have hc : W ≤ centralizer (L : Set G) := he ▸ hcross
      have hz : ⁅W,L⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr hc
      exact source_full_moved_ne_bot D ((source_full_moved_eq_commutator D).symm.trans hz)
    have he := (hpair t (le_normalizer_componentOrbit L T ht)).resolve_left hdiff
    exact hV.trans (congrArg (fun X : Subgroup G => W ⊔ X) he.symm)
  have hindex : (S.subgroupOf (T : Subgroup G)).index = 2 := by
    have he : S.subgroupOf (T : Subgroup G) =
        (normalizer (L : Set G)).subgroupOf (T : Subgroup G) := by
      ext x
      exact ⟨fun h => h.2,fun h => ⟨x.property,h⟩⟩
    rw [he]
    exact source_nonnormal_sylow_stabilizer_index D.simpleQTKE D.maximal.1 hn
  let : (S.subgroupOf (T : Subgroup G)).Normal := normal_of_index_eq_two hindex
  have hTS : (T : Subgroup G) ≤ normalizer (S : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (show S ≤ (T : Subgroup G) from inf_le_left)).mp inferInstance
  have hSf : S.map f.toMonoidHom=S := mem_normalizer_iff_map_conj_eq.mp (hTS ht)
  have hN : S.map f.toMonoidHom ≤ normalizer (U : Set G) :=
    (map_mono hSW).trans (le_normalizer_map f.toMonoidHom)
  have hSU : S ≤ normalizer (U : Set G) := hSf ▸ hN
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.map f.toMonoidHom
  have hW := common_normalizer_not_strong D hmodel hne S inf_le_right hSW
  have hU : ¬ IsStrongFFModule (ChapterD.UniqueFactor.imageRepresentation S U hSU) := by
    have hh := ChapterD.UniqueFactor.conjugate_image_not_strong S W hSW f hN hW
    have aux (K : Subgroup G) (hK : K=S) (hKU : K ≤ normalizer (U : Set G))
        (hnK : ¬ IsStrongFFModule (ChapterD.UniqueFactor.imageRepresentation K U hKU)) :
        ¬ IsStrongFFModule (ChapterD.UniqueFactor.imageRepresentation S U hSU) := by
      cases hK
      exact hnK
    exact aux _ hSf hN hh
  exact ChapterD.UniqueFactor.spanning_pair_image_not_strong S D.fullModule W U
    (hSM.trans D.maximalLocal_normalizes_fullModule) hSW hSU hgen.symm hW hU
end CFSG.Quasithin.Chapter10.PointControl.Selection.BinaryThree
