module
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.CompleteSource
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.QuasisimpleWhole
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.PairSourceOrbitSpan
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.FiveSeedObstruction
/-!
# Entire reduced-module generation from a Sylow seed centralizer

Complete E.2.3 classification supplies either a quasisimple source or two
actual factors. In the single case a seed whose centralizer is the chosen
Sylow excludes the five-letter module; the natural section gives generation
by moved and fixed vectors. The pair already has that generation property.
Vanishing residual fixed points therefore makes the entire original reduced
module residual-generated. This includes the single H* component in 10.2.3.
Source: Aschbacher--Smith E.2.3 and 10.2.3(4), pp.216--217 and746--747.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.ThompsonAction
open ChapterB ChapterB.QuasisimpleSource ChapterB.SourceInduction
universe u
variable {G : Type u} [Group G] [Finite G]
set_option backward.isDefEq.respectTransparency false in
theorem source_module_eq_commutator_of_seed_centralizer
    (hG : IsSQTK KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) (hU : IsPReduced 2 U)
    (hns : ¬ Group.IsSolvable G)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (Z : Subgroup G) (hZU : Z ≤ U)
    (hCZ : centralizer (Z : Set G) = (T : Subgroup G))
    (hfixed : U ⊓ centralizer (pResidual 2 G : Set G) = ⊥) :
    U = ⁅U,pResidual 2 G⁆ := by
  let := hU.normal
  let := hU.elementary
  let C := centralizer (U : Set G)
  let q := QuotientGroup.mk' C
  have hq := QuotientGroup.mk'_surjective C
  have hk : q.ker = centralizer (U : Set G) := QuotientGroup.ker_mk' C
  let α := NormalElementaryQuotient.representation U q hq hk
  let Y := offenderSubgroup α
  let := offenderSubgroup_normal α
  have hgen : U ≤ (⁅U,pResidual 2 G⁆ : Subgroup G) ⊔
      (U ⊓ centralizer (pResidual 2 G : Set G)) := by
    rcases source_nonsolvable_natural_factors hG T hP U hU hns hJ with
      ⟨hqs,c,hlinear | hfive⟩ | ⟨d,_,_⟩
    · obtain ⟨F,hF⟩ := hlinear
      have hs := (quasisimple_linear_whole_source T hP U hU hJ q hq hk
        hqs c.sectionData F hF).2.2.1
      rw [NormalElementaryQuotient.commutatorSpace_eq U q hq hk] at hs
      exact NormalElementaryQuotient.le_commutator_sup_fixed_of_generation U q hq hk
        (pResidual 2 G) (pResidual 2 G) U ((pResidual 2 G).map q)
        le_rfl le_rfl hs inf_le_left
    · obtain ⟨a⟩ := hfive
      exfalso
      apply not_five_movedSection_of_seed U Z q hq hk hZU T hCZ Y
        (generalizedFitting Y) c.sectionData
      refine ⟨a.subgroupEquiv,a.action.linearEquiv,?_⟩
      intro g v
      exact (a.action.intertwines ⟨g,a.contained g.property⟩ v).trans
        (congrArg (fun k => BinaryPermutation.naturalRepresentation (Fin 5) k
          (a.action.linearEquiv v)) (a.compatible g))
    · exact paired_module_le_moved_sup_alpha_fixed T hP U hU hJ q hq hk d U inf_le_left
  rw [hfixed,sup_bot_eq] at hgen
  exact le_antisymm hgen (commutator_le_left _ _)
end CFSG.Quasithin.ChapterE.ThompsonAction
