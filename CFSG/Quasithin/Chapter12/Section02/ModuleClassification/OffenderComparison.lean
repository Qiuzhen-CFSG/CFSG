module
public import CFSG.Quasithin.Chapter12.Section02.ModuleClassification.Comparison
public import Theory.Representation.BinaryOffender.QuasisimpleNormalizer

/-!
# Restriction and offender-supplement comparisons

Restriction to the actual offender subgroup and adjoining a full-normalizer
offender preserve the original component quotient projection and every
operator on the chosen space. These comparisons feed the two B.5 source
applications without changing the module or its action.
Source: Aschbacher--Smith B.5.1 and 12.2.2, pp.99--103,795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.BinaryOffender.QuasisimpleNormalizer
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule.LiteralComparison
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} {H : Type*} [Group H]
    {ρ : Representation (ZMod 2) H D.space} {K : Subgroup H}
    (c : D.LiteralComparison ρ K)

/-- Restriction retains the original quotient projection and every operator. -/
def restrict (J : Subgroup H) (hK : K ≤ J) :
    D.LiteralComparison (ρ.comp J.subtype) (K.subgroupOf J) where
  projection := (subgroupOfEquivOfLe hK).symm.toMonoidHom.comp c.projection
  surjective := (subgroupOfEquivOfLe hK).symm.surjective.comp c.surjective
  faithful := by
    intro x y he
    apply (subgroupOfEquivOfLe hK).injective
    exact c.faithful he
  action := c.action

/-- Adjoining the normalizer offender leaves the component operators unchanged. -/
def onSupplement (A : Subgroup (linearNormalizer (ρ.comp K.subtype))) :
    D.LiteralComparison (linearAction (supplement (ρ.comp K.subtype) A))
      (component (ρ.comp K.subtype) A) where
  projection := (QuasisimpleNormalizer.projection (ρ.comp K.subtype) A).comp c.projection
  surjective := (projection_surjective (ρ.comp K.subtype) A).comp c.surjective
  faithful := (linearAction_injective _).comp (component (ρ.comp K.subtype) A).subtype_injective
  action q := (projection_action (ρ.comp K.subtype) A (c.projection q)).trans (c.action q)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule.LiteralComparison
