module
public import CFSG.Quasithin.Chapter12.Section02.ModuleClassification.ActorComparison
public import CFSG.Quasithin.Chapter12.Section02.ModuleClassification.OffenderComparison

/-!
# The two literal B.5 source applications

Restrict the original component image to the actual offender subgroup, or
first adjoin the full-normalizer offender. The common comparison retains
the original quotient projection in both constructions.
Source: Aschbacher--Smith B.5.1 and 12.2.2, pp.99--103,795.
-/
public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.BinaryOffender.QuasisimpleNormalizer
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V)

def seedOffenderComparison
    (hK : D.componentImage ≤ offenderSubgroup D.seedRepresentation) :
    D.LiteralComparison
      (D.seedRepresentation.comp (offenderSubgroup D.seedRepresentation).subtype)
      (D.componentImage.subgroupOf (offenderSubgroup D.seedRepresentation)) :=
  D.seedComparison.restrict _ hK

def normalizerOffenderComparison
    (A : Subgroup (linearNormalizer (D.seedRepresentation.comp D.componentImage.subtype)))
    (hK : component (D.seedRepresentation.comp D.componentImage.subtype) A ≤
      offenderSubgroup (linearAction (supplement (D.seedRepresentation.comp D.componentImage.subtype) A))) :
    D.LiteralComparison
      ((linearAction (supplement (D.seedRepresentation.comp D.componentImage.subtype) A)).comp
        (offenderSubgroup (linearAction (supplement (D.seedRepresentation.comp D.componentImage.subtype) A))).subtype)
      ((component (D.seedRepresentation.comp D.componentImage.subtype) A).subgroupOf
        (offenderSubgroup (linearAction (supplement (D.seedRepresentation.comp D.componentImage.subtype) A)))) :=
  (D.seedComparison.onSupplement A).restrict _ hK

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
