module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.SeedAlternativesMovedSylowTwoTypes
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedSylowSieveLinearThree

/-!
# The complete constituent type bound for the original chosen seed

The scalar-cover comparison proves characteristicity of the actual component
action kernel in the remaining SL₃ case. The original and graph-twisted
natural actions then give the two literal homogeneous conjugates. Combining
this with the other marked rows completes the type bound used by D.3.5(4).

This proves the type bound conditional on the constituent model. Excluding
the two exceptional B.4.2 rows and exhausting the full normalizer orbit remain
with qt-baumann-fsu; the conditional assembly is in the companion module.
Source: Aschbacher--Smith D.3.5(4), printed pp.195--196, and 3.2.5, p.580.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter3.Section02.ChosenSource325 ChapterB.QuasisimpleSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The literal SL₃ component image has characteristic action kernel, including
its nontrivial scalar-centre cases. -/
theorem componentHom_kernel_characteristic_of_linearThree
    (D : ChosenModule T L V) (hq : IsQuasisimple (L ⧸ pCore 2 L))
    (F : BinaryField) (e : D.componentImage ≃* Matrix.SpecialLinearGroup (Fin 3) F.Carrier) :
    D.componentHom.ker.Characteristic := by
  let := hq
  exact kernel_characteristic_of_linearThree_equiv F D.componentHom
    D.componentQuotientHom D.componentQuotientHom_surjective D.componentQuotientHom_mk e

/-- The SL₃ row supplies the two unchanged-L types without an extra type premise. -/
theorem sylowTwoModuleTypes_of_linearThree (D : ChosenModule T L V)
    (hq : IsQuasisimple (L ⧸ pCore 2 L))
    (hc : V ⊓ centralizer (L : Set G) = ⊥)
    (hm : V < componentOrbit V (T : Subgroup G)) (F : BinaryField)
    (e : ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype) (linearNatural F 3)) :
    D.SylowTwoModuleTypes := by
  obtain ⟨τ₁,htypes⟩ := linearThree_two_twists F
  exact D.sylowTwoModuleTypes_of_characteristic_model_twists
    (D.componentHom_kernel_characteristic_of_linearThree hq F e.groupEquiv)
    hc hm _ τ₁ e htypes

/-- Every marked constituent model has at most two literal Sylow conjugates. -/
theorem sylowTwoModuleTypes_of_constituentModel
    (D : ChosenModule T L V) (hq : IsQuasisimple (L ⧸ pCore 2 L))
    (hc : V ⊓ centralizer (L : Set G) = ⊥)
    (hm : V < componentOrbit V (T : Subgroup G))
    (hmodel : ConstituentModel (D.seedRepresentation.comp D.componentImage.subtype)) :
    D.SylowTwoModuleTypes :=
  D.sylowTwoModuleTypes_of_constituentModel_of_linearThree hq hc hm hmodel
    (D.sylowTwoModuleTypes_of_linearThree hq hc hm)

/-- The complete type bound supplies the literal moved-Sylow model used in D.3.10. -/
theorem sylowMovedModel_of_constituentModel
    (D : ChosenModule T L V) (hq : IsQuasisimple (L ⧸ pCore 2 L))
    (hc : V ⊓ centralizer (L : Set G) = ⊥)
    (hm : V < componentOrbit V (T : Subgroup G))
    (hmodel : ConstituentModel (D.seedRepresentation.comp D.componentImage.subtype)) :
    D.SylowMovedModel :=
  D.sylowMovedModel_of_model_of_two_module_types hmodel
    (D.sylowTwoModuleTypes_of_constituentModel hq hc hm hmodel)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
