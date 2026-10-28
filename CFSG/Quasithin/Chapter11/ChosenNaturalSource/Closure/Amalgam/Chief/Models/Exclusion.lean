module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.Chief.Models.SmallComponents
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.Chief.Models.OddKernel
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.Chief.Models.Reduction

/-!
# Excluding all transvection models for a surviving exceptional component

The literal action of the conjugated K descends through K/O₂(K). On an
irreducible binary section its nontrivial image is a C-component. Every
C-component in a G.6.4 model is simple and has one of the small model orders.
The surviving PSL₂(p) branch has a different order; in the odd-by-SL₂(p)
branch no simple image detects F*(K/O₂(K)). Thus none of the models can occur.

The relative-component premise belongs to
`qt-d-1222-natural-relative-components`; the surviving alternatives, including
triangle elimination, belong to `qt-d-1222-shadow-component-triangle`.
The construction of a chief section detecting the marked lift remains with
`qt-d-1222-amalgam-chief-section`. No such section is assumed to exist here.
Source: Aschbacher--Smith, 11.1.2(1--2), 11.4.1(2), and 11.5.8, p.784.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.Chief.Models
open Chapter12.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V} (E : Closure.Geometry D) (g : G)

/-- The full model comparison on the actual conjugated K action. -/
theorem irreducible_model_exclusion
    (h : LocalInputs E) (hK : Source.NormalComponentIn E.G₁ E.K)
    (hlt : E.L₁ < E.K)
    (hcase : Source.ClassicalRefinementCase L E.L₁ E.K 1 E.input.field.degree)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (σ : Representation (ZMod 2) (actor E g) W) (hi : σ.IsIrreducible)
    (hF : ¬ markedFitting E g ≤ σ.ker) (a : actionImage σ) :
    ¬ ChapterG.Section06.Conclusion (imageRepresentation σ) a := by
  intro hclass
  let := imageRepresentation_irreducible σ hi
  have hcore := QuadraticFourGroup.twoCore_eq_bot_of_faithful_irreducible
    (imageRepresentation σ) (imageRepresentation_injective σ)
  have hk := componentAction_kills_twoCore E g σ h hcore
  let f := quotientAction E g σ hk
  have hc := quotientAction_component E g σ h hK hk hF
  obtain ⟨hsimple, hsmall⟩ := classified_component_small (imageRepresentation σ) a hclass f.range hc
  obtain ⟨_, hodd | hlarge⟩ := source_quotient_comparison E hlt hcase f hc.ne_bot
  · obtain ⟨p, hp, hSL⟩ := hodd
    exact quotientAction_oddSL2_not_simple E g hK hp hSL σ hk hF hsimple
  · exact hlarge hsmall

/-- The source model exclusion for an arbitrary literal chief section on
which the conjugated generalized-Fitting lift survives. -/
theorem chief_model_exclusion [IsElementaryAbelian 2 (localClosure E)]
    (h : LocalInputs E) (hK : Source.NormalComponentIn E.G₁ E.K)
    (hlt : E.L₁ < E.K)
    (hcase : Source.ClassicalRefinementCase L E.L₁ E.K 1 E.input.field.degree)
    (A B : Subrepresentation (action E g)) (hAB : A ⋖ B)
    (hF : ¬ markedFitting E g ≤ (sectionRepresentation (action E g) A B).ker)
    (a : actionImage (sectionRepresentation (action E g) A B)) :
    ¬ ChapterG.Section06.Conclusion
      (imageRepresentation (sectionRepresentation (action E g) A B)) a := by
  let : Finite (B.toSubmodule ⧸ (sectionLower (action E g) A B).toSubmodule) :=
    Finite.of_surjective _ (Submodule.mkQ_surjective _)
  exact irreducible_model_exclusion E g h hK hlt hcase
    (sectionRepresentation (action E g) A B)
    (MathieuCode.Hexad.ChiefFlag.Actions.irreducible_section_of_covBy hAB) hF a

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.Chief.Models
