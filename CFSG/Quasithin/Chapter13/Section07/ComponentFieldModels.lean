module
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.SmallMoved.FieldNormalization
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Component.Sections

/-!
# Normalized field models on the actual component section

An action equivalence transports the literal commutator section and its
fixed quotient, retaining the original component quotient map. The rank-one
and degree-one rank-two consumers use the precise natural models required
by the source 13.7.18 case dispatch. Perfectness excludes the solvable SL₂(2)
endpoint; every resulting group marking is displayed as a composition.

Source: Aschbacher–Smith, 13.7.6 and 13.7.18, printed pp.938–940 and 945.
-/

public section
open Subgroup Representation
namespace CFSG.Quasithin.Chapter13.Section08.TransvectionRecognition.Component
open ChapterB.QuasisimpleSource
open scoped IsMulCommutative
variable {G : Type*} [Group G]
  {H V₃ V₁ K : Subgroup G}
  [(V₁.subgroupOf (Source.UH H V₃)).Normal]
  [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]
  {ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁))}
  {hKH : K ≤ H}

/-- An action equivalence changes only the model coordinates and appends
its group marking to the original canonical component quotient map. -/
theorem HasSectionModel.actionEquiv
    {B W C X : Type*} [Group B] [Group C]
    [AddCommGroup W] [Module (ZMod 2) W] [AddCommGroup X] [Module (ZMod 2) X]
    {σ : Representation (ZMod 2) B W} {τ : Representation (ZMod 2) C X}
    {eK : (K ⧸ pCore 2 K) ≃* B}
    (hs : HasSectionModel H V₃ V₁ ρ K hKH σ eK) (e : ActionEquiv σ τ) :
    HasSectionModel H V₃ V₁ ρ K hKH τ (eK.trans e.groupEquiv) := by
  obtain ⟨hst,c,hc⟩ := hs
  refine ⟨hst,c.trans e.linearEquiv,?_⟩
  intro k u
  exact (congrArg e.linearEquiv (hc k u)).trans
    (e.intertwines (eK (QuotientGroup.mk' (pCore 2 K) k)) (c (Submodule.Quotient.mk u)))

/-- The actual rank-one source section has the literal SL₂(4) natural
model once the small-plane degree bound and perfectness are known. -/
theorem HasSectionModel.linearTwoFour
    [Group.IsPerfect (K ⧸ pCore 2 K)] [Nontrivial (K ⧸ pCore 2 K)]
    (F : BinaryField) (hF : F.degree ≤ 2)
    (eK : (K ⧸ pCore 2 K) ≃* Matrix.SpecialLinearGroup (Fin 2) F.Carrier)
    (hs : HasSectionModel H V₃ V₁ ρ K hKH (linearNatural F 2) eK) :
    HasSectionModel H V₃ V₁ ρ K hKH
      (SL2OrthogonalCover.binaryNatural (F := SL2FourNatural.F))
      (eK.trans (SmallMoved.degreeTwoLinearTwoEquiv F
        (SmallMoved.linearTwo_degree_eq_two F hF eK)).groupEquiv) :=
  hs.actionEquiv (SmallMoved.degreeTwoLinearTwoEquiv F
    (SmallMoved.linearTwo_degree_eq_two F hF eK))

/-- Normalize the actual degree-one SL₃ section without changing its
quotient map or its action convention. -/
theorem HasSectionModel.linearThreeTwo
    (F : BinaryField) (hF : F.degree = 1)
    (eK : (K ⧸ pCore 2 K) ≃* Matrix.SpecialLinearGroup (Fin 3) F.Carrier)
    (hs : HasSectionModel H V₃ V₁ ρ K hKH (linearNatural F 3) eK) :
    HasSectionModel H V₃ V₁ ρ K hKH (linearNatural BinaryField.two 3)
      (eK.trans (ExtensionConsequences.degreeOneNaturalEquiv F hF 3).groupEquiv) :=
  hs.actionEquiv (ExtensionConsequences.degreeOneNaturalEquiv F hF 3)

end CFSG.Quasithin.Chapter13.Section08.TransvectionRecognition.Component
