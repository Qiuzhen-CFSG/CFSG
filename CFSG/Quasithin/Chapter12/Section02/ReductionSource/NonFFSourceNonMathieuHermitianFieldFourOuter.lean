module
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourOuter
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianFieldFourPushingUp
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceRankOneOddControl

/-!
# Inner placement for the original field-four Hermitian odd normalizer

The actual PSL₃(4) central quotient excludes all component outer sections,
including the PSU₅(4) Sylow-flag case. In the uniqueness branch this puts
the original perfect fixed residual and the entire chosen module in a
normal component of the original odd normalizer; its centralizer is the
full odd core. No SQTK assumption on that odd normalizer is introduced.

The coordinate consumer discharges the cardinal bound on the original
Hermitian action. The existing FieldFourPushingUp tensor endpoint supplies
placed extraspecial centers on both weak-closure branches; this interface
applies to each residual-uniqueness case. The remaining normal-component
and ordinary pushing-up exclusions still belong to the source assembly.
The proof-only import reuses the internal chosen-module quotient transport.
Source: Aschbacher--Smith 4.4.10--11 and Remark 4.4.2, printed pp.619,621,
as applied in 8.2.7, printed p.718, refs/quasithin.pdf.
-/
public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE ChapterB.QuasisimpleSource ChapterK.Linear.Recognition
open ChapterK.Linear.Recognition.ThreeCubicSieve
open ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition
open Chapter4 Chapter4.Section04 Chapter4.Section04.NormalizedRankOneOddControl
open Chapter8.Section02.HermitianSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

omit [Finite G] in
/-- The original orbit central quotient is not a section of any component outer group. -/
theorem sourceOrbit_hermitian_field_four_no_outer_section
    (B : BinaryField) (eQ : (D.orbitComponent ⧸ center D.orbitComponent) ≃* PSL(3,B.Carrier))
    (hfield : B.degree = 2)
    {K : Type*} [Group K] [Finite K] [IsQuasisimple K]
    (hm : ChapterA.Section02.IsTheoremBModel (K ⧸ center K))
    (U : Subgroup (MulAut.Outer K))
    (f : U →* (D.orbitComponent ⧸ center D.orbitComponent)) : ¬ Function.Surjective f := by
  intro hf
  exact field_four_no_outer_section hm (by rw [B.card_eq,hfield]; decide)
    U (eQ.toMonoidHom.comp f) (eQ.surjective.comp hf)

/-- Use the action-free cardinal bound at the component-placement boundary. -/
theorem sourceOrbit_hermitian_field_four_normal_component_of_card
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L) (hV : V = D.sourceOrbit)
    (hcard : 8 < Nat.card D.sourceOrbit)
    (B : BinaryField) (eQ : (D.orbitComponent ⧸ center D.orbitComponent) ≃* PSL(3,B.Carrier))
    (hfield : B.degree = 2)
    (A : Subgroup G) [IsMulCommutative A] (hne : A ≠ ⊥)
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (D.sourceOrbit : Set G))
    (ho : Odd (Nat.card A))
    (hu : UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)))
    (hout : ¬ normalizer (A : Set G) ≤ normalizer (L : Set G)) :
    NormalComponentCase L D.sourceOrbit A (D.orbitComponent ⧸ center D.orbitComponent) := by
  have hh : NormalComponentCase L V A (D.orbitComponent ⧸ center D.orbitComponent) := by
    apply D.sourceOrbit_normal_component_of_unique_and_no_outer_sections h hV
      hcard A hne hA ho hu hout
    intro K hK hm U f
    let : IsQuasisimple K := hK.2
    exact D.sourceOrbit_hermitian_field_four_no_outer_section B eQ hfield hm U f
  exact (congrArg (fun W => NormalComponentCase L W A
    (D.orbitComponent ⧸ center D.orbitComponent)) hV).mp hh

/-- Residual uniqueness now places the original residual and nine-space inside
an actual normal component; the full centralizer is the odd core. -/
theorem sourceOrbit_hermitian_field_four_normal_component
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L) (hV : V = D.sourceOrbit)
    (d : ActionEquiv (D.orbitRepresentation.comp D.orbitComponent.subtype)
      (overgroupAction 1 (binaryImage 1)))
    (B : BinaryField) (eQ : (D.orbitComponent ⧸ center D.orbitComponent) ≃* PSL(3,B.Carrier))
    (hfield : B.degree = 2)
    (A : Subgroup G) [IsMulCommutative A] (hne : A ≠ ⊥)
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (D.sourceOrbit : Set G))
    (ho : Odd (Nat.card A))
    (hu : UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)))
    (hout : ¬ normalizer (A : Set G) ≤ normalizer (L : Set G)) :
    NormalComponentCase L D.sourceOrbit A (D.orbitComponent ⧸ center D.orbitComponent) := by
  exact D.sourceOrbit_hermitian_field_four_normal_component_of_card h hV
    (D.sourceOrbit_hermitian_card_gt_eight 1 d) B eQ hfield A hne hA ho hu hout

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
