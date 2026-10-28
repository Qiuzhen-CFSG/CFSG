module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitaryProfileCoordinates
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalRecognitionCore

/-!
# Chapter 12 application of the unitary-five profile

The selected Chapter 12 pair inherits its F.1.1 hypothesis from the actual
chosen-module preparation. The U₅ profile theorem then supplies both literal
remainder/core preimages, the original factor’s projective square, and the
root actor square on the same marked quotient. This is a conditional source
consumer; the preceding profile, marked quotient, split data and rotation
order remain genuine inputs and final source assembly retains all other rows.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
open BenderSuzuki.MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.QuadrangleStructure
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.Source ChapterF.Source.FongSeitzBinary
variable {G X E : Type*} [Group G] [Finite G] [Group X]
  [Field E] [Finite E] [CharP E 2]
  {T : Sylow 2 G} {L V H A B R : Subgroup G} {P : Fin 2 → Subgroup X}
  (D : ChosenModule T L V)
include D

/-- The literal Chapter 12 U5 profile selects the special-unitary original
factor and its scalar projective action, with both kernel premises discharged. -/
theorem rankOne_global_unitary_profile_factor
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (d : Global.Preparation T L H A B R) (hTH : (T : Subgroup G) ≤ H)
    (Q : MarkedQuotient P)
    (e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) Q.standardAmalgam)
    (split : SplitData Q.tits) (hm : rotationOrder Q = 4)
    (J : HermitianForm 3 E) {m : ℕ} (hmpos : 0 < m)
    (hE : Nat.card E = (2^m)^2)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (hconj : ∀ x, J.conj x = x^(2^m))
    (hfactor : Nonempty ((R ⧸ pCore 2 R) ≃* J.specialSubgroup) ∨
      Nonempty ((R ⧸ pCore 2 R) ≃* ProjectiveSpecialUnitaryMatrixGroup J))
    (hindexi : (commonBorel ![L,R] (Global.sourceS L H)).relIndex
      (parabolic ![L,R] (Global.sourceS L H) 0) = (2^m)^2 + 1)
    (hindexj : (commonBorel ![L,R] (Global.sourceS L H)).relIndex
      (parabolic ![L,R] (Global.sourceS L H) 1) = (2^m)^3 + 1)
    (hQi : letI := QuadrangleStructure.original_core_normal_in_sylow (L := ![L,R]) (S := Global.sourceS L H) 0
      IsElementaryAbelian 2 ((Global.sourceS L H) ⧸
        ((parabolic ![L,R] (Global.sourceS L H) 0).pCoreIn 2).subgroupOf (Global.sourceS L H)))
    (hQj : Nat.card ((parabolic ![L,R] (Global.sourceS L H) 1).pCoreIn 2) = (2^m)^7)
    (hderived : _root_.commutator ((parabolic ![L,R] (Global.sourceS L H) 1).pCoreIn 2) =
      center ((parabolic ![L,R] (Global.sourceS L H) 1).pCoreIn 2))
    (hfrattini : frattini ((parabolic ![L,R] (Global.sourceS L H) 1).pCoreIn 2) =
      center ((parabolic ![L,R] (Global.sourceS L H) 1).pCoreIn 2)) :
    let hf := d.hypothesisF11 (D.rankOne_generic_input_of_many h hmany hn hpsl) hTH
    (∀ k : Fin 2, simpleRemainder Q split k ≤ localKernel Q k ∧
      (simpleRemainder Q split k).comap (MarkedLocal.endpointMap Q e k) =
        pCore 2 (parabolic ![L,R] (Global.sourceS L H) k)) ∧
    ∃ (ξ : (R ⧸ pCore 2 R) ≃* J.specialSubgroup)
      (ν : localGroup Q split 1 ≃* ProjectiveSpecialUnitaryMatrixGroup J)
      (κ : rankOne Q split 1 ≃* J.specialSubgroup),
      (∀ l, ν (MarkedLocal.factorQuotientLocalMap Q e hf split 1 l) =
        J.specialToProjective (ξ l)) ∧
      (∀ r, ν (RootLocalCover.projection Q split 1 r) = J.specialToProjective (κ r)) ∧
      (RootLocalCover.projection Q split 1).ker = center (rankOne Q split 1) := by
  let hf := d.hypothesisF11 (D.rankOne_generic_input_of_many h hmany hn hpsl) hTH
  obtain ⟨hr,ξ,ν,κ,γ,c,hpanel,hfactorSquare,hker,_,_,_⟩ :=
    UnitaryFiveSource.marked_unitary_profile_coordinates Q split e hf J hmpos hE hJ hconj
      hm 0 1 (by decide) hfactor hindexi hindexj hQi hQj hderived hfrattini
  exact ⟨hr,ξ,ν,κ,hfactorSquare,hpanel,hker⟩
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
