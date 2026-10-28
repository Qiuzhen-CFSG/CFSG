module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.QuadrangleStructure.UnitaryFactorRegularity
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.QuadrangleStructure.UnitaryFactorOrderApplications

/-!
# The all-fields original unitary profile in Chapter 12

The actual Chapter 12 proper-K/full KnownSimple preparation supplies
F.1.1. On its marked split quadrangle, the complete local-catalogue
exclusion discharges the unitary remainder/kernel containment, including
parameter two. The mixed-factor theorem then supplies the field relation
n = 2*m and full FiveProfile, with the prescribed original linear map and
both original two-core preimages. Earlier quotient/profile construction
and the independent U5 source equations remain with their source owners.

Source: AS 12.2.2 and F.1.1--3; DGS (11.8), pp.175--176 and Theorem D,
p.224; Fong--Seitz I (5I),(6A)(c), II (8C).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped MatrixGroups IsMulCommutative
open BenderSuzuki.MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.QuadrangleStructure
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.Source ChapterF.Source.FongSeitzBinary
variable {G X : Type*} [Group G] [Finite G] [Group X]
  {T : Sylow 2 G} {L V H A B R : Subgroup G} {P : Fin 2 → Subgroup X}
  (D : ChosenModule T L V)
include D

/-- The full literal U5 source profile, with all field and core-size premises
discharged, including the regular nonperfect binary unitary case. -/
theorem rankOne_global_unitary_factor_profile_all_fields
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (d : Global.Preparation T L H A B R) (hTH : (T : Subgroup G) ≤ H)
    (Q : MarkedQuotient P)
    (mark : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) Q.standardAmalgam)
    (split : SplitData Q.tits) (hm : rotationOrder Q = 4)
    {K E : Type*} [Field K] [Finite K] [CharP K 2]
    [Field E] [Finite E] [CharP E 2]
    (J : HermitianForm 3 E) {m : ℕ} (hmpos : 0 < m)
    (hE : Nat.card E = (2^m)^2) (hconj : ∀ x, J.conj x = x^(2^m))
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (μ : (L ⧸ pCore 2 L) ≃* PSL(2,K))
    (hfactor : Nonempty ((R ⧸ pCore 2 R) ≃* J.specialSubgroup) ∨
      Nonempty ((R ⧸ pCore 2 R) ≃* ProjectiveSpecialUnitaryMatrixGroup J)) :
    n = 2*m ∧
    ∃ profile : UnitarySource.Combined.FiveProfile ![L,R] (Global.sourceS L H)
      Q split K E m 0 1,
      profile.form = J ∧
      (∀ a : L, profile.linear_actor (MarkedLocal.originalFactorIntoActor 0 a) =
        Atlas.RankOneFieldAutomorphisms.slEquivPSL.symm (μ (QuotientGroup.mk' _ a))) ∧
      ∀ k : Fin 2, simpleRemainder Q split k ≤ localKernel Q k ∧
        (simpleRemainder Q split k).comap (MarkedLocal.endpointMap Q mark k) =
          pCore 2 (parabolic ![L,R] (Global.sourceS L H) k) := by
  have hf := d.hypothesisF11 (D.rankOne_generic_input_of_many h hmany hn hpsl) hTH
  exact D.rankOne_global_unitary_factor_profile_of_regular h hmany hn hpsl d hTH Q mark split hm
    J hmpos hE hconj hJ μ (MarkedLocal.marked_quadrangle_regularity Q mark hf split hm 1).1 hfactor
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
