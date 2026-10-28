module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.QuadrangleStructure.UnitaryFactorFrattini
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalRecognitionCore

/-!
# The original Chapter 12 unitary core is special

For the literal pair ![L,R], the original linear factor fixes its panel
parameter. The opposite original SU3-or-PSU3 quotient constructs the full
unitary cover. Its root center and the binary degree bounds force the
actual opposite core to be special, and identify the full SU3 actor and
its irreducible Frattini action, without either specialness equation.

The full proper-K/KnownSimple preparation, both endpoint squares and the
whole Borel remain in the same amalgam marking. Earlier source producers
still supply that marked split quotient, rotation four, the matching
field parameters and the opposite remainder/kernel containment.
This does not prove the U5 mixed coordinate equations or seven-row selection.

Source: AS 12.2.2 and F.1.1--3; DGS (11.8)(a,c,f), pp.175--176;
Fong--Seitz I (4D), (6A)(c), pp.21--23,37--38.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
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

/-- Specialness and the full unitary Frattini actor on the literal Chapter 12
pair, including the opposite nonperfect SU3(2) case and its scalar center. -/
theorem rankOne_unitary_quadrangle_core_special
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (d : Global.Preparation T L H A B R) (hTH : (T : Subgroup G) ≤ H)
    (Q : MarkedQuotient P)
    (mark : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) Q.standardAmalgam)
    (split : SplitData Q.tits) (hm : rotationOrder Q = 4)
    {E : Type*} [Field E] [Finite E] [CharP E 2]
    (J : HermitianForm 3 E) {m : ℕ} (hmpos : 0 < m) (hdegree : n = 2*m)
    (hE : Nat.card E = (2^m)^2) (hconj : ∀ x, J.conj x = x^(2^m))
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (hVj : simpleRemainder Q split 1 ≤ localKernel Q 1)
    (hfactor : Nonempty ((R ⧸ pCore 2 R) ≃* J.specialSubgroup) ∨
      Nonempty ((R ⧸ pCore 2 R) ≃* ProjectiveSpecialUnitaryMatrixGroup J)) :
    _root_.commutator ((parabolic ![L,R] (Global.sourceS L H) 1).pCoreIn 2) =
        center ((parabolic ![L,R] (Global.sourceS L H) 1).pCoreIn 2) ∧
      frattini ((parabolic ![L,R] (Global.sourceS L H) 1).pCoreIn 2) =
        center ((parabolic ![L,R] (Global.sourceS L H) 1).pCoreIn 2) ∧
      ∃ ν : localGroup Q split 1 ≃* ProjectiveSpecialUnitaryMatrixGroup J,
        Nonempty (QuadrangleStructure.UnitaryActorProfile Q split 1 J hVj ν) ∧
        (elementaryRepresentation (p := 2) (remainderFrattiniAction Q split 1 hVj)).IsIrreducible := by
  have hf := d.hypothesisF11 (D.rankOne_generic_input_of_many h hmany hn hpsl) hTH
  obtain ⟨F,hF,hfin,hcard,⟨μ⟩⟩ := hpsl
  let := Fintype.ofFinite F
  let : NeZero n := ⟨by omega⟩
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hcard)
  obtain ⟨T₀,hT₀⟩ := hf.sylow 0
  have hVi := MarkedLocal.linear_remainder_le_kernel Q mark hf split 0 T₀ hT₀ μ
  have hroot := MarkedLocal.simpleRoot_card_linear Q mark hf split 0 T₀ hT₀ μ
  have hindex : (commonBorel ![L,R] (Global.sourceS L H)).relIndex
      (parabolic ![L,R] (Global.sourceS L H) 0) = (2^m)^2 + 1 := by
    have he := QuadrangleStructure.marked_commonBorel_root_index Q mark hf split 0
    rw [hroot,hcard,hdegree,Nat.mul_comm 2 m,pow_mul] at he
    omega
  exact QuadrangleStructure.marked_unitary_core_special_of_factor Q mark hf split J hmpos hE hconj hJ
    hm 0 1 (by decide) hVi hVj hindex hfactor
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
