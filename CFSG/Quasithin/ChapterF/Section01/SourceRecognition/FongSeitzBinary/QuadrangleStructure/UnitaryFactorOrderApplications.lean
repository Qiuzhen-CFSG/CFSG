module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.QuadrangleStructure.UnitaryFactorOrders
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalRecognitionCore

/-!
# The original Chapter 12 mixed unitary profile without extra size premises

Apply the two Frattini bounds to the literal ![L,R] pair. The original
linear degree equals twice the unitary degree. The same factor markings
construct the full FiveProfile without a field-ratio hypothesis, an
original-core order, or either specialness equation. For the actual
selected perfect residual R, its unitary quotient also gives regularity;
that application has no extra kernel-containment premise.

The original proper-K and full KnownSimple preparation, whole Borel and
both endpoint squares are unchanged. The source quotient, split datum,
rotation four and actual mixed factor marks remain the earlier producers'
inputs. The unitary-five owner still supplies the remaining source
Cartan/Weyl equations and final marked comparison.
Source: AS 12.2.2, F.1.1--3; DGS (11.8); Fong--Seitz I (6A)(c).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped MatrixGroups IsMulCommutative
open BenderSuzuki.MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.Source ChapterF.Source.FongSeitzBinary
variable {G X : Type*} [Group G] [Finite G] [Group X]
  {T : Sylow 2 G} {L V H A B R : Subgroup G} {P : Fin 2 → Subgroup X}
  (D : ChosenModule T L V)
include D

/-- The original Chapter 12 linear and unitary degrees are forced to match;
there is no independent common-field or core-order assumption. -/
theorem rankOne_global_unitary_quadrangle_degree
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
    (J : HermitianForm 3 E) {m : ℕ} (hmpos : 0 < m)
    (hE : Nat.card E = (2^m)^2) (hconj : ∀ x, J.conj x = x^(2^m))
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (hVj : simpleRemainder Q split 1 ≤ localKernel Q 1)
    (hfactor : Nonempty ((R ⧸ pCore 2 R) ≃* J.specialSubgroup) ∨
      Nonempty ((R ⧸ pCore 2 R) ≃* ProjectiveSpecialUnitaryMatrixGroup J)) :
    n = 2*m := by
  have hf := d.hypothesisF11 (D.rankOne_generic_input_of_many h hmany hn hpsl) hTH
  obtain ⟨F,hF,hfin,hcard,⟨μ⟩⟩ := hpsl
  let := Fintype.ofFinite F
  let : NeZero n := ⟨by omega⟩
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hcard)
  have he := QuadrangleStructure.marked_unitary_factor_orders Q mark hf split J hmpos hE hconj hJ
    hm 0 1 (by decide) μ hfactor hVj
  rw [hcard,←pow_mul] at he
  have hh := Nat.pow_right_injective (by decide : 1 < (2 : ℕ)) he
  omega

/-- The full literal U5 source profile, with all field and core-size premises
discharged, including the regular nonperfect binary unitary case. -/
theorem rankOne_global_unitary_factor_profile_of_regular
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
    (hVj : simpleRemainder Q split 1 ≤ localKernel Q 1)
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
  exact ⟨D.rankOne_global_unitary_quadrangle_degree h hmany hn hpsl d hTH Q mark split hm
      J hmpos hE hconj hJ hVj hfactor,
    QuadrangleStructure.marked_unitary_factor_profile_of_regular Q mark hf split J hmpos hE hconj hJ
      hm 0 1 (by decide) μ hfactor hVj⟩

/-- The actual perfect selected residual discharges the last regularity
premise of the mixed-unitary profile and forces the source degree relation. -/
theorem rankOne_global_unitary_factor_profile_of_perfect
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (d : Global.Preparation T L H A B R) (hTH : (T : Subgroup G) ≤ H)
    (hp : Group.IsPerfect R)
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
  obtain ⟨T₁,hT₁⟩ := hf.sylow 1
  have hVj : simpleRemainder Q split 1 ≤ localKernel Q 1 := by
    rcases hfactor with hs | hp'
    · exact MarkedLocal.specialUnitary_remainder_le_kernel_of_perfect
        Q mark hf split 1 T₁ hT₁ J hp hmpos hE hconj hs.some
    · exact MarkedLocal.projectiveUnitary_remainder_le_kernel_of_perfect
        Q mark hf split 1 T₁ hT₁ J hp hmpos hE hconj hp'.some
  exact D.rankOne_global_unitary_factor_profile_of_regular h hmany hn hpsl d hTH Q mark split hm
    J hmpos hE hconj hJ μ hVj hfactor
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
