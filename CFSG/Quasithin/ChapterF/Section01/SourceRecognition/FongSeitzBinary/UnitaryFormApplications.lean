module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitaryFormProfile
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalRecognitionCore

/-!
# Chapter 12 unitary profiles without a Gram-matrix premise

The original proper-K/full KnownSimple preparation supplies F.1.1 and the
actual first PSL₂ quotient. Its source field degree supplies the quadratic
linear field used in the U₅ profile. The form-transport theorem applies to
the given arbitrary Hermitian form, preserving both original endpoint core
preimages, the whole local cover, scalar projection and natural Frattini
coordinates. Binary unitary degree is included.

The marked split quadrangle, source field-degree relation and special-core
profile remain with the earlier quotient and commuting-one-profile producers.
This discharges the form and auxiliary linear-field premises at the literal
Chapter 12 consumer, without asserting completed U₅ or seven-row recognition.

Source: Aschbacher--Smith 12.2.2, p.795; DGS (11.8), pp.175--176
and Theorem D, p.224; Fong--Seitz I (6A)(c), II (8.13)--(8.15).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
open BenderSuzuki.MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.Source ChapterF.Source.FongSeitzBinary
variable {G X E : Type*} [Group G] [Finite G] [Group X]
  [Field E] [Finite E] [CharP E 2]
  {T : Sylow 2 G} {L V H A B R : Subgroup G} {P : Fin 2 → Subgroup X}
  (D : ChosenModule T L V)
include D

/-- The actual chosen-module pair keeps its given Hermitian form in the full
SU₃ cover and natural action; no Gram matrix or extra field marking is assumed. -/
theorem rankOne_unitary_factor_coordinates_arbitrary_form
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (d : Global.Preparation T L H A B R) (hTH : (T : Subgroup G) ≤ H)
    (Q : MarkedQuotient P)
    (mark : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) Q.standardAmalgam)
    (split : SplitData Q.tits) (hm : rotationOrder Q = 4)
    (J : HermitianForm 3 E) {m : ℕ} (hmpos : 0 < m)
    (hE : Nat.card E = (2^m)^2) (hconj : ∀ x, J.conj x = x^(2^m))
    (hdegree : n = 2*m)
    (hfactor : Nonempty ((R ⧸ pCore 2 R) ≃* J.specialSubgroup) ∨
      Nonempty ((R ⧸ pCore 2 R) ≃* ProjectiveSpecialUnitaryMatrixGroup J))
    (hQ : Nat.card ((parabolic ![L,R] (Global.sourceS L H) 1).pCoreIn 2) = (2^m)^7)
    (hderived : _root_.commutator ((parabolic ![L,R] (Global.sourceS L H) 1).pCoreIn 2) =
      center ((parabolic ![L,R] (Global.sourceS L H) 1).pCoreIn 2))
    (hfrattini : frattini ((parabolic ![L,R] (Global.sourceS L H) 1).pCoreIn 2) =
      center ((parabolic ![L,R] (Global.sourceS L H) 1).pCoreIn 2)) :
    let hf := d.hypothesisF11 (D.rankOne_generic_input_of_many h hmany hn hpsl) hTH
    letI := MarkedLocal.originalRadicalInClosure_normal Q mark hf split 1
    letI : Algebra (ZMod 2) E := ZMod.algebra E 2
    ∃ hr : ∀ k : Fin 2, simpleRemainder Q split k ≤ localKernel Q k ∧
      (simpleRemainder Q split k).comap (MarkedLocal.endpointMap Q mark k) =
        pCore 2 (parabolic ![L,R] (Global.sourceS L H) k),
    ∃ (ξ : (R ⧸ pCore 2 R) ≃* J.specialSubgroup)
      (ν : localGroup Q split 1 ≃* ProjectiveSpecialUnitaryMatrixGroup J)
      (κ : rankOne Q split 1 ≃* J.specialSubgroup)
      (γ : (MarkedLocal.originalLocalClosure Q mark split 1 ⧸
        MarkedLocal.originalRadicalInClosure Q mark split 1) ≃* J.specialSubgroup)
      (c : Additive ((simpleRemainder Q split 1) ⧸ frattini (simpleRemainder Q split 1))
        ≃ₗ[ZMod 2] (Fin 3 → E)),
      (∀ l, ν (MarkedLocal.factorQuotientLocalMap Q mark hf split 1 l) =
        J.specialToProjective (ξ l)) ∧
      (∀ r, ν (RootLocalCover.projection Q split 1 r) = J.specialToProjective (κ r)) ∧
      (RootLocalCover.projection Q split 1).ker = center (rankOne Q split 1) ∧
      (∀ l : R, γ (QuotientGroup.mk' _ (MarkedLocal.originalFactorIntoClosure Q mark hf split 1 l)) =
        ξ (QuotientGroup.mk' (pCore 2 R) l)) ∧
      (∀ r : MarkedLocal.originalRankOne Q mark split 1,
        γ (QuotientGroup.mk' _ (inclusion (MarkedLocal.originalRankOne_le_localClosure Q mark split 1) r)) =
          κ (MarkedLocal.originalRankOneEquiv Q mark split 1 r)) ∧
      ∀ r v, c (elementaryRepresentation (p := 2)
        (Theory.AlgebraicGroup.TitsSystem.SourceBinary.QuadrangleStructure.remainderFrattiniAction
          Q split 1 (hr 1).1) r v) = Matrix.mulVec (κ r).val.val (c v) := by
  let hf := d.hypothesisF11 (D.rankOne_generic_input_of_many h hmany hn hpsl) hTH
  let := MarkedLocal.originalRadicalInClosure_normal Q mark hf split 1
  let : Algebra (ZMod 2) E := ZMod.algebra E 2
  obtain ⟨K,hKfield,hfinK,hcardK,⟨μ⟩⟩ := hpsl
  let := Fintype.ofFinite K
  let : NeZero n := ⟨(Nat.zero_lt_of_lt hn).ne'⟩
  let : CharP K 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hcardK)
  have hK : Nat.card K = (2^m)^2 := by
    rw [hcardK,hdegree,Nat.mul_comm 2 m,pow_mul]
  obtain ⟨hr,f,ξ,ν,κ,γ,c,_,_,_,hfactorSquare,hpanel,hker,hγl,hγr,hc⟩ :=
    QuadrangleStructure.marked_unitary_factor_coordinates_arbitrary_form Q mark hf split
      J hmpos hE hconj hK hm 0 1 (by decide) μ hfactor hQ hderived hfrattini
  exact ⟨hr,ξ,ν,κ,γ,c,hfactorSquare,hpanel,hker,hγl,hγr,hc⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
