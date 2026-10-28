module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.BinaryAffineQuadrangleExclusion
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.QuadrangleStructure.UnitaryFactorOrders

/-!
# The mixed unitary profile in every field from the original factors

Quadrangle regularity now removes the remaining binary-unitary kernel
premise from the original mixed PSL2/SU3-or-PSU3 profile. The previous
factor-order and Frattini arguments provide the quadratic field relation,
core order q^7, both specialness equalities and the full natural action.
No field-size, core-structure or endpoint-perfectness premise is added.

The source quotient application retains literal Q.q representatives,
both original core preimages, the full original factor's projective
square and the scalar kernel. The independent U5 source equations are
still needed for its final marked model comparison.

Source: Fong--Seitz I (5I),(6A)(c), pp.31--37; II (8C);
DGS (11.8), pp.175--176; AS F.1.1--3 and 12.2.2.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped MatrixGroups IsMulCommutative
open BenderSuzuki.MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.QuadrangleStructure
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.QuadrangleStructure
variable {G X K E : Type*} [Group G] [Group X]
  [Field K] [Finite K] [CharP K 2] [Field E] [Finite E] [CharP E 2]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (mark : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits)
  (J : HermitianForm 3 E) {n : ℕ} (hn : 0 < n)
  (hE : Nat.card E = (2^n)^2) (hconj : ∀ x, J.conj x = x^(2^n))
  (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
  (hm : rotationOrder Q = 4) (i j : Fin 2) (hij : i ≠ j)
  (μi : ((L i) ⧸ pCore 2 (L i)) ≃* PSL(2,K))
  (hfactor : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* J.specialSubgroup) ∨
    Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* ProjectiveSpecialUnitaryMatrixGroup J))

include mark h split hn hE hconj hJ hm hij μi hfactor in
/-- All auxiliary U5 profile premises follow from the original mixed
factors, including the binary unitary case. The linear quotient map is the prescribed original map. -/
theorem marked_unitary_factor_profile_all_fields :
    ∃ d : UnitarySource.Combined.FiveProfile L S Q split K E n i j,
      d.form = J ∧
      (∀ a : L i, d.linear_actor (MarkedLocal.originalFactorIntoActor i a) =
        Atlas.RankOneFieldAutomorphisms.slEquivPSL.symm (μi (QuotientGroup.mk' _ a))) ∧
      ∀ k : Fin 2, simpleRemainder Q split k ≤ localKernel Q k ∧
        (simpleRemainder Q split k).comap (MarkedLocal.endpointMap Q mark k) =
          pCore 2 (parabolic L S k) := by
  exact marked_unitary_factor_profile_of_regular Q mark h split J hn hE hconj hJ
    hm i j hij μi hfactor
    (MarkedLocal.marked_quadrangle_regularity Q mark h split hm j).1

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.QuadrangleStructure

namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.QuadrangleStructure
variable {G K E : Type*} [Group G] [Field K] [Finite K] [CharP K 2] [Field E] [Finite E] [CharP E 2]
  {L : Fin 2 → Subgroup G} {S : Subgroup G}
  (Q : SourceQuotient L S) (split : SplitData Q.tits)
  (h : HypothesisF11 L S)
  (J : HermitianForm 3 E) {n : ℕ} (hn : 0 < n)
  (hE : Nat.card E = (2^n)^2)
  (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
  (hconj : ∀ x, J.conj x = x^(2^n))
  (hm : rotationOrder Q = 4) (i j : Fin 2) (hij : i ≠ j)
  (μi : ((L i) ⧸ pCore 2 (L i)) ≃* PSL(2,K))
  (hfactor : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* J.specialSubgroup) ∨
    Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* ProjectiveSpecialUnitaryMatrixGroup J))
include h hn hE hJ hconj hm hij hfactor μi

/-- The same natural action on literal source quotient representatives, with
both original core preimages and the original factor's projective square. -/
theorem original_unitary_factor_representatives_all_fields :
    letI : Algebra (ZMod 2) E := ZMod.algebra E 2
    ∃ _hr : ∀ k : Fin 2, simpleRemainder Q split k ≤ localKernel Q k ∧
      (simpleRemainder Q split k).comap (MarkedLocal.endpointMap Q (originalMarkedIso Q) k) =
        pCore 2 (parabolic L S k),
    ∃ (ξ : ((L j) ⧸ pCore 2 (L j)) ≃* J.specialSubgroup)
      (ν : localGroup Q split j ≃* ProjectiveSpecialUnitaryMatrixGroup J)
      (κ : rankOne Q split j ≃* J.specialSubgroup)
      (c : Additive ((simpleRemainder Q split j) ⧸ frattini (simpleRemainder Q split j))
        ≃ₗ[ZMod 2] (Fin 3 → E)),
      (∀ r, ν (RootLocalCover.projection Q split j r) = J.specialToProjective (κ r)) ∧
      (∀ l, ν (MarkedLocal.factorQuotientLocalMap Q (originalMarkedIso Q) h split j l) =
        J.specialToProjective (ξ l)) ∧
      (RootLocalCover.projection Q split j).ker = center (rankOne Q split j) ∧
      ∀ (a v : generated L S) (ha : Q.q a ∈ rankOne Q split j)
        (hv : Q.q v ∈ simpleRemainder Q split j),
        ∃ w : simpleRemainder Q split j,
          (w : (generated L S) ⧸ Q.D) = Q.q (a*v*a⁻¹) ∧
          c (Additive.ofMul (QuotientGroup.mk' (frattini (simpleRemainder Q split j)) w)) =
            Matrix.mulVec (κ ⟨Q.q a,ha⟩).val.val
              (c (Additive.ofMul (QuotientGroup.mk' (frattini (simpleRemainder Q split j))
                ⟨Q.q v,hv⟩))) := by
  exact original_unitary_factor_representatives_of_regular Q split h J hn hE hJ hconj hm i j hij
    μi hfactor (MarkedLocal.marked_quadrangle_regularity Q (originalMarkedIso Q) h split hm j).1
end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.QuadrangleStructure

