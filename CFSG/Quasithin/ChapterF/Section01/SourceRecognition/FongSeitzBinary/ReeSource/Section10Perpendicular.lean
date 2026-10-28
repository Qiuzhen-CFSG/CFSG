module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.PositiveSixFourEquality
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.LinearNear
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.Section10Near

/-!
# Further near and perpendicular clauses at the Section 10 interface

The source proof of (6H)(d) supplies (10.2)(iv), right-hand clause, at every
literal N-conjugate on the same marked quotient. Every statement includes
q=2, with the original positive-parameter specializations preserved. Both
(10.2)(iii) clauses retain the actual root Omega. Source: Fong--Seitz I,
pp.54--55, and II (10.2), p.221.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
open Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)
  (n : ℕ) (hn : Odd n) (m : ℕ)
  (ν : (Endpoint Q 0 ⧸ panelKernel Q 0) ≃* PSL2BinaryMatrixGroup n)
  (T : Sylow 2 (PSL2BinaryMatrixGroup n))
  (hC : (quotientBorel Q 0).map ν.toMonoidHom = normalizer (T : Set _))
  (μ : (Endpoint Q 1 ⧸ panelKernel Q 1) ≃* SuzukiMatrixGroup m)
  (hB : (quotientBorel Q 1).map μ.toMonoidHom = normalizer (SuzukiRootSubgroup m : Set _))

include ν hC μ hB hn in
/-- The all-parameter Suzuki part of (10.2)(iv), with every actual N-conjugate. -/
theorem source_ten_two_iv_right
    (hc : centralizer (pCore 2 (Endpoint Q 1) : Set (Endpoint Q 1)) ≤ pCore 2 (Endpoint Q 1))
    (hm : rotationOrder Q = 8) (hcore : Q.tits.B.normalCore = ⊥) (w : Q.tits.N) :
    ⁅nConj (U Q split 1) w,nConj (Uat Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0)) w⁆ = ⊥ := by
  have h := source_perpendicular_commute Q split n hn m ν T hC μ hB hm hcore hc
  have hw := congrArg (fun A : Subgroup (X ⧸ Q.D) => rightConjugate A (w : X ⧸ Q.D)) h
  simpa only [nConj,U,Uat,rightConjugate,comap_equiv_eq_map_symm',map_commutator,Subgroup.map_bot] using hw

include ν hC μ hB hn in
/-- The full linear near clause (10.2)(i), including q=2. -/
theorem source_ten_two_i
    (hc : centralizer (pCore 2 (Endpoint Q 1) : Set (Endpoint Q 1)) ≤ pCore 2 (Endpoint Q 1))
    (hm : rotationOrder Q = 8) (hcore : Q.tits.B.normalCore = ⊥) (w : Q.tits.N) :
    ⁅nConj (U Q split 0) w,nConj (Uat Q split 0 (Q.simple 1*Q.simple 0)) w⁆ = ⊥ := by
  have h := source_linear_near_commute Q split n hn m ν T hC μ hB hm hcore hc
  have hw := congrArg (fun A : Subgroup (X ⧸ Q.D) => rightConjugate A (w : X ⧸ Q.D)) h
  simpa only [nConj,U,Uat,rightConjugate,comap_equiv_eq_map_symm',map_commutator,Subgroup.map_bot] using hw

include ν hC μ hB hn in
/-- Both all-parameter clauses of (10.2)(iii), at every actual N-conjugate. -/
theorem source_ten_two_iii
    (hc : centralizer (pCore 2 (Endpoint Q 1) : Set (Endpoint Q 1)) ≤ pCore 2 (Endpoint Q 1))
    (hm : rotationOrder Q = 8) (hcore : Q.tits.B.normalCore = ⊥) (w : Q.tits.N) :
    ⁅nConj (U Q split 1) w,nConj (Uat Q split 0 (Q.simple 1*Q.simple 0*Q.simple 1)) w⁆ =
        nConj (omega (Uat Q split 1 (Q.simple 0*Q.simple 1))) w ∧
      ⁅nConj (omega (U Q split 1)) w,nConj (Uat Q split 0 (Q.simple 1*Q.simple 0*Q.simple 1)) w⁆ = ⊥ := by
  constructor
  · have h := source_six_four_eq Q split n hn m ν T hC μ hB hm hcore hc
    have hw := congrArg (fun A : Subgroup (X ⧸ Q.D) => rightConjugate A (w : X ⧸ Q.D)) h
    simpa only [nConj,U,Uat,Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10.omega,rightConjugate,comap_equiv_eq_map_symm',map_commutator] using hw
  · exact source_ten_two_iii_right Q split n hn m ν T hC μ hB hc hm hcore w

set_option linter.unusedVariables false in
include ν hC μ hB hn in
/-- Existing positive-parameter specialization, retained for compatibility. -/
theorem source_ten_two_iv_right_positive
    (hc : centralizer (pCore 2 (Endpoint Q 1) : Set (Endpoint Q 1)) ≤ pCore 2 (Endpoint Q 1))
    (hm : rotationOrder Q = 8) (hcore : Q.tits.B.normalCore = ⊥) (hmpos : 0 < m) (w : Q.tits.N) :
    ⁅nConj (U Q split 1) w,nConj (Uat Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0)) w⁆ = ⊥ := by
  exact source_ten_two_iv_right Q split n hn m ν T hC μ hB hc hm hcore w

set_option linter.unusedVariables false in
include ν hC μ hB hn in
/-- Existing positive-parameter specialization, retained for compatibility. -/
theorem source_ten_two_iii_positive
    (hc : centralizer (pCore 2 (Endpoint Q 1) : Set (Endpoint Q 1)) ≤ pCore 2 (Endpoint Q 1))
    (hm : rotationOrder Q = 8) (hcore : Q.tits.B.normalCore = ⊥) (hmpos : 0 < m) (w : Q.tits.N) :
    ⁅nConj (U Q split 1) w,nConj (Uat Q split 0 (Q.simple 1*Q.simple 0*Q.simple 1)) w⁆ =
        nConj (omega (Uat Q split 1 (Q.simple 0*Q.simple 1))) w ∧
      ⁅nConj (omega (U Q split 1)) w,nConj (Uat Q split 0 (Q.simple 1*Q.simple 0*Q.simple 1)) w⁆ = ⊥ := by
  exact source_ten_two_iii Q split n hn m ν T hC μ hB hc hm hcore w

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
