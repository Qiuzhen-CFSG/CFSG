module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.ThirdCommutator
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.Section10DerivedProduct

/-!
# Remaining mixed equations and the third commutator for Section 10

The actual source proofs supply (10.2)(iv) on the linear roots, the stronger
equality in (10.2)(v), and [Φ(V),V]=Ω₁(E) in (10.3), under all literal
N-conjugations. The identification of Ω₁(E) with the full centers of V
and U remains a separate source obligation.
Source: Fong--Seitz I (1973), (6H)(d,e,g), pp.55--56; II (1974), p.221.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory
open scoped Pointwise
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open BenderSuzuki.MatrixGroups BenderSuzuki.PFAppendixIII

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


private theorem ncomm (A B : Subgroup (X ⧸ Q.D)) (w : Q.tits.N) :
    nConj ⁅A,B⁆ w = ⁅nConj A w,nConj B w⁆ := by
  simp only [nConj,rightConjugate,comap_equiv_eq_map_symm',map_commutator]
private theorem nbot (w : Q.tits.N) : nConj (⊥ : Subgroup (X ⧸ Q.D)) w = ⊥ := by
  simp only [nConj,rightConjugate,comap_equiv_eq_map_symm',Subgroup.map_bot]

include ν hC μ hB hn in
/-- The perpendicular linear commutation clause (10.2)(iv), at all actual N-conjugates. -/
theorem source_ten_two_iv_left
    (hc : centralizer (pCore 2 (Endpoint Q 1) : Set (Endpoint Q 1)) ≤ pCore 2 (Endpoint Q 1))
    (hm : rotationOrder Q = 8) (hcore : Q.tits.B.normalCore = ⊥) (w : Q.tits.N) :
    ⁅nConj (U Q split 0) w,nConj (Uat Q split 0 (Q.simple 1*Q.simple 0*Q.simple 1)) w⁆ = ⊥ := by
  have h := congrArg (fun A => nConj A w)
    (source_linear_perpendicular_commute Q split n hn m ν T hC μ hB hm hcore hc)
  simpa only [U,Uat,ncomm,nbot] using h

include ν hC μ hB hn in
/-- The full Omega equality strengthens the inclusion retained in (10.2)(v). -/
theorem source_ten_two_v_eq
    (hc : centralizer (pCore 2 (Endpoint Q 1) : Set (Endpoint Q 1)) ≤ pCore 2 (Endpoint Q 1))
    (hm : rotationOrder Q = 8) (hcore : Q.tits.B.normalCore = ⊥) (w : Q.tits.N) :
    ⁅nConj (omega (U Q split 1)) w,nConj (Uat Q split 0 (Q.simple 1*Q.simple 0)) w⁆ =
      nConj (omega (Uat Q split 1 (Q.simple 0*Q.simple 1))) w := by
  have h := congrArg (fun A => nConj A w)
    (source_omega_far_linear_eq Q split n hn m ν T hC μ hB hm hcore hc)
  simpa only [U,Uat,Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10.omega,ncomm] using h

include ν hC μ hB hn in
/-- The third commutator equality in (10.3), including every actual N-conjugate. -/
theorem source_ten_three_center_commutator
    (hc : centralizer (pCore 2 (Endpoint Q 1) : Set (Endpoint Q 1)) ≤ pCore 2 (Endpoint Q 1))
    (hm : rotationOrder Q = 8) (hcore : Q.tits.B.normalCore = ⊥) (w : Q.tits.N) :
    ⁅phi (nConj (simpleRemainder Q split 1) w),nConj (simpleRemainder Q split 1) w⁆ =
      Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10.omega (nConj (Uat Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0)) w) := by
  rw [←source_ten_three_frattini Q split n hn m ν T hC μ hB hc hm hcore w,
    commutator_comm,←ncomm,←ncomm,
    source_radical_third_eq_omega Q split n hn m ν T hC μ hB hm hcore hc]
  simp only [nConj,Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10.omega,rightConjugate,comap_equiv_eq_map_symm']
  exact map_omegaOneAmbient_injective _ (MulEquiv.injective _) _

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
