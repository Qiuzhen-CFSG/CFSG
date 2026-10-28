module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.Centers
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.Section10ThirdCommutator

/-!
# Both full center clauses at every Section 10 conjugate

The source identities Z(U)=Z(V)=Ω₁(E) are transported by the literal
N-action. These discharge both remaining center fields of SixHRelations,
including q=2, without an assumed center bound.
Source: Fong--Seitz I (6H)(g), p.55; II (10.3)(iii), p.221.
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

private theorem map_zeta (A : Subgroup (X ⧸ Q.D)) (f : (X ⧸ Q.D) ≃* (X ⧸ Q.D)) :
    (zeta A).map f.toMonoidHom = zeta (A.map f.toMonoidHom) := by
  let e := A.equivMapOfInjective f.toMonoidHom f.injective
  have he : f.toMonoidHom.comp A.subtype = (A.map f.toMonoidHom).subtype.comp e.toMonoidHom := rfl
  change ((center A).map A.subtype).map f.toMonoidHom = _
  rw [map_map,he,←map_map,center_map_equiv]
  rfl

include ν hC μ hB hn in
/-- The full radical-center clause of (10.3) at each actual N-conjugate. -/
theorem source_ten_three_center_remainder
    (hc : centralizer (pCore 2 (Endpoint Q 1) : Set (Endpoint Q 1)) ≤ pCore 2 (Endpoint Q 1))
    (hm : rotationOrder Q = 8) (hcore : Q.tits.B.normalCore = ⊥) (w : Q.tits.N) :
    Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10.omega (nConj (Uat Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0)) w) =
      zeta (nConj (simpleRemainder Q split 1) w) := by
  let f := (MulAut.conj (w : X ⧸ Q.D)).symm
  have hr (A : Subgroup (X ⧸ Q.D)) : nConj A w = A.map f.toMonoidHom := by
    simp only [nConj,rightConjugate,comap_equiv_eq_map_symm']; rfl
  simp only [hr,Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10.omega,Uat]
  rw [←map_omegaOneAmbient_injective f.toMonoidHom f.injective,←map_zeta]
  exact congrArg (Subgroup.map f.toMonoidHom)
    (source_radical_center_eq_omega Q split n hn m ν T hC μ hB hm hcore hc).symm

include ν hC μ hB hn in
/-- The full radical and unipotent centers agree under every actual N-conjugation. -/
theorem source_ten_three_center_unipotent
    (hc : centralizer (pCore 2 (Endpoint Q 1) : Set (Endpoint Q 1)) ≤ pCore 2 (Endpoint Q 1))
    (hm : rotationOrder Q = 8) (hcore : Q.tits.B.normalCore = ⊥) (w : Q.tits.N) :
    zeta (nConj (simpleRemainder Q split 1) w) = zeta (nConj split.U w) := by
  let f := (MulAut.conj (w : X ⧸ Q.D)).symm
  have hr (A : Subgroup (X ⧸ Q.D)) : nConj A w = A.map f.toMonoidHom := by
    simp only [nConj,rightConjugate,comap_equiv_eq_map_symm']; rfl
  simp only [hr,←map_zeta]
  exact congrArg (Subgroup.map f.toMonoidHom)
    ((source_radical_center_eq_omega Q split n hn m ν T hC μ hB hm hcore hc).trans
      (source_unipotent_center_eq_omega Q split n hn m ν T hC μ hB hm hcore hc).symm)

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
