module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.DerivedFrattini
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.Section10Perpendicular

/-!
# The derived/Frattini equality at the literal Section 10 interface

The source proof of (6H)(f) gives the first equality of (10.3) at every
actual N-conjugate. Frattini transport uses the same conjugation map as
the subgroup commutator. All parameters, including q=2, are retained.
The remaining product and center fields are not assumed or constructed here.

Source: Fong--Seitz II (1974), (10.3), printed p.221.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
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

include hn ν hC μ hB in
/-- The derived/Frattini clause of (10.3) at every literal N-conjugate. -/
theorem source_ten_three_frattini
    (hc : centralizer (pCore 2 (Endpoint Q 1) : Set (Endpoint Q 1)) ≤ pCore 2 (Endpoint Q 1))
    (hm : rotationOrder Q = 8) (hcore : Q.tits.B.normalCore = ⊥) (w : Q.tits.N) :
    ⁅nConj (simpleRemainder Q split 1) w,nConj (simpleRemainder Q split 1) w⁆ =
      phi (nConj (simpleRemainder Q split 1) w) := by
  let f := (MulAut.conj (w : X ⧸ Q.D)).symm
  have h := congrArg (fun A : Subgroup (X ⧸ Q.D) => A.map f.toMonoidHom)
    (source_radical_derived_eq_frattini Q split n hn m ν T hC μ hB hm hcore hc)
  rw [map_commutator,←frattini_image_map _ _ f.injective] at h
  have he : nConj (simpleRemainder Q split 1) w =
      (simpleRemainder Q split 1).map f.toMonoidHom := by
    simp only [nConj,rightConjugate,comap_equiv_eq_map_symm']
    rfl
  rw [he]
  exact h

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
