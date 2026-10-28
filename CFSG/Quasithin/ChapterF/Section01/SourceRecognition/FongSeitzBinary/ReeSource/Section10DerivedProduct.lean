module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.DerivedProduct
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.Section10FiveFactors

/-!
# The full derived product at the Section 10 interface

The exact (6H)(f) equality supplies the literal ordered product and the
vanishing second Frattini subgroup in (10.3), at every actual N-conjugate.
These are proofs from the natural panel markings and odd linear degree;
no ReeSixHData or coordinate certificate is assumed.
Source: Fong--Seitz I (1973), (6H)(f), p.55; II (1974), (10.3), p.221.
-/

@[expose] public noncomputable section
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


include ν hC μ hB hn in
/-- The actual Frattini subgroup equals the five-factor subgroup at every N-conjugate. -/
theorem source_ten_three_frattini_eq_five
    (hc : centralizer (pCore 2 (Endpoint Q 1) : Set (Endpoint Q 1)) ≤ pCore 2 (Endpoint Q 1))
    (hm : rotationOrder Q = 8) (hcore : Q.tits.B.normalCore = ⊥) (w : Q.tits.N) :
    phi (nConj (simpleRemainder Q split 1) w) = nConj (fiveDerivedSubgroup Q split) w := by
  let f := (MulAut.conj (w : X ⧸ Q.D)).symm
  have hr (A : Subgroup (X ⧸ Q.D)) : nConj A w = A.map f.toMonoidHom := by
    simp only [nConj,rightConjugate,comap_equiv_eq_map_symm']; rfl
  rw [←source_ten_three_frattini Q split n hn m ν T hC μ hB hc hm hcore w,
    hr,hr,←map_commutator,
    source_radical_derived_eq_five Q split n hn m ν T hC μ hB hm hcore hc]

include ν hC μ hB hn in
/-- The full literal product clause of (10.3). -/
theorem source_ten_three_product
    (hc : centralizer (pCore 2 (Endpoint Q 1) : Set (Endpoint Q 1)) ≤ pCore 2 (Endpoint Q 1))
    (hm : rotationOrder Q = 8) (hcore : Q.tits.B.normalCore = ⊥) (w : Q.tits.N) :
    (phi (nConj (simpleRemainder Q split 1) w) : Set (X ⧸ Q.D)) =
      (nConj (omega (Uat Q split 1 (Q.simple 0*Q.simple 1))) w : Set (X ⧸ Q.D)) *
      (nConj (Uat Q split 0 (Q.simple 1*Q.simple 0*Q.simple 1)) w : Set (X ⧸ Q.D)) *
      (nConj (omega (Uat Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0))) w : Set (X ⧸ Q.D)) *
      (nConj (Uat Q split 0 (Q.simple 1*Q.simple 0)) w : Set (X ⧸ Q.D)) *
      (nConj (omega (Uat Q split 1 (Q.simple 0))) w : Set (X ⧸ Q.D)) := by
  rw [source_ten_three_frattini_eq_five Q split n hn m ν T hC μ hB hc hm hcore w]
  exact source_ten_three_five_product Q split n hn m ν T hC μ hB hc hm hcore w

include ν hC μ hB hn in
/-- The second Frattini subgroup in (10.3) is trivial, including q=2. -/
theorem source_ten_three_frattini_square
    (hc : centralizer (pCore 2 (Endpoint Q 1) : Set (Endpoint Q 1)) ≤ pCore 2 (Endpoint Q 1))
    (hm : rotationOrder Q = 8) (hcore : Q.tits.B.normalCore = ⊥) (w : Q.tits.N) :
    phi (phi (nConj (simpleRemainder Q split 1) w)) = ⊥ := by
  rw [source_ten_three_frattini_eq_five Q split n hn m ν T hC μ hB hc hm hcore w]
  let : IsElementaryAbelian 2 (nConj (fiveDerivedSubgroup Q split) w) :=
    (source_ten_three_five_data Q split n hn m ν T hC μ hB hc hm hcore w).1
  let : Fact (IsPGroup 2 (nConj (fiveDerivedSubgroup Q split) w)) := ⟨IsElementaryAbelian.isPGroup 2 _⟩
  unfold phi
  rw [frattini_eq_bot_of_isElementaryAbelian (p := 2),Subgroup.map_bot]

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
