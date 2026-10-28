module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.FiveFactors
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.Section10DerivedFrattini

/-!
# The five elementary factors at the literal Section 10 interface

At every actual N-conjugate, the right side of (10.3)'s product identity
is an elementary abelian subgroup of order q⁵ contained in the literal
Frattini subgroup. Its product and factor conventions agree exactly with
SixHRelations.ten_three_product. The hypothetical whole-perpendicular-root
case has Frattini subgroup JE and Omega subgroup J on this same carrier.
Excluding that case and proving the reverse product containment remain
with the source assembly; no SixHRelations record is assumed here.
Source: Fong--Seitz I (1973), proof of (6H)(f), p.55;
II (1974), (10.3), p.221.
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
/-- The right side of the literal (10.3) product is the conjugated five-factor subgroup. -/
theorem source_ten_three_five_product
    (hc : centralizer (pCore 2 (Endpoint Q 1) : Set (Endpoint Q 1)) ≤ pCore 2 (Endpoint Q 1))
    (hm : rotationOrder Q = 8) (hcore : Q.tits.B.normalCore = ⊥) (w : Q.tits.N) :
    (nConj (fiveDerivedSubgroup Q split) w : Set (X ⧸ Q.D)) =
      (nConj (omega (Uat Q split 1 (Q.simple 0*Q.simple 1))) w : Set (X ⧸ Q.D)) *
      (nConj (Uat Q split 0 (Q.simple 1*Q.simple 0*Q.simple 1)) w : Set (X ⧸ Q.D)) *
      (nConj (omega (Uat Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0))) w : Set (X ⧸ Q.D)) *
      (nConj (Uat Q split 0 (Q.simple 1*Q.simple 0)) w : Set (X ⧸ Q.D)) *
      (nConj (omega (Uat Q split 1 (Q.simple 0))) w : Set (X ⧸ Q.D)) := by
  let f := (MulAut.conj (w : X ⧸ Q.D)).symm
  have hr (A : Subgroup (X ⧸ Q.D)) : nConj A w = A.map f.toMonoidHom := by
    simp only [nConj,rightConjugate,comap_equiv_eq_map_symm']; rfl
  have h := congrArg (fun S : Set (X ⧸ Q.D) => f.toMonoidHom '' S)
    (source_five_derived_elementary_product Q split n hn m ν T hC μ hB hm hcore hc).2
  simp only [Set.image_mul] at h
  dsimp [fiveDerivedFactor] at h
  simpa only [hr,coe_map,Uat,MulEquiv.coe_toMonoidHom,
    Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10.omega] using h

include ν hC μ hB hn in
/-- The five-factor subgroup is elementary abelian of order q⁵ inside the actual Frattini subgroup. -/
theorem source_ten_three_five_data
    (hc : centralizer (pCore 2 (Endpoint Q 1) : Set (Endpoint Q 1)) ≤ pCore 2 (Endpoint Q 1))
    (hm : rotationOrder Q = 8) (hcore : Q.tits.B.normalCore = ⊥) (w : Q.tits.N) :
    IsElementaryAbelian 2 (nConj (fiveDerivedSubgroup Q split) w) ∧
      Nat.card (nConj (fiveDerivedSubgroup Q split) w) = (2^(2*m+1))^5 ∧
      nConj (fiveDerivedSubgroup Q split) w ≤ phi (nConj (simpleRemainder Q split 1) w) := by
  let f := (MulAut.conj (w : X ⧸ Q.D)).symm
  have hr (A : Subgroup (X ⧸ Q.D)) : nConj A w = A.map f.toMonoidHom := by
    simp only [nConj,rightConjugate,comap_equiv_eq_map_symm']; rfl
  let : IsElementaryAbelian 2 (fiveDerivedSubgroup Q split) :=
    (source_five_derived_elementary_product Q split n hn m ν T hC μ hB hm hcore hc).1
  refine ⟨?_,?_,?_⟩
  · rw [hr]
    exact IsElementaryAbelian.map f.toMonoidHom
  · rw [hr,card_map_of_injective f.injective]
    exact source_five_derived_card Q split n hn m ν T hC μ hB hm hcore hc
  · rw [←source_ten_three_frattini Q split n hn m ν T hC μ hB hc hm hcore w,hr,hr,←map_commutator]
    exact map_mono (source_five_derived_le Q split n hn m ν T hC μ hB hm hcore hc)

include ν hC μ hB hn in
/-- The p.55 whole-root alternative after every literal N-conjugation used in (10.3). -/
theorem source_ten_three_perpendicular_in_derived_case
    (hc : centralizer (pCore 2 (Endpoint Q 1) : Set (Endpoint Q 1)) ≤ pCore 2 (Endpoint Q 1))
    (hm : rotationOrder Q = 8) (hcore : Q.tits.B.normalCore = ⊥) (w : Q.tits.N)
    (hE : nConj (Uat Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0)) w ≤
      phi (nConj (simpleRemainder Q split 1) w)) :
    phi (nConj (simpleRemainder Q split 1) w) =
        nConj (fiveDerivedSubgroup Q split) w ⊔ nConj (Uat Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0)) w ∧
      Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10.omega (phi (nConj (simpleRemainder Q split 1) w)) = nConj (fiveDerivedSubgroup Q split) w := by
  let f := (MulAut.conj (w : X ⧸ Q.D)).symm
  have hr (A : Subgroup (X ⧸ Q.D)) : nConj A w = A.map f.toMonoidHom := by
    simp only [nConj,rightConjugate,comap_equiv_eq_map_symm']; rfl
  have hphi : phi (nConj (simpleRemainder Q split 1) w) =
      (⁅simpleRemainder Q split 1,simpleRemainder Q split 1⁆).map f.toMonoidHom := by
    rw [←source_ten_three_frattini Q split n hn m ν T hC μ hB hc hm hcore w,hr,←map_commutator]
  rw [hphi,hr] at hE
  have h := source_perpendicular_in_derived_case Q split n hn m ν T hC μ hB hm hcore hc
    ((map_le_map_iff_of_injective f.injective).mp hE)
  rw [hphi,hr,hr]
  constructor
  · rw [h.1,Subgroup.map_sup]; rfl
  · change omegaOneAmbient ((⁅simpleRemainder Q split 1,simpleRemainder Q split 1⁆).map f.toMonoidHom) = _
    rw [←map_omegaOneAmbient_injective f.toMonoidHom f.injective,h.2]

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
