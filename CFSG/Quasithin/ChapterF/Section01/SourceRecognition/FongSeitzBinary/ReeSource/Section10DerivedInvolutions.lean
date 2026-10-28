module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.PerpendicularExclusion
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.Section10DerivedFrattini

/-!
# The p.55 involution calculation at the Section 10 interface

Whole-perpendicular-root containment in the Frattini subgroup is excluded
at every literal N-conjugate, and the intersection is exactly the conjugated
Omega root. The intermediate outer-linear commutator bound is also retained.
No (6H) or source-coordinate record is assumed here.
Source: Fong--Seitz I (1973), proof of (6H)(f), p.55; II (10.3), p.221.
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
/-- Under the whole-perpendicular-root alternative, the outer linear-root
commutators lie in J at every literal N-conjugate used by Section 10. -/
theorem source_ten_three_far_linear_le_five_of_perpendicular_le
    (hc : centralizer (pCore 2 (Endpoint Q 1) : Set (Endpoint Q 1)) ≤ pCore 2 (Endpoint Q 1))
    (hm : rotationOrder Q = 8) (hcore : Q.tits.B.normalCore = ⊥) (w : Q.tits.N)
    (hE : nConj (Uat Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0)) w ≤
      phi (nConj (simpleRemainder Q split 1) w)) :
    ⁅nConj (simpleRoot Q split 0) w,nConj (Uat Q split 0 (Q.simple 1)) w⁆ ≤
      nConj (fiveDerivedSubgroup Q split) w := by
  let f := (MulAut.conj (w : X ⧸ Q.D)).symm
  have hr (A : Subgroup (X ⧸ Q.D)) : nConj A w = A.map f.toMonoidHom := by
    simp only [nConj,rightConjugate,comap_equiv_eq_map_symm']; rfl
  have hphi : phi (nConj (simpleRemainder Q split 1) w) =
      (⁅simpleRemainder Q split 1,simpleRemainder Q split 1⁆).map f.toMonoidHom := by
    rw [←source_ten_three_frattini Q split n hn m ν T hC μ hB hc hm hcore w,hr,←map_commutator]
  rw [hphi,hr] at hE
  rw [hr,hr,hr,←map_commutator]
  exact map_mono (source_far_linear_le_five_of_perpendicular_le_derived Q split n hn m ν T hC μ hB
    hm hcore hc ((map_le_map_iff_of_injective f.injective).mp hE))

include ν hC μ hB hn in
/-- The p.55 whole-root exclusion holds at every literal Section 10 N-conjugate. -/
theorem source_ten_three_perpendicular_not_le_frattini
    (hc : centralizer (pCore 2 (Endpoint Q 1) : Set (Endpoint Q 1)) ≤ pCore 2 (Endpoint Q 1))
    (hm : rotationOrder Q = 8) (hcore : Q.tits.B.normalCore = ⊥) (w : Q.tits.N) :
    ¬ nConj (Uat Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0)) w ≤
      phi (nConj (simpleRemainder Q split 1) w) := by
  let f := (MulAut.conj (w : X ⧸ Q.D)).symm
  have hr (A : Subgroup (X ⧸ Q.D)) : nConj A w = A.map f.toMonoidHom := by
    simp only [nConj,rightConjugate,comap_equiv_eq_map_symm']; rfl
  have hphi : phi (nConj (simpleRemainder Q split 1) w) =
      (⁅simpleRemainder Q split 1,simpleRemainder Q split 1⁆).map f.toMonoidHom := by
    rw [←source_ten_three_frattini Q split n hn m ν T hC μ hB hc hm hcore w,hr,←map_commutator]
  intro hE
  rw [hphi,hr] at hE
  exact source_perpendicular_not_le_derived Q split n hn m ν T hC μ hB hm hcore hc
    ((map_le_map_iff_of_injective f.injective).mp hE)

include ν hC μ hB hn in
/-- The exact perpendicular intersection at all N-conjugates of the literal Frattini subgroup. -/
theorem source_ten_three_frattini_inf_perpendicular
    (hc : centralizer (pCore 2 (Endpoint Q 1) : Set (Endpoint Q 1)) ≤ pCore 2 (Endpoint Q 1))
    (hm : rotationOrder Q = 8) (hcore : Q.tits.B.normalCore = ⊥) (w : Q.tits.N) :
    phi (nConj (simpleRemainder Q split 1) w) ⊓
      nConj (Uat Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0)) w =
      nConj (omega (Uat Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0))) w := by
  let f := (MulAut.conj (w : X ⧸ Q.D)).symm
  have hr (A : Subgroup (X ⧸ Q.D)) : nConj A w = A.map f.toMonoidHom := by
    simp only [nConj,rightConjugate,comap_equiv_eq_map_symm']; rfl
  have hphi : phi (nConj (simpleRemainder Q split 1) w) =
      (⁅simpleRemainder Q split 1,simpleRemainder Q split 1⁆).map f.toMonoidHom := by
    rw [←source_ten_three_frattini Q split n hn m ν T hC μ hB hc hm hcore w,hr,←map_commutator]
  rw [hphi,hr,hr,←map_inf _ _ _ f.injective]
  exact congrArg (fun A : Subgroup (X ⧸ Q.D) => A.map f.toMonoidHom)
    (source_derived_inf_perpendicular_eq_omega Q split n hn m ν T hC μ hB hm hcore hc)

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
