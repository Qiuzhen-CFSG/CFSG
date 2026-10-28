module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.Centralizers
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.Section10DerivedFrattini
public import Theory.GroupTheory.CentralizerInjectiveImage

/-!
# Source centralizers and central Omega at the Section 10 interface

The proved perpendicular Omega lies in both literal centers in (10.3),
at every actual N-conjugate. These are the lower center inclusions; their
reverse inclusions and the five-factor product still require source proofs.
The exact intersection of the center with the perpendicular root and its
fixed subgroup under the whole Suzuki actor are transported as well.
The whole Suzuki actor centralizer is also transported on this same carrier,
identifying its fixed perpendicular root without assuming any natural module.

Source: Fong--Seitz I (1973), proof of (6H)(c),(g), p.55;
II (1974), (10.3), p.221.
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
/-- The proved lower inclusions for both center clauses of (10.3), at every actual N-conjugate. -/
theorem source_ten_three_omega_le_centers
    (hc : centralizer (pCore 2 (Endpoint Q 1) : Set (Endpoint Q 1)) ≤ pCore 2 (Endpoint Q 1))
    (hm : rotationOrder Q = 8) (hcore : Q.tits.B.normalCore = ⊥) (w : Q.tits.N) :
    nConj (omega (Uat Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0))) w ≤
        zeta (nConj split.U w) ∧
      nConj (omega (Uat Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0))) w ≤
        zeta (nConj (simpleRemainder Q split 1) w) := by
  let f := (MulAut.conj (w : X ⧸ Q.D)).symm
  have hr (A : Subgroup (X ⧸ Q.D)) : nConj A w = A.map f.toMonoidHom := by
    simp only [nConj,rightConjugate,comap_equiv_eq_map_symm']; rfl
  have h := source_perpendicular_omega_le_centers Q split n hn m ν T hC μ hB hm hcore hc
  have hu := map_mono (f := f.toMonoidHom) h.1
  have hv := map_mono (f := f.toMonoidHom) h.2
  change (zeta split.U).map f.toMonoidHom ≥ _ at hu
  change (zeta (simpleRemainder Q split 1)).map f.toMonoidHom ≥ _ at hv
  rw [map_zeta] at hu hv
  simpa only [hr,Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10.omega,Uat] using And.intro hu hv

include ν hC μ hB hn in
/-- The full Suzuki actor centralizer, transported by the literal N-action used in Section 10. -/
theorem source_ten_suzuki_actor_radical_centralizer
    (hc : centralizer (pCore 2 (Endpoint Q 1) : Set (Endpoint Q 1)) ≤ pCore 2 (Endpoint Q 1))
    (hm : rotationOrder Q = 8) (hcore : Q.tits.B.normalCore = ⊥) (w : Q.tits.N) :
    nConj (simpleRemainder Q split 1) w ⊓ centralizer (nConj (rankOne Q split 1) w : Set (X ⧸ Q.D)) =
      nConj (Uat Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0)) w := by
  let f := (MulAut.conj (w : X ⧸ Q.D)).symm
  have hr (A : Subgroup (X ⧸ Q.D)) : nConj A w = A.map f.toMonoidHom := by
    simp only [nConj,rightConjugate,comap_equiv_eq_map_symm']; rfl
  simp only [hr]
  rw [map_inf_centralizer_of_injective f.toMonoidHom f.injective,
    source_suzuki_actor_radical_centralizer Q split n hn m ν T hC μ hB hm hcore hc]
  rfl


include ν hC μ hB hn in
/-- The exact central intersection with the perpendicular root in the Section 10 conventions. -/
theorem source_ten_three_perpendicular_center_intersection
    (hc : centralizer (pCore 2 (Endpoint Q 1) : Set (Endpoint Q 1)) ≤ pCore 2 (Endpoint Q 1))
    (hm : rotationOrder Q = 8) (hcore : Q.tits.B.normalCore = ⊥) (w : Q.tits.N) :
    zeta (nConj (simpleRemainder Q split 1) w) ⊓
        nConj (Uat Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0)) w =
      nConj (omega (Uat Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0))) w := by
  let f := (MulAut.conj (w : X ⧸ Q.D)).symm
  have hr (A : Subgroup (X ⧸ Q.D)) : nConj A w = A.map f.toMonoidHom := by
    simp only [nConj,rightConjugate,comap_equiv_eq_map_symm']; rfl
  simp only [hr]
  rw [←map_zeta,←map_inf _ _ _ f.injective]
  exact congrArg (Subgroup.map f.toMonoidHom)
    (source_perpendicular_inf_radical_center Q split n hn m ν T hC μ hB hm hcore hc)

include ν hC μ hB hn in
/-- The fixed part of the radical center is precisely the perpendicular Omega, at every N-conjugate. -/
theorem source_ten_three_suzuki_fixed_center
    (hc : centralizer (pCore 2 (Endpoint Q 1) : Set (Endpoint Q 1)) ≤ pCore 2 (Endpoint Q 1))
    (hm : rotationOrder Q = 8) (hcore : Q.tits.B.normalCore = ⊥) (w : Q.tits.N) :
    zeta (nConj (simpleRemainder Q split 1) w) ⊓
        centralizer (nConj (rankOne Q split 1) w : Set (X ⧸ Q.D)) =
      nConj (omega (Uat Q split 1 (Q.simple 0*Q.simple 1*Q.simple 0))) w := by
  let f := (MulAut.conj (w : X ⧸ Q.D)).symm
  have hr (A : Subgroup (X ⧸ Q.D)) : nConj A w = A.map f.toMonoidHom := by
    simp only [nConj,rightConjugate,comap_equiv_eq_map_symm']; rfl
  simp only [hr]
  rw [←map_zeta,map_inf_centralizer_of_injective f.toMonoidHom f.injective]
  exact congrArg (Subgroup.map f.toMonoidHom)
    (source_suzuki_fixed_radical_center Q split n hn m ν T hC μ hB hm hcore hc)

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
