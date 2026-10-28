module
public import CFSG.Quasithin.ChapterF.Section01.SourceDefs
public import Theory.Representation.RankOne.QuadraticRecognition.SourceTheorem
public import Theory.LinearAlgebra.Hermitian.FiniteFieldEquivalence
public import Theory.SpecificGroups.SU3.EvenProjectiveComparison
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support
public import BenderSuzuki.Converse.PSL2

/-!
# Binary representation models from the full local catalogue

Every retained rank-one quotient other than D₁₀ supplies a concrete binary
representation model. Linear fields and both special and projective unitary
forms are transported to the carrier universe by coefficient equivalences.
For the projective unitary case, the equivalence descends through the full
scalar center, including the smallest field.

This adapter preserves the full F.1.1 catalogue. Its consumers must exclude
D₁₀ mathematically; it is not silently removed from the source alternatives.
-/

public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups
open Representation.RankOne.QuadraticRecognition
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source
universe u

private def fieldTransport {F K : Type*} [Field F] [Field K]
    (e : F ≃+* K) {n : ℕ} (J : HermitianForm n F) : HermitianForm n K where
  conj := e.symm.trans (J.conj.trans e)
  conj_involutive := by
    intro x
    change e (J.conj (e.symm (e (J.conj (e.symm x))))) = x
    rw [e.symm_apply_apply,J.conj_involutive,e.apply_symm_apply]
  form := J.form.map e
  form_hermitian := by
    intro i j
    change e (J.conj (e.symm (e (J.form j i)))) = e (J.form i j)
    rw [e.symm_apply_apply,J.form_hermitian]
  form_nondegenerate := by
    change (e.toRingHom.mapMatrix J.form).det ≠ 0
    rw [←RingHom.map_det]
    exact fun he => J.form_nondegenerate (e.injective (he.trans e.map_zero.symm))

private theorem fieldTransport_conj {F K : Type*} [Field F] [Field K]
    (e : F ≃+* K) {n q : ℕ} (J : HermitianForm n F)
    (h : ∀ x, J.conj x = x^q) (x : K) :
    (fieldTransport e J).conj x = x^q := by
  change e (J.conj (e.symm x)) = x^q
  rw [h,map_pow,e.apply_symm_apply]

private def fieldTransportSpecial {F K : Type*} [Field F] [Field K]
    (e : F ≃+* K) {n : ℕ} (J : HermitianForm n F) :
    J.specialSubgroup ≃* (fieldTransport e J).specialSubgroup :=
  J.coefficientSpecialEquiv e (fieldTransport e J)
    (by intro x; change e (J.conj x) = e (J.conj (e.symm (e x))); rw [e.symm_apply_apply]) rfl

private def centerQuotientEquiv {X Y : Type*} [Group X] [Group Y]
    (e : X ≃* Y) : (X ⧸ center X) ≃* (Y ⧸ center Y) :=
  QuotientGroup.congr _ _ e (by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact (Subgroup.centerCongr e ⟨y,hy⟩).property
    · intro hx
      exact ⟨e.symm x,(Subgroup.centerCongr e.symm ⟨x,hx⟩).property,e.apply_symm_apply x⟩)

private def specialCenterQuotientEquiv {F : Type*} [Field F] [Finite F]
    (J : HermitianForm 3 F) {n : ℕ} (hn : 0 < n)
    (hcard : Nat.card F = (2^n)^2) (hconj : ∀ x, J.conj x=x^(2^n)) :
    (J.specialSubgroup ⧸ center J.specialSubgroup) ≃* ProjectiveSpecialUnitaryMatrixGroup J :=
  (QuotientGroup.quotientMulEquivOfEq
    (J.specialToProjective_ker_eq_center (HermitianForm.EvenProjectiveComparison.center_eq_bot J hn hcard hconj)).symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective J.specialToProjective J.specialToProjective_surjective)

/-- Every non-dihedral source row supplies the literal binary model witness. -/
theorem IsRankOneModel.binaryModel_of_not_dihedral {D : Type u} [Group D]
    (M : IsRankOneModel D) (hne : ¬ Nonempty (D ≃* DihedralGroup 5)) :
    Nonempty (BinaryRankOneModel D) := by
  cases M with
  | dihedral h => exact (hne h).elim
  | suzuki m h => exact ⟨.suzuki m h.some⟩
  | linear n hn h =>
    obtain ⟨F,_,_,hc,⟨e⟩⟩ := h
    let := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow
      (by simpa only [Nat.card_eq_fintype_card] using hc)
    let K := ULift.{u} F
    let f : F ≃+* K := ULift.ringEquiv.symm
    let e₀ : D ≃* SL(2,F) := e.trans (MulEquiv.ofBijective (BenderSuzuki.Converse.pi F)
      ⟨BenderSuzuki.Converse.pi_injective,BenderSuzuki.Converse.pi_surjective⟩).symm
    exact ⟨.sl2 K n hn ((Nat.card_congr f.toEquiv).symm.trans hc)
      (e₀.trans (Atlas.fieldEquivSL 2 f))⟩
  | special_unitary n hn h =>
    obtain ⟨F,_,_,J,hc,hj,⟨e⟩⟩ := h
    let K := ULift.{u} F
    let f : F ≃+* K := ULift.ringEquiv.symm
    exact ⟨.su3 K (fieldTransport f J) n hn ((Nat.card_congr f.toEquiv).symm.trans hc)
      (fieldTransport_conj f J hj) (e.trans (fieldTransportSpecial f J))⟩
  | projective_unitary n hn h =>
    obtain ⟨F,_,_,J,hc,hj,⟨e⟩⟩ := h
    let K := ULift.{u} F
    let f : F ≃+* K := ULift.ringEquiv.symm
    have hcK : Nat.card K = (2^n)^2 := (Nat.card_congr f.toEquiv).symm.trans hc
    have hjK := fieldTransport_conj f J hj
    let eq : ProjectiveSpecialUnitaryMatrixGroup J ≃*
        ProjectiveSpecialUnitaryMatrixGroup (fieldTransport f J) :=
      (specialCenterQuotientEquiv J hn hc hj).symm.trans
        ((centerQuotientEquiv (fieldTransportSpecial f J)).trans
          (specialCenterQuotientEquiv (fieldTransport f J) hn hcK hjK))
    exact ⟨.psu3 K (fieldTransport f J) n hn hcK hjK (e.trans eq)⟩

end CFSG.Quasithin.ChapterF.Source
