module

public import CFSG.Quasithin.ChapterA.Section03.RankThreeLocal
public import Theory.SpecificGroups.SU3.InnerInvolutionThreeRank.FormTransport
public import Theory.SpecificGroups.OddThreeRank
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.Models

/-!
# Prime-field special ternary carrier transport

A finite field of prime order is the prime field. In the unitary case,
an orthonormal Hermitian basis and coefficient-field transport preserve
both the unitary equation and determinant one. The resulting equivalence
is for the genuine special group, without a projective or covering shortcut.

Source: Aschbacher--Smith A.3.21, printed pp.55--56.
-/

public noncomputable section
open Subgroup Matrix BenderSuzuki.MatrixGroups
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings
open Chapter1.Section02.LocalModels
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree

private def restrict_model {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (U : Subgroup G) (V : Subgroup H)
    (h : ∀ x, e x ∈ V ↔ x ∈ U) : U ≃* V where
  toFun x := ⟨e x,(h x).2 x.property⟩
  invFun x := ⟨e.symm x,(h _).1 (by simp)⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x)
  right_inv x := Subtype.ext (e.apply_symm_apply x)
  map_mul' x y := Subtype.ext (e.map_mul x y)

private theorem su_equiv_standard {q : ℕ} [Fact q.Prime]
    (E : Type*) [Field E] [Finite E] (J : HermitianForm 3 E)
    (hcard : Nat.card E = q^2) (hc : ∀ x,J.conj x=x^q) :
    Nonempty (J.specialSubgroup ≃* RankThreeSU q) := by
  let : Fintype E := Fintype.ofFinite E
  let : CharP E q := charP_of_card_eq_prime_pow (by simpa only [Nat.card_eq_fintype_card] using hcard)
  obtain ⟨C,hC⟩ := J.exists_orthonormal_basis_of_prime_frobenius hc hcard
  let F := GaloisField q (2*1)
  let : Fintype F := Fintype.ofFinite F
  let e : E ≃+* F := FiniteField.ringEquivOfCardEq (by
    rw [←Nat.card_eq_fintype_card,←Nat.card_eq_fintype_card,hcard]
    exact (GaloisField.card q (2*1) (by decide)).symm)
  let K := ABG.unitaryForm 3 q 1 (by decide)
  have hK (x : F) : K.conj x = x^q := by
    simp only [K,ABG.unitaryForm,iterateFrobeniusEquiv_def,pow_one]
  let b := (restrict_model (MulAut.conj C)
    (identityForm (n := 3) J.conj J.conj_involutive).specialSubgroup J.specialSubgroup
    (fun B => special_conjugate_iff J C B hC)).symm
  have hc' (x : E) : e (J.conj x) = K.conj (e x) := by rw [hc,hK,map_pow]
  let ec : GL (Fin 3) E ≃* GL (Fin 3) F :=
    { Matrix.GeneralLinearGroup.map e.toRingHom with
      invFun := Matrix.GeneralLinearGroup.map e.symm.toRingHom
      left_inv := by intro g; ext i j; exact e.symm_apply_apply (g i j)
      right_inv := by intro g; ext i j; exact e.apply_symm_apply (g i j) }
  have ht (x : GL (Fin 3) E) : ec x ∈ K.specialSubgroup ↔
      x ∈ (identityForm (n := 3) J.conj J.conj_involutive).specialSubgroup := by
    rw [HermitianForm.mem_specialSubgroup_iff,HermitianForm.mem_specialSubgroup_iff]
    have hadj : K.conjTranspose (ec x).val =
        ((identityForm (n := 3) J.conj J.conj_involutive).conjTranspose x.val).map e := by
      ext i j
      exact (hc' (x.val j i)).symm
    have hu : K.conjTranspose (ec x).val * K.form * (ec x).val = K.form ↔
        (identityForm (n := 3) J.conj J.conj_involutive).conjTranspose x.val *
          (identityForm (n := 3) J.conj J.conj_involutive).form * x.val =
            (identityForm (n := 3) J.conj J.conj_involutive).form := by
      change _ * 1 * _ = 1 ↔ _ * 1 * _ = 1
      rw [hadj]
      simp only [mul_one]
      change _ * x.val.map e = 1 ↔ _
      rw [←Matrix.map_mul]
      constructor
      · intro hh
        ext i j
        apply e.injective
        simpa only [Matrix.map_apply,Matrix.one_apply,apply_ite,map_one,map_zero] using
          congrArg (fun A => A i j) hh
      · intro hh
        rw [hh]
        exact Matrix.map_one e (map_zero e) (map_one e)
    rw [hu]
    apply and_congr_right
    intro _
    change GeneralLinearGroup.det (GeneralLinearGroup.map e.toRingHom x) = 1 ↔ _
    rw [GeneralLinearGroup.map_det]
    constructor
    · intro hh
      apply Units.ext
      apply e.injective
      simpa using congrArg Units.val hh
    · intro hh
      rw [hh,map_one]
  exact ⟨b.trans (restrict_model ec _ K.specialSubgroup ht)⟩

theorem special_odd_three_standard {G : Type*} [Group G]
    {q : ℕ} [Fact q.Prime] (unitary : Bool) (hm : IsSLSign G unitary 3 q) :
    (unitary = false ∧ Nonempty (G ≃* SL(3,ZMod q))) ∨
      (unitary = true ∧ Nonempty (G ≃* RankThreeSU q)) := by
  cases unitary
  · left
    refine ⟨rfl,?_⟩
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    let : Fintype F := Fintype.ofFinite F
    let a : F ≃+* ZMod q := FiniteField.ringEquivOfCardEq (by
      rw [←Nat.card_eq_fintype_card,hF,ZMod.card])
    let b : SL(3,F) ≃* SL(3,ZMod q) :=
      { Matrix.SpecialLinearGroup.map a.toRingHom with
        invFun := Matrix.SpecialLinearGroup.map a.symm.toRingHom
        left_inv := by intro g; ext i j; exact a.symm_apply_apply (g i j)
        right_inv := by intro g; ext i j; exact a.apply_symm_apply (g i j) }
    exact ⟨e.trans b⟩
  · right
    refine ⟨rfl,?_⟩
    obtain ⟨F,_,_,J,hF,hc,⟨e⟩⟩ := hm
    exact ⟨e.trans (su_equiv_standard F J hF hc).some⟩

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings
