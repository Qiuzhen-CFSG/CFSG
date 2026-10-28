module

public import Theory.SpecificGroups.SU3.OddPrimeInvolutionComponent
public import Theory.GroupTheory.CubicCentralKernelSL2

/-!
# Odd-prime PSU₃ involution centralizers are not two-groups

Lift the original projective involution through its central cubic kernel.
The actual special-unitary centralizer is GU₂, whose determinant kernel is
SU₂(p) ≃ SL₂(p). This subgroup survives projective passage injectively, and
its odd root subgroup excludes a two-group centralizer, also for p=3.
Hermitian-form and coefficient-field equivalences retain the original
projective involution when transporting the standard calculation.

Source: Aschbacher--Smith A.3.21(a), printed p.55, and G.4.1, printed p.342.
-/

@[expose] public noncomputable section
set_option linter.style.haveILetI false
open Matrix Subgroup BenderSuzuki.MatrixGroups
open scoped MatrixGroups
namespace Matrix.SU3.OddPrimeComponent
open Theory.GroupTheory InnerThreeRank
private theorem prime_conj' (n p : ℕ) [Fact p.Prime]
    (x : GaloisField p (2 * 1)) :
    (ABG.unitaryForm n p 1 one_ne_zero).conj x = x ^ p := by
  simp only [ABG.unitaryForm, iterateFrobeniusEquiv_def, pow_one]

theorem standard_involution_centralizer_not_twoGroup (p : ℕ) [Fact p.Prime]
    (ho : Odd p)
    (k : ProjectiveSpecialUnitaryMatrixGroup (ABG.unitaryForm 3 p 1 one_ne_zero))
    (hk : orderOf k = 2) :
    ¬ IsPGroup 2 (centralizer ({k} : Set
      (ProjectiveSpecialUnitaryMatrixGroup (ABG.unitaryForm 3 p 1 one_ne_zero)))) := by
  let J3 := ABG.unitaryForm 3 p 1 one_ne_zero
  let J2 := ABG.unitaryForm 2 p 1 one_ne_zero
  let q := J3.specialToProjective
  have hcube : ∀ x ∈ q.ker, x ^ 3 = 1 := by
    intro x hx
    exact congrArg Subtype.val (J3.specialToProjective_ker_cube ⟨x,hx⟩)
  obtain ⟨z,hz,rfl⟩ := exists_involution_lift_of_cube_kernel q
    J3.specialToProjective_surjective hcube k hk
  let C := centralizer ({z} : Set J3.specialSubgroup)
  let f : C →* centralizer ({q z} : Set (ProjectiveSpecialUnitaryMatrixGroup J3)) :=
    (q.comp C.subtype).codRestrict _ (fun x => by
      apply mem_centralizer_singleton_iff.mpr
      simpa only [map_mul, MonoidHom.comp_apply, Subgroup.subtype_apply] using
        congrArg q (mem_centralizer_singleton_iff.mp x.property))
  have hker : f.ker ≤ center C := by
    intro x hx
    have hxq : (x : J3.specialSubgroup) ∈ q.ker :=
      congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
    rw [mem_center_iff]
    intro y
    exact Subtype.ext (mem_center_iff.mp (J3.specialToProjective_ker_le_center hxq) y)
  have hfcube : ∀ x ∈ f.ker, x ^ 3 = 1 := by
    intro x hx
    exact Subtype.ext (hcube x (congrArg Subtype.val (MonoidHom.mem_ker.mp hx)))
  let ec : C ≃* J2.unitarySubgroup :=
    (involutionCentralizerEquiv (by obtain ⟨r,hr⟩ := ho; omega)
      (GaloisField.card p (2 * 1) (by decide))
      J3 J2 rfl rfl (prime_conj' 3 p) (prime_conj' 2 p) z hz).symm
  let e2 : J2.specialSubgroup ≃* SL(2,ZMod p) :=
    (ABG.specialUnitaryTwo_equiv_sl2 p 1 ho (by decide)).trans
      (GorensteinWalter.sl2RingEquiv (GaloisField.equivZmodP p).toRingEquiv)
  let K := J2.unitaryDet.ker.map ec.symm.toMonoidHom
  let eK : K ≃* SL(2,ZMod p) :=
    (ec.symm.subgroupMap J2.unitaryDet.ker).symm.trans
      (J2.unitaryDetKernelEquiv.trans e2)
  let j := ((K.map f).subtype.comp (f.subgroupMap K)).comp eK.symm.toMonoidHom
  have hj : Function.Injective j := Subtype.val_injective.comp
    ((injective_sl2_of_cubic_central_kernel f hker hfcube K eK).comp eK.symm.injective)
  exact not_twoGroup_of_sl2_odd_embedding (by simpa only [Nat.card_zmod] using ho) j hj

theorem involution_centralizer_not_twoGroup (p : ℕ) [Fact p.Prime]
    (ho : Odd p) (E : Type*) [Field E] [Finite E]
    (J : HermitianForm 3 E) (hcard : Nat.card E = p ^ 2)
    (hc : ∀ x, J.conj x = x ^ p)
    (t : ProjectiveSpecialUnitaryMatrixGroup J) (ht : orderOf t = 2) :
    ¬ IsPGroup 2 (centralizer ({t} : Set (ProjectiveSpecialUnitaryMatrixGroup J))) := by
  obtain ⟨e⟩ := exists_projective_equiv_standard p E J hcard hc
  intro hp
  exact standard_involution_centralizer_not_twoGroup p ho (e t) ((e.orderOf_eq t).trans ht)
    (hp.of_equiv (centralizerEquiv e t))
end Matrix.SU3.OddPrimeComponent
