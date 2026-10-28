module

public import Theory.SpecificGroups.SU3.OddPrimeInvolutionComponent
public import Theory.SpecificGroups.SL2.CubicCentralDerived

/-!
# The characteristic SL₂ block of an odd-prime PSU₃ involution centralizer

The determinant kernel is the full derived subgroup of GU₂, since its SU₂
is perfect. The actual cubic central projection is injective on that block.
Consequently the literal derived subgroup of the supplied PSU₃ involution
centralizer is SL₂(p), and its centralizer is exactly the center.

All coefficient fields, forms and the original involution are retained.
Source: Aschbacher--Smith 6.1.4, printed p.666.
-/

public noncomputable section
open Matrix Subgroup BenderSuzuki.MatrixGroups
open scoped MatrixGroups
namespace Matrix.SU3.TwoFiveSylow

private theorem prime_conj (n p : ℕ) [Fact p.Prime] (x : GaloisField p (2*1)) :
    (ABG.unitaryForm n p 1 one_ne_zero).conj x = x^p := by
  simp only [ABG.unitaryForm,iterateFrobeniusEquiv_def,pow_one]

private theorem gu2_commutator_equiv (p : ℕ) [Fact p.Prime] (ho : Odd p) (hp : 3 < p) :
    Nonempty (commutator (ABG.unitaryForm 2 p 1 one_ne_zero).unitarySubgroup ≃*
      SL(2,ZMod p)) := by
  let J := ABG.unitaryForm 2 p 1 one_ne_zero
  let D := J.unitaryDet.ker
  let e : D ≃* SL(2,ZMod p) := J.unitaryDetKernelEquiv.trans
    ((ABG.specialUnitaryTwo_equiv_sl2 p 1 ho (by decide)).trans
      (GorensteinWalter.sl2RingEquiv (GaloisField.equivZmodP p).toRingEquiv))
  let : Group.IsPerfect SL(2,ZMod p) := GorensteinWalter.sl2_isPerfect_of_card_gt_three
    (ZMod p) (by simpa only [Nat.card_zmod] using hp)
  let : Group.IsPerfect D := Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hd : commutator J.unitarySubgroup = D := by
    apply le_antisymm (Abelianization.commutator_subset_ker _)
    exact (commutator_eq_self (H := D)).ge.trans (commutator_mono le_top le_top)
  exact ⟨(MulEquiv.subgroupCongr hd).trans e⟩

/-- The actual characteristic derived block is SL₂(p), and a subgroup of
this involution centralizer centralizing the block lies in its center. -/
theorem involution_centralizer_commutator_structure
    (p : ℕ) [Fact p.Prime] (ho : Odd p) (hp : 3 < p)
    (E : Type*) [Field E] [Finite E] (J : HermitianForm 3 E)
    (hcard : Nat.card E = p^2) (hc : ∀ x, J.conj x=x^p)
    (t : ProjectiveSpecialUnitaryMatrixGroup J) (ht : orderOf t=2) :
    Nonempty (commutator (centralizer ({t} : Set (ProjectiveSpecialUnitaryMatrixGroup J))) ≃*
      SL(2,ZMod p)) ∧
      centralizer (commutator (centralizer ({t} : Set (ProjectiveSpecialUnitaryMatrixGroup J))) :
        Set (centralizer ({t} : Set (ProjectiveSpecialUnitaryMatrixGroup J)))) =
        center (centralizer ({t} : Set (ProjectiveSpecialUnitaryMatrixGroup J))) := by
  let J3 := ABG.unitaryForm 3 p 1 one_ne_zero
  let J2 := ABG.unitaryForm 2 p 1 one_ne_zero
  obtain ⟨et⟩ := InnerThreeRank.exists_projective_equiv_standard p E J hcard hc
  let q := J3.specialToProjective
  have hcube : ∀ x ∈ q.ker, x^3=1 := by
    intro x hx
    exact congrArg Subtype.val (J3.specialToProjective_ker_cube ⟨x,hx⟩)
  obtain ⟨z,hz,hzt⟩ := InnerThreeRank.exists_involution_lift_of_cube_kernel q
    J3.specialToProjective_surjective hcube (et t) ((et.orderOf_eq t).trans ht)
  let C := centralizer ({z} : Set J3.specialSubgroup)
  have hmap : C.map q = centralizer ({et t} : Set (ProjectiveSpecialUnitaryMatrixGroup J3)) := by
    rw [←hzt]
    exact InnerThreeRank.map_centralizer_of_central_cube_kernel q J3.specialToProjective_surjective
      J3.specialToProjective_ker_le_center hcube z (by simpa only [hz] using pow_orderOf_eq_one z)
  let ep := MulEquiv.subgroupCongr hmap
  let ct := InnerThreeRank.centralizerEquiv et t
  let f := ct.symm.toMonoidHom.comp (ep.toMonoidHom.comp (q.subgroupMap C))
  have hf : Function.Surjective f :=
    ct.symm.surjective.comp (ep.surjective.comp (q.subgroupMap_surjective C))
  have hker : f.ker ≤ center C := by
    intro x hx
    have hh : ep ((q.subgroupMap C) x) = 1 := ct.symm.injective
      ((MonoidHom.mem_ker.mp hx).trans ct.symm.map_one.symm)
    have hxq : (x : J3.specialSubgroup) ∈ q.ker :=
      congrArg Subtype.val (ep.injective (hh.trans ep.map_one.symm))
    apply mem_center_iff.mpr
    intro y
    exact Subtype.ext (mem_center_iff.mp (J3.specialToProjective_ker_le_center hxq) y)
  have hfcube : ∀ x ∈ f.ker, x^3=1 := by
    intro x hx
    have hh : ep ((q.subgroupMap C) x) = 1 := ct.symm.injective
      ((MonoidHom.mem_ker.mp hx).trans ct.symm.map_one.symm)
    apply Subtype.ext
    exact hcube x (congrArg Subtype.val (ep.injective (hh.trans ep.map_one.symm)))
  let ec : C ≃* J2.unitarySubgroup :=
    (involutionCentralizerEquiv (by omega : p ≠ 2)
      (GaloisField.card p (2*1) (by decide)) J3 J2 rfl rfl
      (prime_conj 3 p) (prime_conj 2 p) z hz).symm
  obtain ⟨eg⟩ := gu2_commutator_equiv p ho hp
  let ed : commutator C ≃* SL(2,ZMod p) := (InnerThreeRank.commutatorEquiv ec).trans eg
  exact SpecialLinearGroup.commutator_structure_of_cubic_central_matrix_surjection
    (J2.unitarySubgroup.subtype.comp ec.toMonoidHom)
    (J2.unitarySubgroup.subtype_injective.comp ec.injective) ed
    (by simpa only [Nat.card_zmod] using hp) f hf hker hfcube

end Matrix.SU3.TwoFiveSylow
