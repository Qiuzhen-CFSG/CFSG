module

public import Theory.SpecificGroups.SU3.InnerInvolutionThreeRank.ScalarKernel
public import Theory.SpecificGroups.SU3.InvolutionConjugacy
public import Theory.SpecificGroups.SU3.UnitaryTwoResidual
public import ABG.ChapterII.Section2.SpecialUnitaryEquivSL2
public import Theory.SpecificGroups.SU3.InnerInvolutionThreeRank.FormTransport
public import Theory.GroupTheory.GeneralizedFitting.ComponentExclusion
public import GorensteinWalter.SL2ProjectiveCover

/-!
# The SL₂ component of an odd-prime PSU₃ involution centralizer

Lift the projective involution through the central scalar kernel of exponent
three. Its full SU₃ centralizer is GU₂, whose determinant kernel is genuinely
SU₂(p) ≃ SL₂(p). Projection is injective on this subgroup: a kernel element
is central in SL₂, hence has square one, and also has cube one. The normal
image is therefore still SL₂(p), and is a component when p > 3.

An orthonormal basis and the coefficient-field equivalence carry the result
to every allowed nondegenerate ternary Hermitian form. Normality is in the
full centralizer, with the literal SU₃ to PSU₃ projection retained.
Source: Aschbacher--Smith, A.3.21(a), printed p.55, and the proof of
1.1.5(3), printed p.503.
-/

public section

open Matrix Subgroup BenderSuzuki.MatrixGroups Theory.GroupTheory
open scoped MatrixGroups
namespace Matrix.SU3.OddPrimeComponent

private theorem central_sq_eq_one {F : Type*} [Field F] {g : SL(2,F)}
    (hg : g ∈ center SL(2,F)) : g ^ 2 = 1 := by
  obtain ⟨a, ha, h⟩ := SpecialLinearGroup.mem_center_iff.mp hg
  simp only [Fintype.card_fin] at ha
  have hcase : g = 1 ∨ g = -1 := by
    rcases sq_eq_one_iff.mp ha with rfl | rfl
    · left
      apply Subtype.ext
      simpa using h.symm
    · right
      apply Subtype.ext
      simpa [← Matrix.diagonal_neg] using h.symm
  rcases hcase with rfl | rfl <;> simp

private theorem injective_on_sl2 {G H F : Type*} [Group G] [Group H] [Field F]
    (f : G →* H) (hk : f.ker ≤ center G)
    (h3 : ∀ x ∈ f.ker, x ^ 3 = 1) (K : Subgroup G)
    (e : K ≃* SL(2,F)) : Function.Injective (f.subgroupMap K) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply eq_bot_iff.mpr
  intro x hx
  have hxk : (x : G) ∈ f.ker := by
    exact congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
  have hc : e x ∈ center SL(2,F) := by
    rw [mem_center_iff]
    intro y
    obtain ⟨y, rfl⟩ := e.surjective y
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mem_center_iff.mp (hk hxk) y)
  have hs := central_sq_eq_one hc
  have ht : e x ^ 3 = 1 := by
    rw [← map_pow]
    exact (congrArg e (show x ^ 3 = 1 from Subtype.ext (h3 x hxk))).trans (map_one e)
  rw [pow_succ, hs, one_mul] at ht
  exact (e.injective (ht.trans (map_one e).symm) : x = 1)

private theorem prime_conj (n p : ℕ) [Fact p.Prime]
    (x : GaloisField p (2 * 1)) :
    (ABG.unitaryForm n p 1 one_ne_zero).conj x = x ^ p := by
  simp only [ABG.unitaryForm, iterateFrobeniusEquiv_def, pow_one]

private theorem standard_centralizer_sl2 (p : ℕ) [Fact p.Prime] (ho : Odd p) (hp : 3 < p)
    (k : ProjectiveSpecialUnitaryMatrixGroup (ABG.unitaryForm 3 p 1 one_ne_zero))
    (hk : orderOf k = 2) :
    ∃ D : Subgroup (centralizer ({k} : Set
        (ProjectiveSpecialUnitaryMatrixGroup (ABG.unitaryForm 3 p 1 one_ne_zero)))),
      D.Normal ∧ Nonempty (D ≃* SL(2,ZMod p)) := by
  let J3 := ABG.unitaryForm 3 p 1 one_ne_zero
  let J2 := ABG.unitaryForm 2 p 1 one_ne_zero
  let q := J3.specialToProjective
  have hcube : ∀ x ∈ q.ker, x ^ 3 = 1 := by
    intro x hx
    exact congrArg Subtype.val (J3.specialToProjective_ker_cube ⟨x, hx⟩)
  obtain ⟨z, hz, rfl⟩ := InnerThreeRank.exists_involution_lift_of_cube_kernel q
    J3.specialToProjective_surjective hcube k hk
  let C := centralizer ({z} : Set J3.specialSubgroup)
  have hmap : C.map q = centralizer ({q z} : Set (ProjectiveSpecialUnitaryMatrixGroup J3)) :=
    InnerThreeRank.map_centralizer_of_central_cube_kernel q J3.specialToProjective_surjective
      J3.specialToProjective_ker_le_center hcube z (by simpa only [hz] using pow_orderOf_eq_one z)
  let ep := MulEquiv.subgroupCongr hmap
  let f := ep.toMonoidHom.comp (q.subgroupMap C)
  have hf : Function.Surjective f := ep.surjective.comp (q.subgroupMap_surjective C)
  have hker : f.ker ≤ center C := by
    intro x hx
    have hxq : (x : J3.specialSubgroup) ∈ q.ker :=
      congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
    rw [mem_center_iff]
    intro y
    exact Subtype.ext (mem_center_iff.mp (J3.specialToProjective_ker_le_center hxq) y)
  have hfcube : ∀ x ∈ f.ker, x ^ 3 = 1 := by
    intro x hx
    apply Subtype.ext
    exact hcube x (congrArg Subtype.val (MonoidHom.mem_ker.mp hx))
  let ec : C ≃* J2.unitarySubgroup :=
    (involutionCentralizerEquiv (by omega : p ≠ 2)
      (GaloisField.card p (2 * 1) (by decide))
      J3 J2 rfl rfl (prime_conj 3 p) (prime_conj 2 p) z hz).symm
  let e2 : J2.specialSubgroup ≃* SL(2,ZMod p) :=
    (ABG.specialUnitaryTwo_equiv_sl2 p 1 ho (by decide)).trans
      (GorensteinWalter.sl2RingEquiv (GaloisField.equivZmodP p).toRingEquiv)
  let K := J2.unitaryDet.ker.map ec.symm.toMonoidHom
  let eK : K ≃* SL(2,ZMod p) :=
    (ec.symm.subgroupMap J2.unitaryDet.ker).symm.trans
      (J2.unitaryDetKernelEquiv.trans e2)
  let : K.Normal := Subgroup.Normal.map inferInstance ec.symm.toMonoidHom ec.symm.surjective
  let eD : K ≃* K.map f :=
    MulEquiv.ofBijective (f.subgroupMap K)
      ⟨injective_on_sl2 f hker hfcube K eK, f.subgroupMap_surjective K⟩
  exact ⟨K.map f, Subgroup.Normal.map inferInstance f hf, ⟨eD.symm.trans eK⟩⟩

/-- The full involution centralizer in every allowed PSU₃(p) model has a
normal component isomorphic to the actual SL₂(p) matrix group, for p > 3. -/
theorem involution_centralizer_has_sl2_component (p : ℕ) [Fact p.Prime]
    (ho : Odd p) (hp : 3 < p) (E : Type*) [Field E] [Finite E]
    (J : HermitianForm 3 E) (hcard : Nat.card E = p ^ 2)
    (hc : ∀ x, J.conj x = x ^ p)
    (t : ProjectiveSpecialUnitaryMatrixGroup J) (ht : orderOf t = 2) :
    ∃ D : Subgroup (centralizer ({t} : Set (ProjectiveSpecialUnitaryMatrixGroup J))),
      D.Normal ∧ IsComponent _ D ∧ Nonempty (D ≃* SL(2,ZMod p)) := by
  let : IsQuasisimple SL(2,ZMod p) := {
    toIsPerfect := GorensteinWalter.sl2_isPerfect_of_card_gt_three (ZMod p)
      (by simpa only [Nat.card_zmod] using hp)
    simple := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by
      rw [Nat.card_zmod]
      omega) }
  obtain ⟨e⟩ := InnerThreeRank.exists_projective_equiv_standard p E J hcard hc
  obtain ⟨D, hD, ⟨eD⟩⟩ := standard_centralizer_sl2 p ho hp (e t)
    ((e.orderOf_eq t).trans ht)
  let c := InnerThreeRank.centralizerEquiv e t
  let ecD : D.map c.symm.toMonoidHom ≃* SL(2,ZMod p) :=
    (c.symm.subgroupMap D).symm.trans eD
  have hN : (D.map c.symm.toMonoidHom).Normal :=
    Subgroup.Normal.map hD c.symm.toMonoidHom c.symm.surjective
  exact ⟨D.map c.symm.toMonoidHom, hN,
    ⟨hN.isSubnormal, IsQuasisimple.of_mulEquiv ecD.symm⟩, ⟨ecD⟩⟩

end Matrix.SU3.OddPrimeComponent
