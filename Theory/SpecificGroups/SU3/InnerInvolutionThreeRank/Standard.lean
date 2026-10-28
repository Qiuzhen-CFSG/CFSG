module

public import Theory.SpecificGroups.SU3.InnerInvolutionThreeRank.ScalarKernel
public import Theory.SpecificGroups.SU3.InnerInvolutionThreeRank.LinearRank
public import Theory.SpecificGroups.SU3.InvolutionConjugacy
public import Theory.SpecificGroups.SU3.UnitaryTwoResidual
public import ABG.ChapterII.Section2.SpecialUnitaryEquivSL2

/-!
# The derived three-rank of standard PSU₃ involution centralizers

Lift a projective involution to SU₃ through the central scalar kernel of
exponent three. The full SU₃ centralizer surjects onto the projective
centralizer and is genuinely GU₂(p). Its first commutator embeds in the
determinant kernel SU₂(p), identified with SL₂(ZMod p) by the proved
change-of-form equivalence. Cyclic Sylow three-subgroups of SL₂ bound the
rank of every image of this commutator, including when p = 3.

No assertion of perfectness, or identification of the first commutator
with the terminal derived subgroup or prime-to-p residual, is used.
Source: Aschbacher–Smith A.3.21(a), printed p.55, and E.6.18, printed p.252.
-/

public section

open Matrix Subgroup BenderSuzuki.MatrixGroups
namespace Matrix.SU3.InnerThreeRank

private theorem prime_conj (n p : ℕ) [Fact p.Prime]
    (x : GaloisField p (2 * 1)) :
    (ABG.unitaryForm n p 1 one_ne_zero).conj x = x ^ p := by
  simp only [ABG.unitaryForm, iterateFrobeniusEquiv_def, pow_one]

/-- Every involution in the standard concrete PSU₃(p) has derived centralizer three-rank at most one. -/
theorem standard_projective_centralizer_rank (p : ℕ) [Fact p.Prime] (hp : Odd p)
    (k : ProjectiveSpecialUnitaryMatrixGroup (ABG.unitaryForm 3 p 1 one_ne_zero))
    (hk : orderOf k = 2) :
    primeRank 3 (commutator (centralizer ({k} : Set
      (ProjectiveSpecialUnitaryMatrixGroup (ABG.unitaryForm 3 p 1 one_ne_zero))))) ≤ 1 := by
  let J3 := ABG.unitaryForm 3 p 1 one_ne_zero
  let J2 := ABG.unitaryForm 2 p 1 one_ne_zero
  let q := J3.specialToProjective
  have hcube : ∀ x ∈ q.ker, x ^ 3 = 1 := by
    intro x hx
    exact congrArg Subtype.val (J3.specialToProjective_ker_cube ⟨x, hx⟩)
  obtain ⟨z, hz, rfl⟩ := exists_involution_lift_of_cube_kernel q
    J3.specialToProjective_surjective hcube k hk
  let C := centralizer ({z} : Set J3.specialSubgroup)
  have hmap : C.map q = centralizer ({q z} : Set (ProjectiveSpecialUnitaryMatrixGroup J3)) :=
    map_centralizer_of_central_cube_kernel q J3.specialToProjective_surjective
      J3.specialToProjective_ker_le_center hcube z (by simpa only [hz] using pow_orderOf_eq_one z)
  let ep := MulEquiv.subgroupCongr hmap
  let f := ep.toMonoidHom.comp (q.subgroupMap C)
  have hf : Function.Surjective f := ep.surjective.comp (q.subgroupMap_surjective C)
  have hp2 : p ≠ 2 := by intro h; subst p; norm_num at hp
  let ec : C ≃* J2.unitarySubgroup :=
    (involutionCentralizerEquiv hp2 (GaloisField.card p (2 * 1) (by decide))
      J3 J2 rfl rfl (prime_conj 3 p) (prime_conj 2 p) z hz).symm
  let e2 : J2.specialSubgroup ≃* SpecialLinearGroup (Fin 2) (ZMod p) :=
    (ABG.specialUnitaryTwo_equiv_sl2 p 1 hp (by decide)).trans
      (GorensteinWalter.sl2RingEquiv (GaloisField.equivZmodP p).toRingEquiv)
  let j0 : commutator C →* J2.unitaryDet.ker :=
    (ec.toMonoidHom.comp (commutator C).subtype).codRestrict _ (by
      intro x
      exact Abelianization.commutator_subset_ker
        (J2.unitaryDet.comp ec.toMonoidHom) x.property)
  let j := e2.toMonoidHom.comp (J2.unitaryDetKernelEquiv.toMonoidHom.comp j0)
  have hj : Function.Injective j := by
    intro x y h
    apply Subtype.ext
    apply ec.injective
    have hh := e2.injective h
    exact congrArg Subtype.val (J2.unitaryDetKernelEquiv.injective hh)
  exact derived_rank_of_surjective_and_sl2_embedding p hp f hf j hj

end Matrix.SU3.InnerThreeRank
