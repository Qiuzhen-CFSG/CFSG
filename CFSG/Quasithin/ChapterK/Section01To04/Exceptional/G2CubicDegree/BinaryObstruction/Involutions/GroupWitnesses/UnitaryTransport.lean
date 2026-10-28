module
public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.G2CubicDegree.BinaryObstruction.Involutions.GroupWitnesses.UnitaryMatrices
public import Theory.SpecificGroups.SU3.BinaryG2Comparison
public import Theory.SpecificGroups.SU3.InvolutionConjugateBounds.Inner.Conjugacy
public import Theory.SpecificGroups.SU3.OddInvolutionNormalization
public import Theory.SpecificGroups.SU3.PrimeOrderDivisibility

/-!
# Universal transport of the unitary inversion witnesses

Inner involution fusion transports the regular three-element and its full
order-nine centralizer. For an outer involution, the existing normalization
identifies the automorphism with entrywise conjugation on an antidiagonal
Hermitian model over the same field. The explicit seven-element is transported
back through that equivalence.

The exceptional comparison is the proved equivalence with the literal
commutator subgroup of the binary octonion automorphism group. Both conclusions
are unconditional group statements, with no representation hypothesis.

Source: Guralnick–Malle, *Classification of 2F-modules I*, Proposition 4.3,
manuscript pp.10–11. The inner fusion and outer normalization are imported from
the source-oriented SU₃ development, and the exceptional comparison from
`Theory.SpecificGroups.SU3.BinaryG2Comparison`.
-/

public noncomputable section
open Matrix BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterK.Exceptional.G2CubicDegree.BinaryObstruction
namespace Involutions
namespace GroupWitnesses
local notation "D" => commutator (Atlas.G2.Model (ZMod 2))

private theorem entrywise_inverts_seven (J : HermitianForm 3 F)
    (hc : J.conj = form.conj) (hJ : J.form = form.form)
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
    (ha : J.IsEntrywiseConjugation a) :
    ∃ s, orderOf s = 7 ∧ a s = s⁻¹ := by
  let x : J.specialSubgroup := ⟨seven.val, by
    rw [J.mem_specialSubgroup_iff]
    refine ⟨?_, seven.property.2⟩
    have hadj : J.conjTranspose M = form.conjTranspose M := by
      change ((M.map J.conj).transpose) = _
      rw [hc]
      rfl
    change J.conjTranspose M * J.form * M = J.form
    rw [hadj, hJ]
    exact M_preserves⟩
  have hxorder : orderOf x = 7 := by
    rw [← Subgroup.orderOf_coe]
    exact (Subgroup.orderOf_coe seven).trans seven_order
  refine ⟨J.specialToProjective x,
    (orderOf_injective J.specialToProjective
      (J.specialToProjective_injective_of_card_nine FiniteField.Nine.natCard) x).trans hxorder, ?_⟩
  obtain ⟨y, hy, hay⟩ := ha x
  have hyx : y = x⁻¹ := by
    apply Subtype.ext
    apply Units.ext
    change y.val.val = Mbar
    rw [hy]
    change M.map J.conj = Mbar
    rw [hc]
    rfl
  change a (J.specialToProjective x) = (J.specialToProjective x)⁻¹
  rw [hay, hyx, map_inv]

private theorem outer_inverts_seven
    [IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup form)]
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup form))
    (ha : a ^ 2 = 1) (houter : ¬ ∃ s, a = MulAut.conj s) :
    ∃ s, orderOf s = 7 ∧ a s = s⁻¹ := by
  have hfixed : Nat.card {x : F // form.conj x = x} = 3 := by
    rw [Nat.card_eq_fintype_card]
    decide
  obtain ⟨J₀, e, hconj, hform, hentry⟩ :=
    HermitianForm.OddInvolutionNormalization.normalized_outer form
      (by decide : Nat.Prime 3) (by decide : Odd 3)
      FiniteField.Nine.natCard hfixed a ha houter
  obtain ⟨s, hs, has⟩ := entrywise_inverts_seven J₀ hconj hform
    (MulAut.congr e a) hentry
  refine ⟨e.symm s, (e.symm.orderOf_eq s).trans hs, ?_⟩
  apply e.injective
  change e (a (e.symm s)) = s⁻¹ at has
  simpa only [map_inv, MulEquiv.apply_symm_apply] using has

private theorem centralizer_card_transport {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (x : G) :
    Nat.card (Subgroup.centralizer ({x} : Set G)) =
      Nat.card (Subgroup.centralizer ({e x} : Set H)) := by
  simpa only [MulAut.congr_conj, MulAut.fixedSubgroup_conj] using
    Nat.card_congr (MulAut.fixedSubgroupCongr e (MulAut.conj x)).toEquiv

private noncomputable def projectiveEquiv :
    ProjectiveSpecialUnitaryMatrixGroup form ≃* D :=
  form.projectiveEquivBinaryG2Derived FiniteField.Nine.natCard FiniteField.Nine.star_eq_cube

private noncomputable def specialEquiv : SU ≃* ProjectiveSpecialUnitaryMatrixGroup form :=
  form.specialProjectiveEquivOfCardNine FiniteField.Nine.natCard

/-- Every nonidentity inner involution inverts a three-element whose centralizer
in the literal derived group has order nine. -/
theorem inner_witness (t : D) (ht : t ≠ 1) (ht2 : t ^ 2 = 1) :
    ∃ x : D, (orderOf x = 3 ∧ Nat.card (Subgroup.centralizer ({x} : Set D)) = 9) ∧ t * x * t⁻¹ = x⁻¹ := by
  have hto : orderOf t = 2 := orderOf_eq_prime ht2 ht
  have hconj := HermitianForm.InvolutionConjugateBounds.Inner.projective_involutions_isConj
    form (by decide : Nat.Prime 3) (by decide : 3 ≠ 2)
    FiniteField.Nine.natCard FiniteField.Nine.star_eq_cube
    (specialEquiv involution) (projectiveEquiv.symm t)
    ((specialEquiv.orderOf_eq involution).trans involution_order)
    ((projectiveEquiv.symm.orderOf_eq t).trans hto)
  obtain ⟨g, hg⟩ := isConj_iff.mp hconj
  let e : SU ≃* D := specialEquiv.trans ((MulAut.conj g).trans projectiveEquiv)
  have het : e involution = t := by
    change projectiveEquiv (g * specialEquiv involution * g⁻¹) = t
    rw [hg, projectiveEquiv.apply_symm_apply]
  refine ⟨e regular, ⟨(e.orderOf_eq regular).trans regular_order,
    (centralizer_card_transport e regular).symm.trans regular_centralizer_card⟩, ?_⟩
  simpa only [map_mul, map_inv, het] using congrArg e involution_inverts_regular

/-- Every noninner involutory automorphism of the literal derived group inverts
an element of order seven. -/
theorem outer_witness (a : MulAut D) (ha : a ^ 2 = 1)
    (houter : ¬ ∃ g : D, a = MulAut.conj g) :
    ∃ x : D, orderOf x = 7 ∧ a x = x⁻¹ := by
  let : IsSimpleGroup D := Atlas.G2.isSimple_commutator_binary
  let : IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup form) :=
    projectiveEquiv.isSimpleGroup
  obtain ⟨s, hs, has⟩ := outer_inverts_seven (MulAut.congr projectiveEquiv.symm a)
    (by rw [← map_pow, ha, map_one])
    (fun h => houter ((MulAut.congr_inner_iff projectiveEquiv.symm a).mp h))
  refine ⟨projectiveEquiv s, (projectiveEquiv.orderOf_eq s).trans hs, ?_⟩
  change projectiveEquiv.symm (a (projectiveEquiv s)) = s⁻¹ at has
  simpa only [MulEquiv.apply_symm_apply, map_inv] using congrArg projectiveEquiv has

end GroupWitnesses
end Involutions
end CFSG.Quasithin.ChapterK.Exceptional.G2CubicDegree.BinaryObstruction
