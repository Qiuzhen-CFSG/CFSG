module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldExclusion.Components.Identification.SimpleSection
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldExclusion.Components.Identification.OddModels.Reduction
public import Theory.SpecificGroups.PSL3.OddInvolutionFixed.ComponentExclusion
public import Theory.SpecificGroups.SU3.InnerInvolutionComponentExclusion


/-!
# Inner-involution exclusion for the odd three-dimensional models

An ordinary component is perfect. In PSL₃ over an odd prime field and in
PSU₃ over its quadratic extension, the full centralizer of an involution
is the image of its actual GL₂ or GU₂ covering centralizer through a kernel
of exponent three. The determinant-one involution in the degree-two block
is unique, and this uniqueness survives in the derived projective image.
Two distinct involutions in the actual PSL₃(2) therefore exclude such a
component.

The unitary calculation includes p = 3 and every nondegenerate Hermitian
form with the prescribed Frobenius conjugation. The final wrappers apply
the calculation to the transported ordinary component of `SimpleInput`,
so the parent odd-model sieve can use the outer-involution branch.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004, proof of
15.3.38, printed p.1137; Theorem C, p.33; A.3.21(a), p.55.
-/

public section

open Subgroup Theory.GroupTheory Matrix BenderSuzuki.MatrixGroups
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion.Identification

private theorem inner_order {G : Type*} [Group G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (t : G) (ht : orderOf (MulAut.conj t) = 2) :
    orderOf t = 2 := by
  have hc : center G = ⊥ := by
    rcases (inferInstance : (center G).Normal).eq_bot_or_eq_top with h | h
    · exact h
    · exact (hns (Group.isSolvable_of_comm (center_eq_top_iff.mp h).is_comm.comm)).elim
  exact (orderOf_injective MulAut.conj (MulAut.conj_injective_of_center_eq_bot hc) t).symm.trans ht

/-- An inner involution of an actual odd-prime PSL₃ model has no PSL₃(2) component. -/
theorem linear_inner_no_component {F : Type*} [Field F] [Finite F]
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hF : Nat.card F = p)
    [IsSimpleGroup PSL(3,F)] (hns : ¬ Group.IsSolvable PSL(3,F))
    (a : MulAut PSL(3,F)) (ha : orderOf a = 2)
    (hi : a ∈ MulAut.innerSubgroup PSL(3,F))
    (D : Subgroup a.fixedSubgroup) (hD : IsComponent a.fixedSubgroup D) :
    ¬ Nonempty (D ≃* PSL(3,ZMod 2)) := by
  rintro ⟨e⟩
  let : Fact p.Prime := ⟨hp⟩
  let : Fintype F := Fintype.ofFinite F
  let : CharP F p := charP_of_card_eq_prime_pow
    (f := 1) (by simpa only [pow_one, Nat.card_eq_fintype_card] using hF)
  have hp2 : p ≠ 2 := by
    have := Nat.odd_iff.mp ho
    omega
  have h2 : (2 : F) ≠ 0 := CharP.cast_ne_zero_of_ne_of_prime F Nat.prime_two hp2
  obtain ⟨t, rfl⟩ := hi
  have ht := inner_order hns t ha
  let : IsQuasisimple D := hD.2
  let c := MulEquiv.subgroupCongr (MulAut.fixedSubgroup_conj t)
  exact PSL3.OddInvolutionFixed.no_perfect_psl3_two_in_centralizer h2 t ht
    (c.toMonoidHom.comp D.subtype) (c.injective.comp D.subtype_injective) e

/-- This excludes all odd-prime PSU₃ models, including p = 3 and every
nondegenerate Hermitian form with the prescribed Frobenius conjugation. -/
theorem unitary_inner_no_component {E : Type*} [Field E] [Finite E]
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (J : HermitianForm 3 E)
    (hE : Nat.card E = p ^ 2) (hc : ∀ x, J.conj x = x ^ p)
    [IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J)]
    (hns : ¬ Group.IsSolvable (ProjectiveSpecialUnitaryMatrixGroup J))
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) (ha : orderOf a = 2)
    (hi : a ∈ MulAut.innerSubgroup (ProjectiveSpecialUnitaryMatrixGroup J))
    (D : Subgroup a.fixedSubgroup) (hD : IsComponent a.fixedSubgroup D) :
    ¬ Nonempty (D ≃* PSL(3,ZMod 2)) := by
  rintro ⟨e⟩
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨t, rfl⟩ := hi
  have ht := inner_order hns t ha
  let : IsQuasisimple D := hD.2
  let c := MulEquiv.subgroupCongr (MulAut.fixedSubgroup_conj t)
  exact SU3.InnerComponentExclusion.no_perfect_psl3_two_in_centralizer p ho E J hE hc t ht
    (c.toMonoidHom.comp D.subtype) (c.injective.comp D.subtype_injective) e

variable {S : Type*} [Group S] (s : SimpleInput S)

/-- The involution transported to an actual odd-prime linear-three model is outer. -/
theorem SimpleInput.linear_three_involution_not_inner
    {F : Type*} [Field F] [Finite F] {p : ℕ}
    (hp : p.Prime) (ho : Odd p) (hF : Nat.card F = p)
    (e : S ≃* PSL(3,F)) :
    MulAut.congr e s.involution ∉ MulAut.innerSubgroup PSL(3,F) := by
  intro hi
  let : IsSimpleGroup S := s.simple
  let : IsSimpleGroup PSL(3,F) := e.symm.isSimpleGroup
  obtain ⟨D, hD, he⟩ := s.exists_fixed_component_of_equiv e
  exact linear_inner_no_component hp ho hF (s.not_isSolvable_of_equiv e)
    (MulAut.congr e s.involution)
    (((MulAut.congr e).orderOf_eq s.involution).trans s.involution_order) hi D hD he

/-- The involution transported to an actual odd-prime unitary-three model is outer. -/
theorem SimpleInput.unitary_three_involution_not_inner
    {E : Type*} [Field E] [Finite E] {p : ℕ}
    (hp : p.Prime) (ho : Odd p) (J : HermitianForm 3 E)
    (hE : Nat.card E = p ^ 2) (hc : ∀ x, J.conj x = x ^ p)
    (e : S ≃* ProjectiveSpecialUnitaryMatrixGroup J) :
    MulAut.congr e s.involution ∉ MulAut.innerSubgroup (ProjectiveSpecialUnitaryMatrixGroup J) := by
  intro hi
  let : IsSimpleGroup S := s.simple
  let : IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J) := e.symm.isSimpleGroup
  obtain ⟨D, hD, he⟩ := s.exists_fixed_component_of_equiv e
  exact unitary_inner_no_component hp ho J hE hc (s.not_isSolvable_of_equiv e)
    (MulAut.congr e s.involution)
    (((MulAut.congr e).orderOf_eq s.involution).trans s.involution_order) hi D hD he
end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion.Identification
