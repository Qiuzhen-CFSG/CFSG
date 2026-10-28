module
public import Theory.GroupTheory.CubicOuterInvolutionExtension
public import Theory.SpecificGroups.SU3.OddPrimeGraphExtension.NormalForm
public import Theory.SpecificGroups.SU3.OddPrimeGraphExtension.Gram
public import Theory.SpecificGroups.SU3.Quasisimplicity
public import Theory.FieldTheory.QuadraticFrobeniusFixed.Transport

/-!
# The literal projective unitary graph involution in the original source group

The genuine semilinear coverage and cubic diagonal quotient align the
ambient action with the inner-and-entrywise involution subgroup. Pullback
produces an outside involution in the original group and proves generation
with its generalized Fitting subgroup. Fixed-field Gram similarity retains
that action on an identity-Gram model, where its special lift is exactly
inverse transpose.

Source: Aschbacher–Smith F.6.18(11), printed pp.309–310; GLS3 2.5.12 and 2.7.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Matrix BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterF.SourceAssembly
open HermitianForm.OddPrimeSylow.NormalizedOuter HermitianForm.OddPrimeGraphExtension
open Theory.SpecificGroups.SU3.UnitaryGraphGram
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree
variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F]
  [IsSimpleGroup (generalizedFitting G)]

/-- The proper simple unitary source component supplies an actual outside
graph involution, with its identity-Gram inverse-transpose lift. -/
theorem exists_projective_unitary_graph_involution
    (T : Sylow 2 G) (hgen : generalizedFitting G ⊔ (T : Subgroup G) = ⊤)
    (hproper : generalizedFitting G ≠ ⊤)
    (J : HermitianForm 3 F) {p : ℕ} (hp : p.Prime) (hp8 : p % 8 = 3)
    (hcard : Nat.card F = p ^ 2) (hc : ∀ x, J.conj x = x ^ p)
    (eK : generalizedFitting G ≃* ProjectiveSpecialUnitaryMatrixGroup J) :
    ∃ t : G, orderOf t = 2 ∧ t ∉ generalizedFitting G ∧
      generalizedFitting G ⊔ zpowers t = ⊤ ∧
      ∃ (J' : HermitianForm 3 F)
        (j : generalizedFitting G ≃* ProjectiveSpecialUnitaryMatrixGroup J')
        (graphLift : MulAut J'.specialSubgroup),
        J'.conj = J.conj ∧ J'.form = 1 ∧
        (∀ x : J'.specialSubgroup, (graphLift x).val.val = x.val.inv.transpose) ∧
        (∀ x : J'.specialSubgroup,
          j (MulAut.conjNormal t (j.symm (J'.specialToProjective x))) =
            J'.specialToProjective (graphLift x)) := by
  let : Fact p.Prime := ⟨hp⟩
  have hfixed : Nat.card {x : F // J.conj x = x} = p := by
    simpa only [pow_one] using FiniteField.card_fixed_of_quadratic_frobenius
      J.conj p 1 (by decide) (by simpa only [pow_one] using hcard)
      (by simpa only [pow_one] using hc)
  let J₀ := FormTransport.standardForm J
  obtain ⟨e₀⟩ := FormTransport.exists_projectiveEquiv J p hcard hfixed
  let e := eK.trans e₀
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J₀) :=
    Finite.of_surjective e e.surjective
  let : IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J₀) := e.symm.isSimpleGroup
  have hp3 : 2 < p := by omega
  let : Group.IsPerfect (ProjectiveSpecialUnitaryMatrixGroup J₀) :=
    J₀.projective_isPerfect_of_fixed_card hp3 hcard hfixed
  let : Group.IsPerfect (generalizedFitting G) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hz : center (generalizedFitting G) = ⊥ := by
    rcases (inferInstance : (center (generalizedFitting G)).Normal).eq_bot_or_eq_top with h | h
    · exact h
    · exact (Group.IsPerfect.not_isMulCommutative _ (center_eq_top_iff.mp h)).elim
  let γ := entrywiseProjectiveAut J₀ rfl
  have hγ : J₀.IsEntrywiseConjugation γ := entrywiseProjectiveAut_isEntrywiseConjugation J₀ rfl
  obtain ⟨t, ht2, htout, htgen, j₀, hj₀⟩ :=
    CubicOuterInvolutionExtension.exists_marked_involution (generalizedFitting G) hz rfl
      T hgen hproper e γ hγ.sq_eq_one J₀.unitaryOuterHom.range
      (unitary_outer_is_three J₀)
      (outer_normal_form J₀ rfl hp hp8 hcard hfixed γ hγ)
  obtain ⟨b, hb⟩ := identity_gram_entrywise J₀ rfl hp hp8 hcard hfixed γ hγ
  let I := identityForm (n := 3) J₀.conj J₀.conj_involutive
  let j := j₀.trans b
  let gl := HermitianForm.OddPrimeSylow.specialEntrywiseAut I hb
  refine ⟨t, ht2, htout, htgen, I, j, gl, rfl, rfl,
    entrywise_lift_inverse_transpose I rfl (MulAut.congr b γ) hb, ?_⟩
  intro x
  have hx := hj₀ (j.symm (I.specialToProjective x))
  change b (j₀ (MulAut.conjNormal t (j.symm (I.specialToProjective x)))) = _
  rw [hx]
  have hh := HermitianForm.OddPrimeSylow.specialEntrywiseAut_projective I hb x
  change I.specialToProjective (gl x) = b (γ (b.symm (I.specialToProjective x))) at hh
  simpa only [j, MulEquiv.symm_trans_apply, j₀.apply_symm_apply] using hh.symm

end CFSG.Quasithin.ChapterF.SourceAssembly
