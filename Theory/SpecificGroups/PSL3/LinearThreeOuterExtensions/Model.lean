module

public import Theory.SpecificGroups.PSL3.ExtensionBorel
public import Theory.SpecificGroups.PSL3.OuterSolvable.StandardQuotient
public import Mathlib.GroupTheory.SemidirectProduct

/-!
# A faithful projective semilinear model in degree three

The linear factor is the actual image of GL₃ acting on PSL₃, already
identified with PGL₃ by `pglEquivInnerDiagonal`. Coefficient automorphisms
act on this image by conjugation. The resulting semidirect product acts
faithfully: an identity actor has trivial field part, and its GL₃ matrix
is scalar. Its image is exactly the existing `linearField` subgroup.

The coefficient projection and its exact kernel are consequently available
without choosing matrix representatives. Over a field of order two every
unit and field automorphism is trivial, so the entire linear-field group
is inner. Identifying this subgroup with the geometric diagram kernel is
an additional obligation, not built into the definition of this model.

Source: GLS3, Theorem 2.5.12 and §2.7; Aschbacher–Smith F.1.12,
printed pp.263–264 (PDF pp.274–275 of `refs/quasithin.pdf`).
-/

@[expose] public section
open scoped MatrixGroups
open Matrix Matrix.PSL3.OuterSolvable Matrix.PSL3.ExtensionBorel
namespace Matrix.PSL3.LinearThree.OuterExtensions
variable (F : Type*) [Field F]

/-- The exact kernel of a linear-field expression on PSL₃ in characteristic two. -/
theorem linear_field_eq_one_iff [CharP F 2] (g : GL (Fin 3) F) (σ : F ≃+* F) :
    linearConj F g * fieldAction F σ = 1 ↔
      σ = 1 ∧ g ∈ Subgroup.center (GL (Fin 3) F) := by
  constructor
  · intro h
    have hs : σ = 1 := by
      simpa using CartanActions.ResidualLinear.coefficient_pow_eq_one g σ (j := 1)
        (by simpa using h)
    refine ⟨hs, ?_⟩
    have hg : g ∈ (linearConj F).ker := by simpa [hs] using h
    rwa [linearConj_ker] at hg
  · rintro ⟨rfl, hg⟩
    have hk : g ∈ (linearConj F).ker := by rwa [linearConj_ker]
    simpa using hk

/-- Coefficients conjugate the actual PGL image in the automorphism group. -/
def coefficientAction : (F ≃+* F) →* MulAut (innerDiagonal F) :=
  (innerDiagonal F).normalizerMonoidHom.comp
    ((fieldAction F).codRestrict (Subgroup.normalizer (innerDiagonal F : Set _))
      (fun σ => fieldAction_mem_normalizer_innerDiagonal σ))

/-- The semilinear group with its linear factor already divided by scalars. -/
abbrev Semilinear := (innerDiagonal F) ⋊[coefficientAction F] (F ≃+* F)

/-- The actual action on PSL₃, with no additional tagged automorphisms. -/
def semilinearAction : Semilinear F →* MulAut PSL(3,F) :=
  SemidirectProduct.lift (innerDiagonal F).subtype (fieldAction F) (by
    intro σ
    ext a
    rfl)

theorem semilinearAction_apply (x : Semilinear F) :
    semilinearAction F x = x.left.val * fieldAction F x.right := rfl

/-- The scalar and field kernel calculation makes the projective action faithful. -/
theorem semilinearAction_injective [CharP F 2] :
    Function.Injective (semilinearAction F) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  apply (semilinearAction F).ker.eq_bot_iff_forall.mpr
  intro x hx
  obtain ⟨g, hg⟩ := x.left.property
  have he : linearConj F g * fieldAction F x.right = 1 := by
    rw [hg]
    exact hx
  obtain ⟨hσ, hscalar⟩ := (linear_field_eq_one_iff F g x.right).mp he
  apply SemidirectProduct.ext
  · apply Subtype.ext
    change x.left.val = 1
    rw [← hg]
    exact show g ∈ (linearConj F).ker from (linearConj_ker F).symm ▸ hscalar
  · exact hσ

theorem semilinearAction_range : (semilinearAction F).range = linearField F := by
  apply le_antisymm
  · rintro a ⟨x, rfl⟩
    exact (linearField F).mul_mem (Subgroup.mem_sup_left x.left.property)
      (Subgroup.mem_sup_right ⟨x.right, rfl⟩)
  · intro a ha
    obtain ⟨g, σ, rfl⟩ := linearField_factorization F a ha
    exact ⟨⟨⟨linearConj F g, ⟨g, rfl⟩⟩, σ⟩, rfl⟩

/-- A faithful realization of the projective semilinear group, on the whole group. -/
noncomputable def semilinearEquiv [CharP F 2] : Semilinear F ≃* linearField F :=
  (MonoidHom.ofInjective (semilinearAction_injective F)).trans
    (MulEquiv.subgroupCongr (semilinearAction_range F))

theorem semilinearEquiv_apply [CharP F 2] (x : Semilinear F) :
    (semilinearEquiv F x).val = x.left.val * fieldAction F x.right := rfl

/-- The coefficient projection, recovered from the faithful semilinear realization. -/
noncomputable def coefficient [CharP F 2] : linearField F →* (F ≃+* F) :=
  SemidirectProduct.rightHom.comp (semilinearEquiv F).symm.toMonoidHom

theorem coefficient_semilinearEquiv [CharP F 2] (x : Semilinear F) :
    coefficient F (semilinearEquiv F x) = x.right := by
  change ((semilinearEquiv F).symm (semilinearEquiv F x)).right = x.right
  rw [MulEquiv.symm_apply_apply]

/-- An actor has no coefficient part exactly when it is inner-diagonal. -/
theorem coefficient_ker [CharP F 2] :
    (coefficient F).ker = (innerDiagonal F).subgroupOf (linearField F) := by
  ext a
  obtain ⟨x, rfl⟩ := (semilinearEquiv F).surjective a
  change coefficient F (semilinearEquiv F x) = 1 ↔ (semilinearEquiv F x).val ∈ innerDiagonal F
  rw [coefficient_semilinearEquiv, semilinearEquiv_apply]
  constructor
  · intro hx
    simp [hx]
  · intro hx
    obtain ⟨g, hg⟩ := x.left.property
    obtain ⟨h, hh⟩ := hx
    have he : linearConj F (h⁻¹ * g) * fieldAction F x.right = 1 := by
      rw [map_mul, map_inv, hg]
      rw [mul_assoc, ← hh, inv_mul_cancel]
    exact ((linear_field_eq_one_iff F _ _).mp he).1

private theorem unit_eq_one_of_card_two (hF : Nat.card F = 2) (a : Fˣ) : a = 1 := by
  have h : Nat.card Fˣ = 1 := by rw [Nat.card_units, hF]
  let : Subsingleton Fˣ := (Nat.card_eq_one_iff_unique.mp h).1
  exact Subsingleton.elim _ _

theorem field_eq_one_of_card_two (hF : Nat.card F = 2) (σ : F ≃+* F) : σ = 1 := by
  ext x
  by_cases hx : x = 0
  · simp [hx]
  · have he : x = 1 := congrArg Units.val
      (unit_eq_one_of_card_two F hF (Units.mk0 x hx))
    simp [he]

theorem linearField_eq_inner_of_card_two (hF : Nat.card F = 2) :
    linearField F = MulAut.innerSubgroup PSL(3,F) := by
  apply le_antisymm
  · intro a ha
    obtain ⟨g, σ, rfl⟩ := linearField_factorization F a ha
    rw [field_eq_one_of_card_two F hF σ, map_one, mul_one]
    have hd : GeneralLinearGroup.det g = 1 := unit_eq_one_of_card_two F hF _
    let x : SL(3,F) := ⟨g.val, congrArg Units.val hd⟩
    have hx : SpecialLinearGroup.toGL x = g := Units.ext rfl
    rw [← hx, linearConj_toGL]
    exact ⟨_, rfl⟩
  · exact (inner_le_innerDiagonal F).trans le_sup_left

/-- Every intermediate actual linear-field extension collapses in the binary case. -/
theorem extension_eq_inner_of_card_two (hF : Nat.card F = 2)
    (E : Subgroup (MulAut PSL(3,F))) (hinner : MulAut.innerSubgroup PSL(3,F) ≤ E)
    (hE : E ≤ linearField F) : E = MulAut.innerSubgroup PSL(3,F) := by
  exact le_antisymm (hE.trans_eq (linearField_eq_inner_of_card_two F hF)) hinner

end Matrix.PSL3.LinearThree.OuterExtensions
