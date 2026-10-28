module

public import Theory.Mathieu.M22.ChapterHLocalClassification.HexadAction.Restriction
public import Theory.Mathieu.M22.ChapterHLocalClassification.HexadAction.InvariantForm.Symmetric

/-!
# The invariant alternating form of the native hexad action

The inherited octad four-space admits a nondegenerate alternating form
preserved by the literal six-coordinate symmetric action. The construction
normalizes the image of a five-cycle by Sylow conjugacy in GL₄(2), then
uses a bounded kernel-checked (2,5,6) matrix calculation. Generation by
a transposition and a five-cycle proves preservation by the full action.
Pullback along the actual change of basis retains the original coordinates
and the original six-point marking.

The native outer conjugation action and its inner alternating restriction
preserve the same named form. This supplies the invariant-form step of
Aschbacher--Smith H.14.3(3), printed p.397 (PDF p.408), following H.14.1(4).
The subsequent natural-module comparison remains a separate construction.
-/

public section
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry MathieuCode
open MathieuCode.Hexad.CocodeAction.SixPointModel
namespace Sporadic.Mathieu.M22ChapterH.Hexad.Action
noncomputable section

/-- A form for the actual action, with no additional representation premise. -/
theorem exists_invariantForm :
    ∃ B : LinearMap.BilinForm (ZMod 2) Space,
      B.IsAlt ∧ B.Nondegenerate ∧
      ∀ s v w, B (symmetricAction s v) (symmetricAction s w) = B v w := by
  let e : Fin 6 ≃ H := (Fintype.equivFinOfCardEq card_H).symm
  let m := BinaryLinear.OuterCyclic.matrixEquivLinear 4
  let f : Equiv.Perm (Fin 6) →* BinaryFourSymmetricForm.GL4 :=
    m.symm.toMonoidHom.comp (symmetricAction.comp e.permCongrHom.toMonoidHom)
  have hf : Function.Injective f :=
    m.symm.injective.comp (symmetricAction_injective.comp e.permCongrHom.injective)
  obtain ⟨B, hBa, hBn, hp⟩ := BinaryFourSymmetricForm.exists_matrix_form f hf
  refine ⟨B.toBilin', hBa, hBn, ?_⟩
  intro s v w
  obtain ⟨t, rfl⟩ := e.permCongrHom.surjective s
  have hact (v : Space) : symmetricAction (e.permCongrHom t) v =
      (f t).val.toLin' v := by
    have he := m.apply_symm_apply (symmetricAction (e.permCongrHom t))
    exact congrArg (fun g : Space ≃ₗ[ZMod 2] Space => g v) he.symm
  rw [hact, hact]
  have hh := congrArg (fun b : LinearMap.BilinForm (ZMod 2) Space => b v w)
    (Matrix.toBilin'_comp B (f t).val (f t).val)
  rw [hp t] at hh
  exact hh

/-- A nondegenerate alternating form in the original octad moment coordinates. -/
def invariantForm : LinearMap.BilinForm (ZMod 2) Space :=
  Classical.choose exists_invariantForm

theorem invariantForm_isAlt : invariantForm.IsAlt :=
  (Classical.choose_spec exists_invariantForm).1

theorem invariantForm_nondegenerate : invariantForm.Nondegenerate :=
  (Classical.choose_spec exists_invariantForm).2.1

/-- Preservation by S₆ with its original six-coordinate marking. -/
theorem invariantForm_symmetric (s : Equiv.Perm H) (v w : Space) :
    invariantForm (symmetricAction s v) (symmetricAction s w) = invariantForm v w :=
  (Classical.choose_spec exists_invariantForm).2.2 s v w

/-- Preservation by actual conjugation in the native outer hexad stabilizer. -/
theorem invariantForm_outer (g : Outer) (v w : Space) :
    invariantForm (outerLinearAction g v) (outerLinearAction g w) = invariantForm v w := by
  rw [← symmetricAction_coordinate]
  exact invariantForm_symmetric _ v w

/-- The inner alternating action preserves the same form and marking. -/
theorem invariantForm_alternating (g : alternatingGroup H) (v w : Space) :
    invariantForm (alternatingAction g v) (alternatingAction g w) = invariantForm v w := by
  rw [← symmetricAction_alternating]
  exact invariantForm_symmetric _ v w

/-- Preservation also holds before taking the native inner quotient. -/
theorem invariantForm_inner (g : Inner) (v w : Space) :
    invariantForm (innerLinearAction g v) (innerLinearAction g w) = invariantForm v w := by
  rw [← linearAction_compatible]
  exact invariantForm_outer _ v w

end
end Sporadic.Mathieu.M22ChapterH.Hexad.Action
