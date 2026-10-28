module

public import Theory.SpecificGroups.Suzuki.SchurEightCover.AtlasModel.Group
public import Theory.SpecificGroups.Suzuki.SchurEightCover.AtlasModel.BlockModel
public import Theory.SpecificGroups.Suzuki.SchurEightCover.AtlasModel.BlockComparison
public import Theory.SpecificGroups.Suzuki.SchurEightCover.AtlasModel.MatrixComparison
public import BenderSuzuki.MatrixGroups.Suzuki

/-!
# A concrete finite perfect central fourfold cover of native Sz(8)

The concrete finite group and its checked central Klein four subgroup are
constructed in `AtlasModel.Group`. The checked block action identifies their
quotient with the degree-65 block model, and the faithful matrix action and
generation proof identify that model with the entire `SuzukiMatrixGroup 1`.
Composing these marked isomorphisms with the original quotient map constructs
`cover`, whose kernel is exactly the constructed central four-group.

Both displayed generator images are retained. The earlier conditional
constructor `coverOfEquiv` remains available, but `cover` has no comparison
or group-order premise. This supplies the fourfold lower cover used in the
exceptional multiplier calculation; universality is a separate assertion.
Source: Aschbacher--Smith I.1.1 and I.1.3(5), printed p.407.
ATLAS numerical attribution and conventions: `AtlasModel/source/README.md`.
-/

@[expose] public section
namespace BenderSuzuki.MatrixGroups.SchurEightCover.AtlasModel

/-- Native covering map with the supplied matrix comparison explicitly retained. -/
noncomputable def coverOfEquiv (e : Quotient ≃* SuzukiMatrixGroup 1) :
    PerfectCentralCovering.Cover E (SuzukiMatrixGroup 1) where
  toMonoidHom := e.toMonoidHom.comp (QuotientGroup.mk' kernel)
  surjective := e.surjective.comp (QuotientGroup.mk'_surjective kernel)
  isPerfect := inferInstance
  ker_le_center := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
    exact kernel_le_center

/-- The original quotient convention, followed by the actual model comparison. -/
theorem coverOfEquiv_apply (e : Quotient ≃* SuzukiMatrixGroup 1) (x : E) :
    (coverOfEquiv e).toMonoidHom x = e (QuotientGroup.mk x) := rfl

theorem coverOfEquiv_kernel (e : Quotient ≃* SuzukiMatrixGroup 1) :
    (coverOfEquiv e).toMonoidHom.ker = kernel := by
  change (e.toMonoidHom.comp (QuotientGroup.mk' kernel)).ker = kernel
  rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']

theorem coverOfEquiv_kernel_card (e : Quotient ≃* SuzukiMatrixGroup 1) :
    Nat.card (coverOfEquiv e).toMonoidHom.ker = 4 := by
  rw [coverOfEquiv_kernel]
  exact kernel_card

/-- The actual central quotient is the native Suzuki matrix group Sz(8). -/
noncomputable def quotientEquiv : Quotient ≃* SuzukiMatrixGroup 1 :=
  BlockComparison.equiv.trans MatrixComparison.equiv

/-- The comparison on a quotient class is the checked block action followed
by the faithful matrix comparison. -/
theorem quotientEquiv_mk (x : E) :
    quotientEquiv (QuotientGroup.mk x) = MatrixComparison.equiv (BlockComparison.action x) := by
  change MatrixComparison.equiv (BlockComparison.equiv (QuotientGroup.mk x)) = _
  rw [BlockComparison.equiv_mk]

theorem quotientEquiv_generatorA :
    (quotientEquiv (QuotientGroup.mk generatorA)).val =
      MatrixComparison.glEquiv MatrixComparison.matrixA := by
  change (MatrixComparison.equiv
    (BlockComparison.equiv (QuotientGroup.mk generatorA))).val = _
  rw [BlockComparison.equiv_generatorA]
  exact MatrixComparison.equiv_generatorA

theorem quotientEquiv_generatorB :
    (quotientEquiv (QuotientGroup.mk generatorB)).val =
      MatrixComparison.glEquiv MatrixComparison.matrixB := by
  change (MatrixComparison.equiv
    (BlockComparison.equiv (QuotientGroup.mk generatorB))).val = _
  rw [BlockComparison.equiv_generatorB]
  exact MatrixComparison.equiv_generatorB

/-- The concrete finite perfect central fourfold cover of the native Sz(8). -/
noncomputable def cover : PerfectCentralCovering.Cover E (SuzukiMatrixGroup 1) :=
  coverOfEquiv quotientEquiv

/-- The projection uses the original central quotient map. -/
theorem cover_toMonoidHom :
    cover.toMonoidHom = quotientEquiv.toMonoidHom.comp (QuotientGroup.mk' kernel) := rfl

theorem cover_apply (x : E) :
    cover.toMonoidHom x = quotientEquiv (QuotientGroup.mk x) := rfl

/-- The same projection expressed through the literal block action. -/
theorem cover_apply_eq_matrix_action (x : E) :
    cover.toMonoidHom x = MatrixComparison.equiv (BlockComparison.action x) :=
  quotientEquiv_mk x

theorem cover_generatorA :
    (cover.toMonoidHom generatorA).val =
      MatrixComparison.glEquiv MatrixComparison.matrixA :=
  quotientEquiv_generatorA

theorem cover_generatorB :
    (cover.toMonoidHom generatorB).val =
      MatrixComparison.glEquiv MatrixComparison.matrixB :=
  quotientEquiv_generatorB

theorem cover_surjective : Function.Surjective cover.toMonoidHom := cover.surjective

theorem cover_ker_le_center : cover.toMonoidHom.ker ≤ Subgroup.center E :=
  cover.ker_le_center

/-- No additional elements enter the kernel on passing to the native model. -/
theorem cover_kernel : cover.toMonoidHom.ker = kernel := coverOfEquiv_kernel quotientEquiv

theorem cover_kernel_card : Nat.card cover.toMonoidHom.ker = 4 :=
  coverOfEquiv_kernel_card quotientEquiv

instance cover_kernel_isKleinFour : IsKleinFour cover.toMonoidHom.ker := by
  rw [cover_kernel]
  infer_instance

end BenderSuzuki.MatrixGroups.SchurEightCover.AtlasModel
