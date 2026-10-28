module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.AmbientOrder.FixedImage.Configuration

/-!
# Certified coordinates of the small seed-fixed configuration

The eleven candidate columns are evaluated from the literal seed matrix using
its existing word certificate. Eleven displayed covectors form a left inverse.
Kernel-checked binary arithmetic certifies both identities; linearity then proves
that `codeLift` is injective. This is an actual embedding in the original column
representation, not a group-family identification.

The certificate uses `KernelCount.Relations.representation_seed` and the matrix
provenance documented in `Cardinality.Subgroup`. It asserts neither invariance
under the full centralizer nor faithfulness of the action on this subspace.
-/

@[expose] public section
open scoped Matrix
namespace Janko4.LocalStructure.MathieuSeedCentralizer.AmbientOrder.FixedImage
open GeneratorCertificates Cardinality.KernelCount

private def codeColumns : Vector ℕ 11 := #v[
  13987318277763475446445011774760,
  3824936879284296410835240842414898,
  2143760286298637224498797409938018,
  265702484200699489057791992508183,
  840874172327147788615751336123333,
  22747109678171165895042454972844,
  411407035063847566061205841844735,
  16432662096988255177862472932341,
  68639460558714787205367367079379,
  161540515394325583655745274327680,
  7891599426060375840933163851152]

private theorem seed_matrix : toMatrix seed = decodeRows e0Rows :=
  Relations.representation_seed matrixA_mul_self matrixB_pow_four

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
private theorem codeColumns_checked : ∀ i : Fin 11,
    (decodeRows e0Rows) *ᵥ binaryColumn 112 (codePreimages.get i) -
      binaryColumn 112 (codePreimages.get i) = binaryColumn 112 (codeColumns.get i) := by
  decide +kernel

private theorem codeBasis_coordinates (i : Fin 11) :
    (codeBasis i : NaturalModule) = binaryColumn 112 (codeColumns.get i) := by
  change displacement _ = _
  rw [displacement_apply, seed_matrix]
  exact codeColumns_checked i

/-- Covectors giving a left inverse to the displayed column family. -/
def codeDecodeRows : Vector ℕ 11 := #v[
  4539,
  4597,
  5296,
  5361,
  43,
  4224,
  307,
  1389,
  4229,
  5439,
  4559]

/-- The coordinate recovery map on the full seed fixed space. -/
def codeDecode : fixedVectors →ₗ[ZMod 2] CodeModule where
  toFun v i := binaryColumn 112 (codeDecodeRows.get i) ⬝ᵥ (v : NaturalModule)
  map_add' v w := by
    funext i
    exact dotProduct_add _ _ _
  map_smul' r v := by
    funext i
    exact dotProduct_smul _ _ _

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
private theorem codeDecode_checked : ∀ i : Fin 11,
    (fun j => binaryColumn 112 (codeDecodeRows.get j) ⬝ᵥ
      binaryColumn 112 (codeColumns.get i)) = Pi.single i (1 : ZMod 2) := by
  decide +kernel

theorem codeDecode_basis (i : Fin 11) : codeDecode (codeBasis i) = Pi.single i 1 := by
  change (fun j => binaryColumn 112 (codeDecodeRows.get j) ⬝ᵥ
    (codeBasis i : NaturalModule)) = _
  rw [codeBasis_coordinates]
  exact codeDecode_checked i

theorem codeDecode_comp_codeLift : codeDecode.comp codeLift = LinearMap.id := by
  apply LinearMap.pi_ext
  intro i a
  simp only [LinearMap.comp_apply, codeLift, Fintype.linearCombination_apply_single,
    map_smul, codeDecode_basis, LinearMap.id_apply]
  funext j
  by_cases h : i = j <;> simp [h]

/-- The eleven-dimensional configuration is embedded in the actual fixed space. -/
theorem codeLift_injective : Function.Injective codeLift := by
  apply Function.LeftInverse.injective (g := codeDecode)
  intro v
  exact LinearMap.congr_fun codeDecode_comp_codeLift v

end Janko4.LocalStructure.MathieuSeedCentralizer.AmbientOrder.FixedImage
