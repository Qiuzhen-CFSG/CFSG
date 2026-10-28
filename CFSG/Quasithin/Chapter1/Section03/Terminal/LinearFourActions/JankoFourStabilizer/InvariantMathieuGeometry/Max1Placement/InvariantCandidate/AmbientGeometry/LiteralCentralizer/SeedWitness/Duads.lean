module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.InvariantCandidate.AmbientGeometry.LiteralCentralizer.Reduction
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.InvariantCandidate.LiteralGeometry.Transport
public import Theory.Mathieu.M24.Properties.Transitivity
import all CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Reduction

/-!
# Duad vectors in the literal max1 kernel

The checked binary pair labels intertwine the actual conjugation action with
its 24-star permutation action. Relabeling to the native Witt design gives
kernel vectors attached to duads. The triangle identity is multiplication of
vectors, and native M₂₄ two-transitivity puts every duad vector in the orbit
of the literal word `(xy)^14`.

The coordinate argument adapts the existing proof in
`Cardinality.LocalOrder.QuotientCount.Image.Comparison` and the saved
`LiteralCoreRecovery/Binary.lean` exploration. The finite tables themselves
are those of `Image.StarData`, derived from the ATLAS `J4G1-max1W1` words.
Source motivation: Aschbacher–Smith A.3.12(17), pp.47–48, and GLS3 Table 5.3i.

The private-scope import of `InvariantMathieuGeometry.Reduction` is an
internal equation adapter for its unexposed `certifiedMathieuQuotientEquiv`.
It proves compatibility without changing that shared module or re-exporting
its private scope. The public duad API uses only native points and elements
of the certified subgroup.
-/

set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency true

public section

namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.AmbientGeometry.SeedDuads
open Janko4 Janko4.Cardinality Janko4.Cardinality.QuotientCount
open Janko4.Cardinality.QuotientCount.Image Janko4.Cardinality.KernelCount
section Generic
variable (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1)
attribute [local irreducible] basis modelGroup matrixA matrixB localKernel
  max1Subgroup localX localY localKernelSeed

private def maskValue (m : ℕ) : localKernel hA hB :=
  coordinates hA hB (fun i => m.testBit i.val)

private lemma maskValue_zero : maskValue hA hB 0 = 1 := by
  apply Subtype.ext
  simp [maskValue, coordinates_val, binaryProduct_zero]

private lemma maskValue_xor (m n : ℕ) :
    maskValue hA hB (Nat.xor m n) = maskValue hA hB m * maskValue hA hB n := by
  change maskValue hA hB (m ^^^ n) = _
  simp only [maskValue, coordinates_mul, Nat.testBit_xor]

private lemma maskValue_fold (l : List ℕ) :
    maskValue hA hB (l.foldr Nat.xor 0) = (l.map (maskValue hA hB)).prod := by
  induction l with
  | nil => exact maskValue_zero hA hB
  | cons a l ih => simpa only [List.foldr_cons, List.map_cons, List.prod_cons,
      maskValue_xor] using congrArg (maskValue hA hB a * ·) ih

private lemma maskValue_maskImage (masks : Fin 11 → ℕ) (m : ℕ) :
    (maskValue hA hB (maskImage masks m) : max1Subgroup hA hB) =
      binaryProduct (fun i => binaryProduct (basis hA hB)
        (fun j => (masks i).testBit j.val)) (fun i => m.testBit i.val) := by
  rw [maskImage, maskValue_fold]
  simp only [List.map_ofFn, SubmonoidClass.coe_list_prod]
  rw [binaryProduct]
  congr 1
  congr 1
  funext i
  dsimp only [Function.comp_apply]
  split_ifs
  · rfl
  · change (maskValue hA hB 0 : max1Subgroup hA hB) = 1
    rw [maskValue_zero]
    rfl

private lemma right_compatible_x (i j : Fin 24) :
    action hA hB (localX hA hB)⁻¹ (maskValue hA hB (pairLabel i j)) =
      maskValue hA hB (pairLabel (rightX i) (rightX j)) := by
  apply Subtype.ext
  rw [action_apply, inv_inv, pairLabel_rightX, maskValue_maskImage]
  exact right_conj_coordinates_x hA hB _

private lemma right_compatible_y (i j : Fin 24) :
    action hA hB (localY hA hB)⁻¹ (maskValue hA hB (pairLabel i j)) =
      maskValue hA hB (pairLabel (rightY i) (rightY j)) := by
  apply Subtype.ext
  rw [action_apply, inv_inv, pairLabel_rightY, maskValue_maskImage]
  exact right_conj_coordinates_y hA hB _

private def Compatible (p : Equiv.Perm (localKernel hA hB) × Equiv.Perm (Fin 24)) : Prop :=
  ∀ i j, p.1 (maskValue hA hB (pairLabel i j)) =
    maskValue hA hB (pairLabel (p.2 i) (p.2 j))

private lemma compatible_inv {p : Equiv.Perm (localKernel hA hB) × Equiv.Perm (Fin 24)}
    (h : Compatible hA hB p) : Compatible hA hB p⁻¹ := by
  intro i j
  apply p.1.injective
  simpa using (h (p.2⁻¹ i) (p.2⁻¹ j)).symm

private noncomputable def starProjection : max1Subgroup hA hB →* Equiv.Perm (Fin 24) :=
  StarGroup.subtype.comp ((actionImageEquivStarGroup hA hB).toMonoidHom.comp
    (action hA hB).rangeRestrict)

private theorem projection_x : starProjection hA hB (localX hA hB) = starX :=
  actionImageEquivStarGroup_x hA hB

private theorem projection_y : starProjection hA hB (localY hA hB) = starY :=
  actionImageEquivStarGroup_y hA hB

/-- The star permutation intertwines the actual left-conjugation action on all pair labels. -/
private theorem starProjection_compatible (g : max1Subgroup hA hB) :
    ∀ i j, action hA hB g (maskValue hA hB (pairLabel i j)) =
      maskValue hA hB (pairLabel (starProjection hA hB g i) (starProjection hA hB g j)) := by
  change Compatible hA hB (action hA hB g, starProjection hA hB g)
  have hg : g ∈ Subgroup.closure {localX hA hB, localY hA hB} := by
    rw [localXY_generate]
    trivial
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    rcases Set.mem_insert_iff.mp hg with rfl | hg
    · rw [projection_x]
      have hr : Compatible hA hB (action hA hB (localX hA hB)⁻¹, rightX) :=
        right_compatible_x hA hB
      simpa only [Prod.inv_mk, ← map_inv, inv_inv, starX] using compatible_inv hA hB hr
    · obtain rfl := Set.mem_singleton_iff.mp hg
      rw [projection_y]
      have hr : Compatible hA hB (action hA hB (localY hA hB)⁻¹, rightY) :=
        right_compatible_y hA hB
      simpa only [Prod.inv_mk, ← map_inv, inv_inv, starY] using compatible_inv hA hB hr
  | one => intro i j; simp only [map_one, Equiv.Perm.one_apply]
  | mul g h hg hh ihg ihh =>
    intro i j
    change (action hA hB (g * h)) _ = _
    rw [map_mul, map_mul]
    change action hA hB g (action hA hB h _) = _
    rw [ihh, ihg]
    rfl
  | inv g hg ih =>
    simpa only [Prod.inv_mk, map_inv] using compatible_inv hA hB ih


private theorem maskValue_one :
    (maskValue hA hB 1 : max1Subgroup hA hB) = localKernelSeed hA hB := by
  have h : (maskValue hA hB (2 ^ (0 : Fin 11).val) : max1Subgroup hA hB) =
      basis hA hB 0 := by
    simp only [maskValue, coordinates_val, Nat.testBit_two_pow]
    convert binaryProduct_single (basis hA hB) 0 using 2
    funext j
    simp only [Fin.ext_iff, eq_comm]
  simpa only [Fin.val_zero, pow_zero, basis, conjugates, Matrix.cons_val_zero] using h

private theorem pairLabel_row_zero : ∀ i j : Fin 24,
    Nat.xor (pairLabel 0 i) (pairLabel 0 j) = pairLabel i j := by
  decide +kernel

private theorem pairLabel_triangle (i j k : Fin 24) :
    Nat.xor (pairLabel i k) (pairLabel j k) = pairLabel i j := by
  rw [← pairLabel_row_zero i k, ← pairLabel_row_zero j k, ← pairLabel_row_zero i j]
  change ((pairLabel 0 i ^^^ pairLabel 0 k) ^^^ (pairLabel 0 j ^^^ pairLabel 0 k)) =
    (pairLabel 0 i ^^^ pairLabel 0 j)
  rw [Nat.xor_assoc, Nat.xor_comm (pairLabel 0 j), Nat.xor_xor_cancel_left]

end Generic

open Subgroup Sporadic.Mathieu
open StarOrderCertificate
attribute [local irreducible] Janko4.modelGroup

/-- The kernel vector attached to a duad, in the native Witt-design labeling. -/
noncomputable def duad (i j : Fin 24) : certifiedMathieuSubgroup :=
  (maskValue matrixA_mul_self matrixB_pow_four
    (pairLabel (relabel.symm i) (relabel.symm j)) : max1Subgroup _ _)

theorem duad_mem_core (i j : Fin 24) : duad i j ∈ pCore 2 certifiedMathieuSubgroup := by
  change (maskValue _ _ _ : max1Subgroup _ _) ∈ pCore 2 (max1Subgroup _ _)
  rw [← LocalStructure.localKernel_eq_twoCore]
  exact (maskValue _ _ _).property

private theorem literalMathieuMap_apply (g : certifiedMathieuSubgroup) :
    (literalMathieuMap g : Equiv.Perm (Fin 24)) =
      MulAut.conj relabel (starProjection matrixA_mul_self matrixB_pow_four g) := by
  have he := QuotientGroup.quotientMulEquivOfEq_mk
    (LocalStructure.localKernel_eq_twoCore matrixA_mul_self matrixB_pow_four).symm
    (g : max1Subgroup matrixA_mul_self matrixB_pow_four)
  exact (congrArg (fun z : LocalQuotient matrixA_mul_self matrixB_pow_four =>
    (LocalStructure.localQuotientEquivM24 matrixA_mul_self matrixB_pow_four z :
      Equiv.Perm (Fin 24))) he).trans (starGroupEquivM24_apply _)

theorem conjugate_duad (g : certifiedMathieuSubgroup) (i j : Fin 24) :
    g * duad i j * g⁻¹ = duad (literalMathieuMap g • i) (literalMathieuMap g • j) := by
  have h := congrArg (fun v : localKernel matrixA_mul_self matrixB_pow_four =>
    (v : max1Subgroup matrixA_mul_self matrixB_pow_four))
    (starProjection_compatible matrixA_mul_self matrixB_pow_four g
      (relabel.symm i) (relabel.symm j))
  change g * duad i j * g⁻¹ = _ at h
  rw [h]
  unfold duad
  congr 3 <;>
    simp only [Subgroup.smul_def, Equiv.Perm.smul_def, literalMathieuMap_apply,
      MulAut.conj_apply, Equiv.Perm.mul_apply, Equiv.Perm.inv_def,
      Equiv.symm_apply_apply]

theorem duad_mul (i j k : Fin 24) : duad i k * duad j k = duad i j := by
  unfold duad
  exact congrArg (fun z : localKernel matrixA_mul_self matrixB_pow_four =>
    (z : max1Subgroup matrixA_mul_self matrixB_pow_four))
      ((maskValue_xor _ _ _ _).symm.trans (congrArg (maskValue _ _) (pairLabel_triangle _ _ _)))

theorem duad_symm (i j : Fin 24) : duad i j = duad j i := by
  unfold duad
  rw [pairLabel_symm]

theorem duad_self (i : Fin 24) : duad i i = 1 := by
  unfold duad
  rw [(pairLabel_eq_zero_iff _ _).mpr rfl, maskValue_zero]
  rfl

theorem duad_inv (i j : Fin 24) : (duad i j)⁻¹ = duad i j := by
  apply inv_eq_of_mul_eq_one_right
  rw [duad_mul, duad_self]

theorem duad_seed : duad (relabel 0) (relabel 1) = literalCentralizerSeed := by
  simp only [duad, Equiv.symm_apply_apply]
  exact maskValue_one _ _

theorem duad_is_seed_conjugate (i j : Fin 24) (hij : i ≠ j) :
    ∃ g : certifiedMathieuSubgroup, g * literalCentralizerSeed * g⁻¹ = duad i j := by
  let : MulAction.IsMultiplyPretransitive M24 (Fin 24) 5 := m24_isFivePretransitive
  have ht : MulAction.IsMultiplyPretransitive M24 (Fin 24) 2 :=
    MulAction.isMultiplyPretransitive_of_le (n := 5) (by decide) (by simp)
  obtain ⟨g, hi, hj⟩ := MulAction.is_two_pretransitive_iff.mp ht
    (relabel.injective.ne (by decide : (0 : Fin 24) ≠ 1)) hij
  obtain ⟨x, rfl⟩ := literalMathieuMap_surjective g
  exact ⟨x, by rw [← duad_seed, conjugate_duad, hi, hj]⟩

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.AmbientGeometry.SeedDuads
