module
public import Theory.Representation.Mathieu.SmallModules.M22Recognition.DegreeThirty.SixteenSubmodule.InducedFiltration.GeneratorMatrices.Transversal
import all Theory.Representation.MathieuCodeRestriction.M22.SourceModules.OrbitStabilizers.Models

/-!
# Comparing the explicit and native M22 point markings

A certified word in the native M24 generators sends the ordered triple
`(0, 9, m22Coordinates 0)` to the marked M23 pair and zero. Its difference
from the chosen native marking fixes all three target points, hence belongs
to the embedded pointwise-pair subgroup. Conjugation by its PSL image gives
one binary adjoint equivalence valid for the entire native zero stabilizer.
`markingChange_intertwines` retains the literal embedding equation, so a
finite word certificate can connect numerical matrices to `pointAdjoint`.

The `import all` above is intentional internal coupling to the chosen marking
and its specification in `OrbitStabilizers.Models`. It avoids changing that
shared module or choosing a second unrelated stabilizer isomorphism. No private
constant occurs in a public signature, and the coordinate-change body is hidden.

Source context: Guralnick--Malle I, Proposition 5.1, pp.15--16;
Aschbacher--Smith, Chapter K, printed pp.451--452 and 457. This comparison
supplies coordinates for the local adjoint model, not a recognition theorem.
-/

open Sporadic.Mathieu MathieuCode
open scoped Pointwise
set_option maxRecDepth 10000

namespace Representation.MathieuSmall.M22Recognition.DegreeThirty.SixteenSubmodule.LocalBlocks

/-- A native M24 word realizing the required ordered triple. -/
@[expose] public def markingWord : List (Fin 2) :=
  [0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1,
    0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0]

/-- Evaluate native M24 letters with the rightmost letter acting first. -/
@[expose] public def markingWordPerm : List (Fin 2) → Equiv.Perm (Fin 24)
  | [] => 1
  | k :: w => (![m24GeneratorA, m24GeneratorB] k) * markingWordPerm w

private noncomputable def wordElement : List (Fin 2) → M24
  | [] => 1
  | k :: w => (![m24GeneratorAInM24, m24GeneratorBInM24] k) * wordElement w

private theorem wordElement_val (w : List (Fin 2)) : (wordElement w).val = markingWordPerm w := by
  induction w with
  | nil => rfl
  | cons k w ih =>
    change (![m24GeneratorAInM24, m24GeneratorBInM24] k).val * (wordElement w).val = _
    rw [ih]
    fin_cases k <;> rfl

/-- The executable permutation of the explicit marking. -/
@[expose] public def explicitMarkingPerm : Equiv.Perm (Fin 24) := markingWordPerm markingWord

/-- The same certified word inside the actual M24 group. -/
public noncomputable def explicitMarking : M24 := wordElement markingWord

public theorem explicitMarking_val : explicitMarking.val = explicitMarkingPerm :=
  wordElement_val _

public theorem explicitMarking_zero :
    explicitMarking • (0 : Fin 24) = m23PointEmbedding (M23Geometry.label 5) := by
  change explicitMarking.val 0 = _
  rw [explicitMarking_val]
  decide +kernel

public theorem explicitMarking_nine :
    explicitMarking • (9 : Fin 24) = m23PointEmbedding (M23Geometry.label 6) := by
  change explicitMarking.val 9 = _
  rw [explicitMarking_val]
  decide +kernel

public theorem explicitMarking_moving : explicitMarking • m22Coordinates 0 = 0 := by
  change explicitMarking.val (m22Coordinates 0) = _
  rw [explicitMarking_val]
  decide +kernel

/-- The literal inclusion of the pointwise M23 pair subgroup into M24. -/
@[expose] public noncomputable def pairEmbedding : M23Geometry.pointwisePairStabilizer →* M24 :=
  pointEmbedding.comp (M23Geometry.pairStabilizer.subtype.comp
    M23Geometry.pointwisePairStabilizer.subtype)

public theorem pairEmbedding_injective : Function.Injective pairEmbedding :=
  pointEmbedding_injective.comp (Subtype.val_injective.comp Subtype.val_injective)

private theorem nativePair_embedding (h : MulAction.stabilizer M22 (0 : Fin 22)) :
    pairEmbedding (innerToM23 0 h) = marking 0 * m22Embedding h.val * (marking 0)⁻¹ := by
  have he := innerToM23Pair_embedding 0 h
  change (marking 0)⁻¹ * pairEmbedding (innerToM23 0 h) * marking 0 = m22Embedding h.val at he
  calc
    pairEmbedding (innerToM23 0 h) =
        marking 0 * ((marking 0)⁻¹ * pairEmbedding (innerToM23 0 h) * marking 0) *
          (marking 0)⁻¹ := by group
    _ = _ := by rw [he]

private theorem exists_pairDifference : ∃ d : M23Geometry.pointwisePairStabilizer,
    pairEmbedding d = explicitMarking * (marking 0)⁻¹ := by
  have hfix : explicitMarking * (marking 0)⁻¹ ∈ MulAction.stabilizer M24 (0 : Fin 24) := by
    change (explicitMarking * (marking 0)⁻¹) • (0 : Fin 24) = 0
    rw [mul_smul]
    conv_lhs => rw [← marking_moving 0, inv_smul_smul, explicitMarking_moving]
  rw [← pointEmbedding_range] at hfix
  obtain ⟨d, hd⟩ := hfix
  have h5 : d • M23Geometry.label 5 = M23Geometry.label 5 := by
    apply m23PointEmbedding.injective
    change m23PointEmbedding (d.val (M23Geometry.label 5)) = _
    rw [← pointEmbedding_apply]
    change pointEmbedding d • m23PointEmbedding (M23Geometry.label 5) = _
    rw [hd, mul_smul]
    conv_lhs => rw [← marking_zero 0, inv_smul_smul, explicitMarking_zero]
  have h6 : d • M23Geometry.label 6 = M23Geometry.label 6 := by
    apply m23PointEmbedding.injective
    change m23PointEmbedding (d.val (M23Geometry.label 6)) = _
    rw [← pointEmbedding_apply]
    change pointEmbedding d • m23PointEmbedding (M23Geometry.label 6) = _
    rw [hd, mul_smul]
    conv_lhs => rw [← marking_nine 0, inv_smul_smul, explicitMarking_nine]
  have hp : d ∈ M23Geometry.pairStabilizer := by
    change d • {M23Geometry.label 5, M23Geometry.label 6} = _
    rw [Finset.smul_finset_insert, Finset.smul_finset_singleton, h5, h6]
    rfl
  exact ⟨⟨⟨d, hp⟩, (M23Geometry.mem_pointwisePairStabilizer _).mpr ⟨h5, h6⟩⟩, hd⟩

private noncomputable def pairDifference : M23Geometry.pointwisePairStabilizer :=
  Classical.choose exists_pairDifference

private theorem pairDifference_embedding :
    pairEmbedding pairDifference = explicitMarking * (marking 0)⁻¹ :=
  Classical.choose_spec exists_pairDifference

/-- The projective adjoint representation before choosing a point marking. -/
@[expose] public noncomputable def projectiveAdjoint :
    Representation (ZMod 2) Matrix.PSL3Four.PSL Adjoint :=
  QuotientGroup.lift (Subgroup.center Matrix.PSL3Four.SL) adjointBinary
    (fun g hg => adjointBinary_center g hg)

public theorem projectiveAdjoint_mk (g : Matrix.PSL3Four.SL) :
    projectiveAdjoint (g : Matrix.PSL3Four.PSL) = adjointBinary g := rfl

private noncomputable def changeElement : Matrix.PSL3Four.PSL :=
  M23Geometry.PairPlane.pointwiseEquiv pairDifference

/-- One coordinate change, shared by all elements of the native zero stabilizer. -/
public noncomputable def markingChange : Adjoint ≃ₗ[ZMod 2] Adjoint where
  toLinearMap := projectiveAdjoint changeElement
  invFun := projectiveAdjoint changeElement⁻¹
  left_inv := projectiveAdjoint.inv_self_apply changeElement
  right_inv := projectiveAdjoint.self_inv_apply changeElement

private theorem nativePair_conjugate (h : MulAction.stabilizer M22 (0 : Fin 22))
    (s : M23Geometry.pointwisePairStabilizer)
    (hs : pairEmbedding s = explicitMarking * m22Embedding h.val * explicitMarking⁻¹) :
    s = pairDifference * innerToM23 0 h * pairDifference⁻¹ := by
  apply pairEmbedding_injective
  rw [hs, map_mul, map_mul, map_inv, pairDifference_embedding, nativePair_embedding]
  group

/-- Any explicitly marked pair element acts through the same native adjoint change. -/
public theorem markingChange_intertwines (h : MulAction.stabilizer M22 (0 : Fin 22))
    (s : M23Geometry.pointwisePairStabilizer)
    (hs : pairEmbedding s = explicitMarking * m22Embedding h.val * explicitMarking⁻¹)
    (v : Adjoint) :
    markingChange (pointAdjoint h v) =
      projectiveAdjoint (M23Geometry.PairPlane.pointwiseEquiv s) (markingChange v) := by
  rw [nativePair_conjugate h s hs]
  simp only [M23Geometry.PairPlane.pointwiseEquiv.map_mul,
    M23Geometry.PairPlane.pointwiseEquiv.map_inv]
  change projectiveAdjoint changeElement
    (projectiveAdjoint (M23Geometry.PairPlane.pointwiseEquiv (innerToM23 0 h)) v) =
      projectiveAdjoint (changeElement *
        M23Geometry.PairPlane.pointwiseEquiv (innerToM23 0 h) * changeElement⁻¹)
        (projectiveAdjoint changeElement v)
  simp only [map_mul, Module.End.mul_apply, Representation.inv_self_apply]

end Representation.MathieuSmall.M22Recognition.DegreeThirty.SixteenSubmodule.LocalBlocks
