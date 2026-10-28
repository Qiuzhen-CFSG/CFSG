module

public import Theory.Representation.MathieuCodeRestriction.M22.SourceModules.OrbitStabilizers.Action
public import Theory.Mathieu.M23.QuasithinGeometry.PairPlane
/-!
# Compatible PSL(3,4) models for the native point stabilizers

Triple transitivity supplies a native M24 conjugation carrying the marked
moving point to coordinate zero and the distinguished pair to the standard
M23 pair. Conjugating the embedded M23 pair group gives an injective map onto
the outer point stabilizer; the proved equal orders establish surjectivity.
Restricting its inverse to the native inner point stabilizer gives the
pointwise pair subgroup. The existing faithful plane-action equivalences then
identify these groups with PSL(3,4) and its field-Frobenius extension, retaining
the inclusion of the former into the latter.

Source: Aschbacher--Smith, H.15.1 and 8.1.1, printed pp.398,712;
the compatible M23 plane model is the one used in 5.2.18, printed p.655.
-/

public section
open Sporadic.Mathieu
open scoped Pointwise
namespace MathieuCode
noncomputable section
set_option maxRecDepth 10000

private theorem exists_marking (i : Fin 22) : ∃ g : M24,
    g • (0 : Fin 24) = m23PointEmbedding (M23Geometry.label 5) ∧
    g • (9 : Fin 24) = m23PointEmbedding (M23Geometry.label 6) ∧
    g • m22Coordinates i = 0 := by
  let a : Fin 3 ↪ Fin 24 := ⟨![0, 9, m22Coordinates i], by revert i; decide +kernel⟩
  let b : Fin 3 ↪ Fin 24 :=
    ⟨![m23PointEmbedding (M23Geometry.label 5), m23PointEmbedding (M23Geometry.label 6), 0],
      by decide +kernel⟩
  let := m24_isFivePretransitive
  have ht : MulAction.IsMultiplyPretransitive M24 (Fin 24) 3 :=
    MulAction.isMultiplyPretransitive_of_le (n := 5) (by decide) (by simp)
  obtain ⟨g, hg⟩ := ht.exists_smul_eq a b
  exact ⟨g, congrArg (fun e : Fin 3 ↪ Fin 24 => e 0) hg,
    congrArg (fun e : Fin 3 ↪ Fin 24 => e 1) hg,
    congrArg (fun e : Fin 3 ↪ Fin 24 => e 2) hg⟩

private def marking (i : Fin 22) : M24 := Classical.choose (exists_marking i)
private theorem marking_zero (i : Fin 22) :
    marking i • (0 : Fin 24) = m23PointEmbedding (M23Geometry.label 5) :=
  (Classical.choose_spec (exists_marking i)).1
private theorem marking_nine (i : Fin 22) :
    marking i • (9 : Fin 24) = m23PointEmbedding (M23Geometry.label 6) :=
  (Classical.choose_spec (exists_marking i)).2.1
private theorem marking_moving (i : Fin 22) : marking i • m22Coordinates i = 0 :=
  (Classical.choose_spec (exists_marking i)).2.2

private def liftedPair : Finset (Fin 24) := M23Geometry.x.val.map m23PointEmbedding
private theorem liftedPair_smul (h : M23) :
    pointEmbedding h • liftedPair = (h • M23Geometry.x.val).map m23PointEmbedding := by
  simp only [liftedPair, Finset.smul_finset_def, Finset.map_eq_image, Finset.image_image]
  congr 1
  funext a
  exact pointEmbedding_apply h a

private theorem marking_pair (i : Fin 22) : marking i • m22Pair = liftedPair := by
  simp only [m22Pair, Finset.smul_finset_insert, Finset.smul_finset_singleton,
    marking_zero, marking_nine, liftedPair, M23Geometry.x, Finset.map_insert, Finset.map_singleton]

private def movedHom (i : Fin 22) : M23 →* M24 :=
  (MulAut.conj (marking i)⁻¹).toMonoidHom.comp pointEmbedding

private theorem movedHom_apply (i : Fin 22) (h : M23) (k : Fin 24) :
    movedHom i h • k = (marking i)⁻¹ • (pointEmbedding h • (marking i • k)) := by
  change ((marking i)⁻¹ * pointEmbedding h * ((marking i)⁻¹)⁻¹) • k = _
  rw [inv_inv, mul_smul, mul_smul]


private theorem movedHom_injective (i : Fin 22) : Function.Injective (movedHom i) :=
  (MulAut.conj (marking i)⁻¹).injective.comp pointEmbedding_injective

private theorem movedHom_moving (i : Fin 22) (h : M23) :
    movedHom i h • m22Coordinates i = m22Coordinates i := by
  rw [movedHom_apply, marking_moving, show pointEmbedding h • (0 : Fin 24) = 0 from pointEmbedding_fixed h]
  rw [← marking_moving i, inv_smul_smul]

private theorem movedHom_pair (i : Fin 22) (h : M23Geometry.pairStabilizer) :
    movedHom i h.val ∈ m22PairStabilizer := by
  have he : pointEmbedding h.val • liftedPair = liftedPair := by
    rw [liftedPair_smul, show h.val • M23Geometry.x.val = M23Geometry.x.val from h.property]
    rfl
  change movedHom i h.val • m22Pair = m22Pair
  change ((marking i)⁻¹ * pointEmbedding h.val * ((marking i)⁻¹)⁻¹) • m22Pair = m22Pair
  rw [inv_inv, mul_smul, mul_smul, marking_pair, he, ← marking_pair i, inv_smul_smul]

private def outerFromM23 (i : Fin 22) : M23Geometry.pairStabilizer →* m22OuterPointStabilizer i where
  toFun h := ⟨⟨movedHom i h.val, movedHom_pair i h⟩, movedHom_moving i h.val⟩
  map_one' := by apply Subtype.ext; apply Subtype.ext; exact (movedHom i).map_one
  map_mul' h k := by apply Subtype.ext; apply Subtype.ext; exact (movedHom i).map_mul h.val k.val

private theorem outerFromM23_injective (i : Fin 22) : Function.Injective (outerFromM23 i) := by
  intro h k he
  apply Subtype.ext
  apply movedHom_injective i
  exact congrArg (fun u : m22OuterPointStabilizer i => u.val.val) he

private theorem outerFromM23_bijective (i : Fin 22) : Function.Bijective (outerFromM23 i) := by
  apply (Nat.bijective_iff_injective_and_card _).mpr
  refine ⟨outerFromM23_injective i, ?_⟩
  rw [← m22WeightTwoVector_outer_stabilizer, m22WeightTwoVector_outer_stabilizer_card,
    M23Geometry.PairPlaneImage.pairStabilizer_card]

/-- The native outer point stabilizer is PSL(3,4) extended by field Frobenius. -/
def m22OuterPointStabilizerEquiv (i : Fin 22) :
    m22OuterPointStabilizer i ≃* Matrix.PSL3Four.FieldExtension :=
  (MulEquiv.ofBijective (outerFromM23 i) (outerFromM23_bijective i)).symm.trans
    M23Geometry.PairPlane.pairEquiv

private def outerEquivFromM23 (i : Fin 22) : M23Geometry.pairStabilizer ≃* m22OuterPointStabilizer i :=
  MulEquiv.ofBijective (outerFromM23 i) (outerFromM23_bijective i)

private def innerToM23Pair (i : Fin 22) : MulAction.stabilizer M22 i →* M23Geometry.pairStabilizer :=
  (outerEquivFromM23 i).symm.toMonoidHom.comp (m22PointToOuterPoint i)

private theorem innerToM23Pair_embedding (i : Fin 22) (k : MulAction.stabilizer M22 i) :
    movedHom i (innerToM23Pair i k).val = m22Embedding k.val := by
  have h := (outerEquivFromM23 i).apply_symm_apply (m22PointToOuterPoint i k)
  exact congrArg (fun u : m22OuterPointStabilizer i => u.val.val) h

private theorem innerToM23Pair_pointwise (i : Fin 22) (k : MulAction.stabilizer M22 i) :
    innerToM23Pair i k ∈ M23Geometry.pointwisePairStabilizer := by
  apply (M23Geometry.mem_pointwisePairStabilizer _).mpr
  have hfix (a : Fin 24) (ha : m22Embedding k.val • a = a) :
      pointEmbedding (innerToM23Pair i k).val • (marking i • a) = marking i • a := by
    rw [← innerToM23Pair_embedding i k, movedHom_apply] at ha
    have he := congrArg (fun b : Fin 24 => marking i • b) ha
    simpa only [smul_inv_smul] using he
  constructor
  · apply m23PointEmbedding.injective
    change m23PointEmbedding ((innerToM23Pair i k).val.val (M23Geometry.label 5)) = _
    rw [← pointEmbedding_apply, ← marking_zero i]
    exact hfix 0 (m22Embedding_fixed_zero k.val)
  · apply m23PointEmbedding.injective
    change m23PointEmbedding ((innerToM23Pair i k).val.val (M23Geometry.label 6)) = _
    rw [← pointEmbedding_apply, ← marking_nine i]
    exact hfix 9 (m22Embedding_fixed_nine k.val)

private def innerToM23 (i : Fin 22) : MulAction.stabilizer M22 i →* M23Geometry.pointwisePairStabilizer :=
  (innerToM23Pair i).codRestrict _ (innerToM23Pair_pointwise i)

private theorem innerToM23_injective (i : Fin 22) : Function.Injective (innerToM23 i) := by
  intro k l h
  apply Subtype.ext
  apply m22Embedding_injective
  have he := congrArg Subtype.val h
  change innerToM23Pair i k = innerToM23Pair i l at he
  have hm := congrArg (fun u : M23Geometry.pairStabilizer => movedHom i u.val) he
  exact (innerToM23Pair_embedding i k).symm.trans (hm.trans (innerToM23Pair_embedding i l))


private theorem innerToM23_bijective (i : Fin 22) : Function.Bijective (innerToM23 i) := by
  apply (Nat.bijective_iff_injective_and_card _).mpr
  refine ⟨innerToM23_injective i, ?_⟩
  rw [← m22WeightTwoVector_stabilizer, m22WeightTwoVector_stabilizer_card,
    M23Geometry.PairPlaneImage.pointwisePairStabilizer_card]

/-- The native M22 point stabilizer is the actual projective special linear group. -/
def m22PointStabilizerEquiv (i : Fin 22) :
    MulAction.stabilizer M22 i ≃* Matrix.PSL3Four.PSL :=
  (MulEquiv.ofBijective (innerToM23 i) (innerToM23_bijective i)).trans
    M23Geometry.PairPlane.pointwiseEquiv

/-- Both identifications preserve the marked inclusion of the inner stabilizer. -/
theorem m22PointStabilizerEquiv_compatible (i : Fin 22) (k : MulAction.stabilizer M22 i) :
    m22OuterPointStabilizerEquiv i (m22PointToOuterPoint i k) =
      Matrix.PSL3Four.linearInclusion (m22PointStabilizerEquiv i k) := by
  exact M23Geometry.PairPlane.pairEquiv_pointwise (innerToM23 i k)

end
end MathieuCode
