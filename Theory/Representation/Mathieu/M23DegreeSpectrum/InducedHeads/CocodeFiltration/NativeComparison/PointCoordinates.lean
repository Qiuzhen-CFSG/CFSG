module

public import Theory.Representation.Mathieu.M23DegreeSpectrum.InducedHeads.CocodeFiltration.NativeComparison.Data
public import Theory.Representation.MathieuCodeRestriction.M22.SourceModules.PairVectors

/-!
# Coordinates on the literal native M22 cocode

The published 23 masks define a linear map on the native 24-coordinate space,
ignoring the distinguished coordinate 0 (Atlas 24). Kernel-checked identities
show that the map kills all twelve Golay rows and the distinguished pair.
Restricting to the even core and descending through both literal quotient maps
therefore gives coordinates on `MathieuCode.M22Cocode`.

The ordered pairs e14 + e24, ..., e23 + e24 map to the ten standard basis
vectors. This proves surjectivity; the existing dimension theorem then proves
injectivity. The canonical stabilizer marking recovers the original inclusion
in M24. Its action permutes the actual pair representatives, proving the
published matrix formula on the basis and hence on every vector.

Source application: Guralnick–Malle, *Classification of 2F-modules I*,
Proposition 5.1, M23 paragraph, journal p.366/manuscript p.16. This is the local
quotient calculation for the independently constructed filtration, not an
assumption of that filtration. Mask and ordering provenance is recorded in
`NativeComparison/source/README.md` and `InducedHeads/source/native-candidate.json`.
-/

public noncomputable section
open Sporadic.Mathieu MathieuCode
open scoped BigOperators
namespace Representation.MathieuSmall.M23DegreeSpectrum.InducedHeads.CocodeFiltration.NativeComparison

private def fullCoordinates : Full →ₗ[ZMod 2] (Fin 10 → ZMod 2) where
  toFun v x := ∑ i : Fin 23, v (m23PointEmbedding i) * bit (quotientMask i) x.val
  map_add' v w := by
    funext x
    simp [add_mul, Finset.sum_add_distrib]
  map_smul' c v := by
    funext x
    simp [Finset.mul_sum, mul_assoc]

private theorem fullCoordinates_row (i : Fin 12) : fullCoordinates (row i) = 0 := by
  funext x
  change (∑ j : Fin 23, row i (m23PointEmbedding j) * bit (quotientMask j) x.val) = 0
  revert i x
  decide +kernel

private theorem fullCoordinates_golay : golay ≤ fullCoordinates.ker := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  exact fullCoordinates_row i

private def coreCoordinates : Core →ₗ[ZMod 2] (Fin 10 → ZMod 2) :=
  fullCoordinates.comp Core.subtype

private def cocodeCoordinates : Cocode →ₗ[ZMod 2] (Fin 10 → ZMod 2) :=
  codeInCore.liftQ coreCoordinates (by
    intro v hv
    exact fullCoordinates_golay hv)

private theorem cocodeCoordinates_mk (v : Core) :
    cocodeCoordinates (codeInCore.mkQ v) = fullCoordinates v.val := rfl

private theorem cocodeCoordinates_pair : cocodeCoordinates m22PairClass = 0 := by
  rw [m22PairClass, cocodeCoordinates_mk]
  funext x
  change (∑ j : Fin 23, m22PairWord (m23PointEmbedding j) * bit (quotientMask j) x.val) = 0
  revert x
  decide +kernel

private def quotientCoordinates : M22Cocode →ₗ[ZMod 2] (Fin 10 → ZMod 2) :=
  m22PairLine.liftQ cocodeCoordinates (by
    apply Submodule.span_le.mpr
    rintro _ rfl
    exact cocodeCoordinates_pair)

private theorem quotientCoordinates_mk (v : Core) :
    quotientCoordinates (m22PairLine.mkQ (codeInCore.mkQ v)) = fullCoordinates v.val :=
  cocodeCoordinates_mk v

private theorem quotientCoordinates_pair (i : Fin 23) :
    quotientCoordinates (m22CocodePair (m23PointEmbedding i) 0) =
      fun x => bit (quotientMask i) x.val := by
  rw [m22CocodePair, quotientCoordinates_mk]
  funext x
  simp only [fullCoordinates, m22EvenPair, LinearMap.coe_mk, AddHom.coe_mk]
  have hn (j : Fin 23) : m23PointEmbedding j ≠ 0 := by
    revert j
    decide +kernel
  simp [Pi.single_apply, m23PointEmbedding.injective.eq_iff, hn]

private theorem quotientCoordinates_basis (y : Fin 10) :
    quotientCoordinates (m22CocodePair (m23PointEmbedding (quotientPoint y)) 0) =
      Pi.single y 1 := by
  rw [quotientCoordinates_pair]
  revert y
  decide +kernel

private theorem quotientCoordinates_surjective : Function.Surjective quotientCoordinates := by
  intro v
  refine ⟨∑ y : Fin 10, v y • m22CocodePair (m23PointEmbedding (quotientPoint y)) 0, ?_⟩
  simp only [map_sum, map_smul, quotientCoordinates_basis]
  ext x
  simp [Pi.single_apply, Finset.sum_apply]

private theorem quotientCoordinates_bijective : Function.Bijective quotientCoordinates := by
  refine ⟨?_, quotientCoordinates_surjective⟩
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (by simpa using finrank_m22Cocode)).mpr quotientCoordinates_surjective

private noncomputable def quotientEquiv : M22Cocode ≃ₗ[ZMod 2] (Fin 10 → ZMod 2) :=
  LinearEquiv.ofBijective quotientCoordinates quotientCoordinates_bijective

private theorem pairExpansion (v : M22Cocode) :
    v = ∑ y : Fin 10, quotientCoordinates v y •
      m22CocodePair (m23PointEmbedding (quotientPoint y)) 0 := by
  apply quotientCoordinates_bijective.1
  simp only [map_sum, map_smul, quotientCoordinates_basis]
  ext x
  simp [Pi.single_apply, Finset.sum_apply]

private theorem canonicalMarking_embedding (g : Models.pointGroup) :
    m22Embedding (canonicalMarking g) = pointEmbedding g.val := by
  apply congrArg pointEmbedding
  change (m23EquivM22PointStabilizer (m23EquivM22PointStabilizer.symm g)).val = g.val
  rw [MulEquiv.apply_symm_apply]

private theorem canonicalAction_pair (g : Models.pointGroup) (i : Fin 23) :
    Models.pointAction canonicalMarking false g (m22CocodePair (m23PointEmbedding i) 0) =
      m22CocodePair (m23PointEmbedding (g.val.val i)) 0 := by
  change m22CocodeRepresentation (canonicalMarking g) _ = _
  rw [m22CocodePair, m22CocodeRepresentation_mk, cocodeRepresentation_mk,
    canonicalMarking_embedding]
  apply congrArg (fun v : Core => m22PairLine.mkQ (codeInCore.mkQ v))
  apply Subtype.ext
  have hs (a : Fin 24) : fullRepresentation (pointEmbedding g.val) (Pi.single a 1) =
      Pi.single ((pointEmbedding g.val).val a) 1 := by
    ext b
    change (Pi.single a 1 : Full) ((pointEmbedding g.val).val.symm b) = _
    simp only [Pi.single_apply]
    congr 1
    exact propext (pointEmbedding g.val).val.symm_apply_eq
  change fullRepresentation (pointEmbedding g.val)
    (Pi.single (m23PointEmbedding i) 1 + Pi.single 0 1) = _
  rw [map_add, hs, hs, pointEmbedding_apply, pointEmbedding_fixed]
  rfl

private theorem quotientCoordinates_intertwines (g : Models.pointGroup) (v : M22Cocode) :
    quotientCoordinates (Models.pointAction canonicalMarking false g v) =
      (pointMatrix g).mulVec (quotientCoordinates v) := by
  let f : M22Cocode →ₗ[ZMod 2] (Fin 10 → ZMod 2) :=
    quotientCoordinates.comp (Models.pointAction canonicalMarking false g)
  have hf (i : Fin 23) : f (m22CocodePair (m23PointEmbedding i) 0) =
      fun x => bit (quotientMask (g.val.val i)) x.val := by
    exact (congrArg quotientCoordinates (canonicalAction_pair g i)).trans
      (quotientCoordinates_pair _)
  change f v = _
  conv_lhs => rw [pairExpansion v]
  rw [map_sum]
  simp only [map_smul, hf]
  ext x
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct,
    pointMatrix]
  apply Finset.sum_congr rfl
  intro y _
  exact mul_comm _ _

/-- The actual native cocode in the ten published coordinates, equivariantly
for every member of the canonically marked point stabilizer. -/
def nativePointCoordinates : PointCoordinates where
  equiv := quotientEquiv
  intertwines := quotientCoordinates_intertwines

/-- The coordinate formula retains both literal quotient maps. -/
theorem nativePointCoordinates_mk (v : Core) (x : Fin 10) :
    nativePointCoordinates.equiv (m22PairLine.mkQ (codeInCore.mkQ v)) x =
      ∑ i : Fin 23, v.val (m23PointEmbedding i) * bit (quotientMask i) x.val :=
  congrFun (quotientCoordinates_mk v) x

/-- The published mask is the image of the actual pair class, with the native
Atlas relabelling retained. -/
theorem nativePointCoordinates_pair (i : Fin 23) :
    nativePointCoordinates.equiv (m22CocodePair (m23PointEmbedding i) 0) =
      fun x => bit (quotientMask i) x.val :=
  quotientCoordinates_pair i

/-- The displayed ten pairs are the ordered coordinate basis. -/
theorem nativePointCoordinates_basis (y : Fin 10) :
    nativePointCoordinates.equiv
      (m22CocodePair (m23PointEmbedding (quotientPoint y)) 0) = Pi.single y 1 :=
  quotientCoordinates_basis y

end Representation.MathieuSmall.M23DegreeSpectrum.InducedHeads.CocodeFiltration.NativeComparison
