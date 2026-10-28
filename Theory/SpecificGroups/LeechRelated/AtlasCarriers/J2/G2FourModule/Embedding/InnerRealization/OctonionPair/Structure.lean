module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.G2FourModule.Embedding.InnerRealization.OctonionPair.Data
public import Theory.AtlasPort.LinearGroups.G2.FieldTransport

/-!
# Faithful coordinate matrices for the octonion model

The coordinate matrix is a faithful monoid homomorphism and carries field
transport to entrywise transport. A pair of inverse matrices preserving the
64 basis products therefore defines an element of the literal G₂ model.
These lemmas connect the finite certificates to actual octonion automorphisms.
The octonion conventions and attribution are those of the imported ATLAS modules.
-/

@[expose] public section

open Atlas.SplitOctonion
namespace Sporadic.LeechRelated.J2.G2FourModule.Embedding.InnerRealization.OctonionPair

def matrixHom {K : Type*} [Field K] : Atlas.G2.Model K →* Matrix (Fin 8) (Fin 8) K where
  toFun g := LinearMap.toMatrix' g.val.toLinearMap
  map_one' := LinearMap.toMatrix'_one
  map_mul' g h := LinearMap.toMatrix'_mul g.val.toLinearMap h.val.toLinearMap

theorem matrixHom_injective {K : Type*} [Field K] :
    Function.Injective (matrixHom (K := K)) := by
  intro g h he
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  exact LinearMap.toMatrix'.injective he

theorem matrixHom_fieldEquiv {K L : Type*} [Field K] [Field L]
    (e : K ≃+* L) (g : Atlas.G2.Model K) :
    matrixHom (Atlas.G2.fieldEquiv e g) = (matrixHom g).map e := by
  ext i j
  change (Atlas.G2.fieldEquiv e g).val (basisVector j) i = e (g.val (basisVector j) i)
  have hb : mapCoefficients e (basisVector j) = basisVector j := by
    ext k
    simp [mapCoefficients, basisVector, Pi.single_apply]
  rw [← hb, Atlas.G2.fieldEquiv_action]
  rfl

def ofMatrices (m n : Mat) (hnm : n * m = 1) (hmn : m * n = 1)
    (hm : ∀ i j, m.mulVecLin (mul (basisVector i) (basisVector j)) =
      mul (m.mulVecLin (basisVector i)) (m.mulVecLin (basisVector j))) : Atlas.G2.Model Coeff :=
  ⟨Matrix.toLin'OfInv hnm hmn, map_mul_of_basis m.mulVecLin hm⟩

theorem matrixHom_ofMatrices (m n : Mat) (hnm : n * m = 1) (hmn : m * n = 1)
    (hm : ∀ i j, m.mulVecLin (mul (basisVector i) (basisVector j)) =
      mul (m.mulVecLin (basisVector i)) (m.mulVecLin (basisVector j))) :
    matrixHom (ofMatrices m n hnm hmn hm) = m :=
  LinearMap.toMatrix'_toLin' m

theorem matrixHom_ofMatrices_inv (m n : Mat) (hnm : n * m = 1) (hmn : m * n = 1)
    (hm : ∀ i j, m.mulVecLin (mul (basisVector i) (basisVector j)) =
      mul (m.mulVecLin (basisVector i)) (m.mulVecLin (basisVector j))) :
    matrixHom (ofMatrices m n hnm hmn hm)⁻¹ = n :=
  LinearMap.toMatrix'_toLin' n

end Sporadic.LeechRelated.J2.G2FourModule.Embedding.InnerRealization.OctonionPair
