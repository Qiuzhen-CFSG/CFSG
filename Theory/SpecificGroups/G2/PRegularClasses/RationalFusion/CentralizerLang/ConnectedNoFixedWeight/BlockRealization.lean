module

public import Theory.SpecificGroups.G2.PRegularClasses.RationalFusion.CentralizerLang.CoordinateModel
public import Theory.SpecificGroups.G2.PRegularClasses.RationalFusion.CentralizerLang.ConnectedNoFixedWeight.Restriction
public import Theory.SpecificGroups.G2.PRegularClasses.RationalFusion.CentralizerLang.ConnectedNoFixedWeight.BlockRealization.Algebra

/-!
# A regular surjection from Peirce blocks to the octonion centralizer

The determinant-one action constructed in `BlockRealization.Algebra` has
polynomial entries: it uses the matrix on one Peirce space and its cofactors
on the opposite space. Evaluation commutes with these formulas. The extra
GL₈ coordinate is the determinant of the inverse action, which is again
polynomial because inversion in SL₃ is the adjugate.

The resulting regular morphism lands in the literal octonion torus
centralizer. When `l ≠ 1`, `m ≠ 1`, and `l ≠ m` in characteristic two, the
published faithful restriction makes this morphism surjective. No condition
on equality among the three Peirce weights is imposed, so repeated weights
and the scalar order-three SL₃ case are included.

This is the realization step for Steinberg 8.5 and 12.5
(`refs/KGroup/GLS3/Chapter2St2.tex`). The multiplication table and
coordinate model come from the licensed ATLAS port (`LICENSES/ATLAS.txt`).
-/

@[expose] public section

open Matrix Atlas.SplitOctonion Theory.AlgebraicGroup
open scoped MatrixGroups
namespace Atlas.G2.PRegularClasses.RationalFusion.CentralizerLang.NoFixedWeight.BlockRealization
section
variable {R S : Type*} [CommRing R] [CommRing S]

def blockMatrix (A : Matrix (Fin 3) (Fin 3) R) : Matrix (Fin 8) (Fin 8) R :=
  fun i j => blockLinear A (basisVector j) i

theorem map_blockLinear (f : R →+* S) (A : Matrix (Fin 3) (Fin 3) R) (x : Carrier R) :
    (fun i => f (blockLinear A x i)) = blockLinear (A.map f) (f ∘ x) := by
  ext i
  fin_cases i <;>
    simp [blockLinear,pack,cofactor,Matrix.adjugate_fin_three,
      Matrix.mulVec,dotProduct,Fin.sum_univ_three,Function.comp_def]

theorem map_blockMatrix (f : R →+* S) (A : Matrix (Fin 3) (Fin 3) R) :
    (blockMatrix A).map f = blockMatrix (A.map f) := by
  ext i j
  have hf : f ∘ (basisVector j : Carrier R) = (basisVector j : Carrier S) := by
    ext k
    by_cases h : k = j <;> simp [basisVector,h]
  simpa only [blockMatrix,Matrix.map_apply,hf] using
    congrFun (map_blockLinear f A (basisVector j)) i

end
section
variable {K : Type*} [Field K]

theorem coordinateMatrix_blockHom (A : SL(3,K)) :
    (FieldExtension.coordinateMatrix (blockHom A) : Matrix (Fin 8) (Fin 8) K) =
      blockMatrix A.val := by
  ext i j
  rw [coordinateMatrix_entry]
  rfl

theorem coordinateMatrix_inverse (g : Model K) :
    FieldExtension.coordinateMatrix g⁻¹ = (FieldExtension.coordinateMatrix g)⁻¹ := by
  change (Matrix.GeneralLinearGroup.toLin' (Pi.basisFun K (Fin 8))).symm
      (LinearMap.GeneralLinearGroup.ofLinearEquiv g.val.symm) = _
  change (Matrix.GeneralLinearGroup.toLin' (Pi.basisFun K (Fin 8))).symm
    (LinearMap.GeneralLinearGroup.ofLinearEquiv g.val)⁻¹ = _
  rw [map_inv]
  rfl

theorem blockMatrix_inverse_det (A : SL(3,K)) :
    (blockMatrix (A⁻¹).val).det = (blockMatrix A.val).det⁻¹ := by
  rw [← coordinateMatrix_blockHom, map_inv, coordinateMatrix_inverse,
    Matrix.GeneralLinearGroup.coe_inv, Matrix.det_nonsing_inv, Ring.inverse_eq_inv,
    coordinateMatrix_blockHom]

end
noncomputable section
variable {K : Type*} [Field K] [IsAlgClosed K]

def blockPoint (l m : Kˣ)
    (p : Variety.Point (blockVariety (peirceWeights l m) (peirceWeights_prod l m))) :
    Variety.Point (centralizerVariety (torus l m)) :=
  (centralizerPointEquiv (torus l m)).symm
    ⟨blockHom (blockPointEquiv _ _ p).val, blockHom_centralizes l m (blockPointEquiv _ _ p)⟩

theorem blockPoint_entry (l m : Kˣ)
    (p : Variety.Point (blockVariety (peirceWeights l m) (peirceWeights_prod l m)))
    (i j : Fin 8) :
    (blockPoint l m p).val (Sum.inl (i,j)) =
      blockMatrix (blockPointEquiv _ _ p).val.val i j := by
  rw [← centralizerPointEquiv_entry]
  change (FieldExtension.coordinateMatrix
    ((centralizerPointEquiv (torus l m)) ((centralizerPointEquiv (torus l m)).symm _)).val :
    Matrix (Fin 8) (Fin 8) K) i j = _
  rw [MulEquiv.apply_symm_apply, coordinateMatrix_blockHom]

theorem blockPoint_scalar (l m : Kˣ)
    (p : Variety.Point (blockVariety (peirceWeights l m) (peirceWeights_prod l m))) :
    (blockPoint l m p).val (Sum.inr PUnit.unit) =
      (blockMatrix ((blockPointEquiv _ _ p).val⁻¹).val).det := by
  rw [centralizerPointEquiv_scalar]
  change (FieldExtension.coordinateMatrix
    ((centralizerPointEquiv (torus l m)) ((centralizerPointEquiv (torus l m)).symm _)).val :
    Matrix (Fin 8) (Fin 8) K).det⁻¹ = _
  rw [MulEquiv.apply_symm_apply, coordinateMatrix_blockHom, blockMatrix_inverse_det]

theorem eval_entryMatrix (l m : Kˣ)
    (p : Variety.Point (blockVariety (peirceWeights l m) (peirceWeights_prod l m))) :
    (slEntryMatrix 3).map (MvPolynomial.eval p.val) = (blockPointEquiv _ _ p).val.val := by
  ext i j
  rw [blockPointEquiv_entry]
  simp [slEntryMatrix]

end
end Atlas.G2.PRegularClasses.RationalFusion.CentralizerLang.NoFixedWeight.BlockRealization

namespace Atlas.G2.PRegularClasses.RationalFusion.CentralizerLang.NoFixedWeight
open BlockRealization
noncomputable section
variable {K : Type*} [Field K] [IsAlgClosed K]

/-- Polynomial realization of the actual determinant-one blocks in the octonion centralizer. -/
def blockParametrization (l m : Kˣ) :
    Variety.Morphism (blockVariety (peirceWeights l m) (peirceWeights_prod l m))
      (centralizerVariety (torus l m)) where
  toFun := blockPoint l m
  regular := by
    rintro (⟨i,j⟩ | ⟨⟩)
    · refine ⟨blockMatrix (slEntryMatrix 3) i j, ?_⟩
      intro p
      rw [blockPoint_entry]
      have h := map_blockMatrix (MvPolynomial.eval p.val) (slEntryMatrix 3)
      rw [eval_entryMatrix l m p] at h
      exact (congrArg (fun M => M i j) h).symm
    · refine ⟨(blockMatrix (slEntryMatrix 3).adjugate).det, ?_⟩
      intro p
      rw [blockPoint_scalar]
      change (blockMatrix ((blockPointEquiv _ _ p).val.val).adjugate).det =
        (MvPolynomial.eval p.val) (blockMatrix (slEntryMatrix 3).adjugate).det
      rw [RingHom.map_det]
      change _ = ((blockMatrix (slEntryMatrix 3).adjugate).map (MvPolynomial.eval p.val)).det
      rw [map_blockMatrix]
      have h := (MvPolynomial.eval p.val).map_adjugate (slEntryMatrix 3)
      change ((slEntryMatrix 3).adjugate).map (MvPolynomial.eval p.val) =
        ((slEntryMatrix 3).map (MvPolynomial.eval p.val)).adjugate at h
      rw [h, eval_entryMatrix l m p]

variable [CharP K 2]

/-- Restriction recovers every entry of the block used to construct the automorphism. -/
theorem centralizerRestriction_blockParametrization (l m : Kˣ)
    (hl : l ≠ 1) (hm : m ≠ 1) (hlm : l ≠ m)
    (p : Variety.Point (blockVariety (peirceWeights l m) (peirceWeights_prod l m))) :
    (centralizerRestriction l m hl hm hlm).toFun ((blockParametrization l m).toFun p) = p := by
  apply (blockPointEquiv _ _).injective
  change (blockPointEquiv _ _) ((blockPointEquiv _ _).symm _) = _
  rw [MulEquiv.apply_symm_apply]
  apply Subtype.ext
  apply Subtype.ext
  change peirceMatrix (centralizerPointEquiv _ (blockPoint l m p)).val = _
  simp only [blockPoint, MulEquiv.apply_symm_apply]
  exact peirceMatrix_blockHom _

/-- Every element of the literal centralizer is realized by its determinant-one Peirce block. -/
theorem blockParametrization_surjective (l m : Kˣ)
    (hl : l ≠ 1) (hm : m ≠ 1) (hlm : l ≠ m) :
    Function.Surjective (blockParametrization l m).toFun := by
  intro q
  refine ⟨(centralizerRestriction l m hl hm hlm).toFun q, ?_⟩
  apply centralizerRestriction_injective l m hl hm hlm
  exact centralizerRestriction_blockParametrization l m hl hm hlm _

end
end Atlas.G2.PRegularClasses.RationalFusion.CentralizerLang.NoFixedWeight
