module

public import Theory.Representation.Mathieu.SmallModules.M12Recognition.PointClassification.NormalizedInvolution.Certificate.Filtration.Witness

/-!
# Coordinates on the actual eleven-point augmentation module

Append the sum of the first ten coordinates to identify F₂¹⁰ with the
augmentation core on the actual eleven points. The standard vectors become
eᵢ + e₁₀. Computing their images gives the inverse-permutation action matrix,
which is then connected to the published augmentation-to-point equivalence.
Source: the James input to Aschbacher–Smith G.7.3(2), printed p.348/PDF p.359.
-/

@[expose] public section

open Sporadic.Mathieu BinaryPermutation
open Representation.MathieuSmall Representation.MathieuSmall.M12Recognition
open Representation.MathieuSmall.M12Recognition.PointClassification
namespace Representation.MathieuSmall.M12Recognition.PointClassification.NormalizedInvolution.CertificateFiltration

/-- Append the parity coordinate; its inverse forgets point ten. -/
noncomputable def augmentationCoordinates : (Fin 10 → ZMod 2) ≃ₗ[ZMod 2] core (Fin 11) where
  toFun v := ⟨Fin.lastCases (∑ j, v j) v, by
    simp only [mem_core, Fin.sum_univ_castSucc, Fin.lastCases_castSucc,
      Fin.lastCases_last, CharTwo.add_self_eq_zero]⟩
  invFun v j := v.val j.castSucc
  left_inv v := by ext j; simp
  right_inv v := by
    apply Subtype.ext
    ext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · have h := v.property
      rw [mem_core, Fin.sum_univ_castSucc] at h
      change (∑ j : Fin 10, v.val j.castSucc) = v.val (Fin.last 10)
      exact (eq_neg_of_add_eq_zero_left h).trans (CharTwo.neg_eq _)
    · simp
  map_add' v w := by
    apply Subtype.ext
    ext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp only [Pi.add_apply, Finset.sum_add_distrib,
      Fin.lastCases_last, Fin.lastCases_castSucc, Submodule.coe_add]
  map_smul' c v := by
    apply Subtype.ext
    ext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp only [Pi.smul_apply, RingHom.id_apply, Fin.lastCases_last,
      Fin.lastCases_castSucc, Submodule.coe_smul, smul_eq_mul, Finset.mul_sum]

/-- The requested basis is literally eᵢ + e₁₀. -/
theorem augmentationCoordinates_single (j : Fin 10) :
    (augmentationCoordinates (Pi.single j 1)).val = Pi.single j.castSucc 1 + Pi.single (Fin.last 10) 1 := by
  ext i
  refine Fin.lastCases ?_ (fun r => ?_) i
  · change (∑ r : Fin 10, (Pi.single j (1 : ZMod 2)) r) = _
    simp only [Pi.add_apply, Pi.single_eq_same]
    rw [Pi.single_eq_of_ne (Fin.castSucc_ne_last j).symm]
    simp
  · change (Fin.lastCases (motive := fun _ : Fin 11 => ZMod 2) _
      (Pi.single j (1 : ZMod 2) : Fin 10 → ZMod 2) r.castSucc) = _
    rw [Fin.lastCases_castSucc]
    simp only [Pi.add_apply, Pi.single_apply, Fin.castSucc_inj, Fin.castSucc_ne_last,
      ↓reduceIte, add_zero]

/-- Matrix of the actual inverse-permutation action in the parity basis. -/
def augmentationMatrix (g : M11) : Matrix (Fin 10) (Fin 10) (ZMod 2) := fun r j =>
  (if g.val j.castSucc = r.castSucc then 1 else 0) +
  (if g.val (Fin.last 10) = r.castSucc then 1 else 0)

theorem augmentationMatrix_column (g : M11) (j : Fin 10) :
    augmentationCoordinates.symm (augmentationRepresentation g (augmentationCoordinates (Pi.single j 1))) =
      fun r => augmentationMatrix g r j := by
  ext r
  change (augmentationCoordinates (Pi.single j 1)).val (g.val.symm r.castSucc) = _
  rw [augmentationCoordinates_single]
  simp only [Pi.add_apply, Pi.single_apply, augmentationMatrix]
  congr 1 <;> congr 1 <;> exact propext (g.val.symm_apply_eq.trans eq_comm)

theorem augmentationCoordinates_equivariant (g : M11) (v : Fin 10 → ZMod 2) :
    augmentationCoordinates ((augmentationMatrix g).mulVec v) = augmentationRepresentation g (augmentationCoordinates v) := by
  have h : (augmentationMatrix g).mulVecLin =
      augmentationCoordinates.symm.toLinearMap.comp ((augmentationRepresentation g).comp augmentationCoordinates.toLinearMap) := by
    apply (Pi.basisFun (ZMod 2) (Fin 10)).ext
    intro j
    ext r
    simpa only [Pi.basisFun_apply, Matrix.mulVecLin_apply, Matrix.mulVec_single_one,
      LinearMap.comp_apply, LinearEquiv.coe_coe, Matrix.col_apply] using (congrFun (augmentationMatrix_column g j) r).symm
  have hv := LinearMap.congr_fun h v
  exact (congrArg augmentationCoordinates hv).trans (augmentationCoordinates.apply_symm_apply _)

/-- The same coordinates on the published M₁₂ heart restricted to M₁₁. -/
noncomputable def pointCoordinates : (Fin 10 → ZMod 2) ≃ₗ[ZMod 2]
    M12Heart :=
  augmentationCoordinates.trans augmentationEquivPoint.toLinearEquiv

theorem pointCoordinates_equivariant (g : M11) (v : Fin 10 → ZMod 2) :
    pointCoordinates ((augmentationMatrix g).mulVec v) = pointRepresentation g (pointCoordinates v) := by
  change augmentationEquivPoint (augmentationCoordinates ((augmentationMatrix g).mulVec v)) = _
  rw [augmentationCoordinates_equivariant]
  exact LinearMap.congr_fun (augmentationEquivPoint.isIntertwining' g) (augmentationCoordinates v)

open Packed

theorem pointColumns_bound : ∀ (s : Fin 2) (j : Fin 10), pointColumns s j < 2 ^ 10 := by
  decide +kernel

theorem pointColumns_actual : ∀ (s : Fin 2) (r j : Fin 10),
    bit (pointColumns s j) r.val = augmentationMatrix (CertificateData.generator s) r j := by
  unfold augmentationMatrix
  decide +kernel

end Representation.MathieuSmall.M12Recognition.PointClassification.NormalizedInvolution.CertificateFiltration
