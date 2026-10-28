/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Lattices/IcosianRootNormFibers.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Lattices.IcosianRoots
public import Theory.AtlasPort.Janko2.Codes.IcosianDeterminantGlue

/-!
# Icosian Root Norm Fibers

Fixed-norm roots correspond to determinant-glue words equipped with
one scalar norm-and-reduction fiber in each coordinate. Reconstruction
and reduction are inverse, giving the structural counting equivalence.

Source: Gerald Höhn, ATLAS, `Atlas/Lattices/IcosianRootNormFibers.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0: module/public imports and exposed public
coordinate definitions; concrete carriers and theorem statements are retained.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Lattices
open Atlas.Algebra Atlas.Codes
open scoped Matrix BigOperators Quaternion

abbrev IcosianRootsWithNorms (n : Fin 3 → GoldenRational) :=
  {r : IcosianRoot // ∀ i,icosianNorm (r.val i).val=n i}

abbrev IcosianScalarNormReductionFiber (t : GoldenRational) (m : IcosianMatrix) :=
  {x : icosianOrder // icosianNorm x.val=t ∧ icosianModuloTwo x=m}

def icosianScalarNormReductionFiberEquiv (t : GoldenRational) (m : IcosianMatrix) :
    IcosianScalarNormReductionFiber t m ≃
      {x : {x : icosianOrder // icosianNorm x.val=t} // icosianModuloTwo x.val=m} where
  toFun x := ⟨⟨x.val,x.property.1⟩,x.property.2⟩
  invFun x := ⟨x.val.val,x.val.property,x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem icosianNorm_det_of_integral_value (t : GoldenInteger) (x : icosianOrder)
    (hx : icosianNorm x.val=goldenIntegerToRational t) :
    Matrix.det (icosianModuloTwo x)=goldenModuloTwo t := by
  rw [icosianModuloTwo_det]
  congr 1
  apply goldenIntegerToRational_injective
  rw [icosianIntegralNorm_spec]
  exact hx

theorem icosianMatrixGlue_common_row (m : icosianMatrixGlue GoldenFour) (i : Fin 3) :
    (fun j => m.val i 1 j)=(fun j => m.val 0 1 j) := by
  funext j
  have h := (icosianMatrixGlue_constraints _).mp m.property j
  fin_cases i <;> simp_all

theorem icosianMatrixGlue_row_ne_zero_of_det (m : icosianMatrixGlue GoldenFour)
    (h : ∃ i,Matrix.det (m.val i)≠0) : (fun j => m.val 0 1 j)≠0 := by
  rintro hz
  obtain ⟨i,hi⟩ := h
  have he : (fun j => m.val i 1 j)=0 := (icosianMatrixGlue_common_row m i).trans hz
  apply hi
  rw [Matrix.det_fin_two]
  rw [congrFun he 0,congrFun he 1]
  simp

theorem icosianDeterminantGlue_block_ne_zero (d : Fin 3 → GoldenFour)
    (m : IcosianDeterminantGlue d) (i : Fin 3) : m.val.val i≠0 := by
  intro h
  apply m.property.2
  rw [← icosianMatrixGlue_common_row m.val i]
  funext j
  rw [h]
  rfl

theorem icosianRoot_norm_of_sum (x : IcosianCoordinates)
    (hs : (∑ i,icosianNorm (x i).val)=4) :
    icosianHermitian (icosianCoordinateEmbedding x) (icosianCoordinateEmbedding x)=2 := by
  have he : icosianHermitian (icosianCoordinateEmbedding x) (icosianCoordinateEmbedding x)=
      (1/2 : ℚ) • ((∑ i,icosianNorm (x i).val : GoldenRational) : IcosianQuaternion) := by
    simp [icosianHermitian,icosianCoordinateEmbedding,Quaternion.star_mul_self,
      icosianNorm,Fin.sum_univ_succ]
  rw [he,hs]
  ext <;> norm_num [QuaternionAlgebra.re_ofNat, QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat] <;> rfl

def icosianRootNormReduction (n : Fin 3 → GoldenRational) (d : Fin 3 → GoldenFour)
    (hd : ∀ i (x : icosianOrder),icosianNorm x.val=n i → Matrix.det (icosianModuloTwo x)=d i)
    (hne : ∃ i,d i≠0) (r : IcosianRootsWithNorms n) : IcosianDeterminantGlue d := by
  let m : icosianMatrixGlue GoldenFour :=
    ⟨fun i => icosianModuloTwo (r.val.val i),
      (icosianLeechModule_matrix_glue _).mp r.val.property.1⟩
  have hm (i : Fin 3) : Matrix.det (m.val i)=d i := hd i _ (r.property i)
  refine ⟨m,hm,icosianMatrixGlue_row_ne_zero_of_det m ?_⟩
  obtain ⟨i,hi⟩ := hne
  exact ⟨i,by rw [hm]; exact hi⟩

def icosianRootFromNormFibers (n : Fin 3 → GoldenRational) (d : Fin 3 → GoldenFour)
    (hn : (∑ i,n i)=4) (m : IcosianDeterminantGlue d)
    (x : ∀ i,IcosianScalarNormReductionFiber (n i) (m.val.val i)) : IcosianRootsWithNorms n := by
  let v : IcosianCoordinates := fun i => (x i).val
  have hL : v∈icosianLeechModule := by
    apply (icosianLeechModule_matrix_glue v).mpr
    have he : (fun i => icosianModuloTwo (v i))=m.val.val := funext (fun i => (x i).property.2)
    rw [he]
    exact m.val.property
  have hN (i : Fin 3) : icosianNorm (v i).val=n i := (x i).property.1
  exact ⟨⟨v,hL,icosianRoot_norm_of_sum v (by simpa only [hN] using hn)⟩,hN⟩

/-- The fiber over an actual matrix-glue word is exactly the product of its three
actual integral scalar norm-and-reduction fibers. -/
def icosianRootNormReductionFiberEquiv
    (n : Fin 3 → GoldenRational) (d : Fin 3 → GoldenFour) (hn : (∑ i,n i)=4)
    (hd : ∀ i (x : icosianOrder),icosianNorm x.val=n i → Matrix.det (icosianModuloTwo x)=d i)
    (hne : ∃ i,d i≠0) (m : IcosianDeterminantGlue d) :
    {r : IcosianRootsWithNorms n // icosianRootNormReduction n d hd hne r=m} ≃
      (∀ i,IcosianScalarNormReductionFiber (n i) (m.val.val i)) where
  toFun r i := ⟨r.val.val.val i,r.val.property i,by
    have h := congrArg (fun a : IcosianDeterminantGlue d => a.val.val i) r.property
    exact h⟩
  invFun x := ⟨icosianRootFromNormFibers n d hn m x,by
    apply Subtype.ext
    apply Subtype.ext
    funext i
    exact (x i).property.2⟩
  left_inv r := by apply Subtype.ext; apply Subtype.ext; apply Subtype.ext; rfl
  right_inv x := by funext i; apply Subtype.ext; rfl

/-- Structural root coordinates over the 240-word determinant glue. -/
def icosianRootsWithNormsEquiv
    (n : Fin 3 → GoldenRational) (d : Fin 3 → GoldenFour) (hn : (∑ i,n i)=4)
    (hd : ∀ i (x : icosianOrder),icosianNorm x.val=n i → Matrix.det (icosianModuloTwo x)=d i)
    (hne : ∃ i,d i≠0) : IcosianRootsWithNorms n ≃
      (m : IcosianDeterminantGlue d) ×
        (∀ i,IcosianScalarNormReductionFiber (n i) (m.val.val i)) :=
  (Equiv.sigmaPreimageEquiv (icosianRootNormReduction n d hd hne)).symm.trans
    (Equiv.sigmaCongrRight (icosianRootNormReductionFiberEquiv n d hn hd hne))

end Atlas.Lattices
