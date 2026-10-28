/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/IcosianMonomialCentralizer.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
Source revision: 8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
-/
module

public import Theory.AtlasPort.Janko2.Conway.IcosianProjectiveKernel
public import Theory.AtlasPort.Janko2.Conway.IcosianReflectionDiagonalImage

/-!
# IcosianMonomialCentralizer

Commutation with axis signs forces a right-quaternion-linear endomorphism to be diagonal.
Coordinate swaps and paired quaternion units force its diagonal entries to be one golden-field scalar.

Source: Gerald Höhn, `Atlas/Conway/IcosianMonomialCentralizer.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and the definition bodies
needed by the source coordinate calculations; source statements are preserved.
-/

set_option backward.isDefEq.respectTransparency false
public section

noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Lattices

/-- An endomorphism commuting with the three axis signs is diagonal. -/
theorem icosian_linear_diagonal_of_axis_commutation
    (f : IcosianRationalCoordinates →ₗ[ℚ] IcosianRationalCoordinates)
    (hf : ∀ a x, f (icosianRightMul x a)=icosianRightMul (f x) a)
    (hc : ∀ i x, f ((icosianAxisReflection i).val x)=(icosianAxisReflection i).val (f x)) :
    ∃ q : Fin 3 → IcosianQuaternion, ∀ x i, f x i=q i*x i := by
  let q : Fin 3 → IcosianQuaternion := fun i => f (Pi.single i 1) i
  have he (i j : Fin 3) (hji : j≠i) : f (Pi.single i 1) j=0 := by
    have hs : (icosianAxisReflection i).val (Pi.single i 1 : IcosianRationalCoordinates)=
        -(Pi.single i 1 : IcosianRationalCoordinates) := by
      funext k
      rw [icosianAxisReflection_apply]
      by_cases hk : k=i <;> simp [hk]
    have h := congrFun (hc i (Pi.single i 1)) j
    rw [hs,map_neg,icosianAxisReflection_apply,if_neg hji] at h
    apply QuaternionAlgebra.ext
    · exact CharZero.neg_eq_self_iff.mp (congrArg QuaternionAlgebra.re h)
    · exact CharZero.neg_eq_self_iff.mp (congrArg QuaternionAlgebra.imI h)
    · exact CharZero.neg_eq_self_iff.mp (congrArg QuaternionAlgebra.imJ h)
    · exact CharZero.neg_eq_self_iff.mp (congrArg QuaternionAlgebra.imK h)
  refine ⟨q,?_⟩
  intro x i
  have hx : x=icosianRightMul (Pi.single 0 1) (x 0)+
      icosianRightMul (Pi.single 1 1) (x 1)+icosianRightMul (Pi.single 2 1) (x 2) := by
    funext j
    fin_cases j <;> simp [icosianRightMul]
  conv_lhs => rw [hx]
  simp only [map_add,hf,Pi.add_apply,icosianRightMul]
  fin_cases i <;> simp [q,he]

/-- The actual swaps and paired quaternion units force a diagonal endomorphism
to be a scalar over the golden field. This statement includes noninvertible maps. -/
theorem icosian_linear_scalar_of_bounded_monomials
    (f : IcosianRationalCoordinates →ₗ[ℚ] IcosianRationalCoordinates)
    (hf : ∀ a x, f (icosianRightMul x a)=icosianRightMul (f x) a)
    (hs : ∀ i x, f ((icosianAxisReflection i).val x)=(icosianAxisReflection i).val (f x))
    (hp : ∀ p x, f ((icosianReflectionEdgeGenerator 0 p).val x)=
      (icosianReflectionEdgeGenerator 0 p).val (f x))
    (hu : ∀ k x, f ((icosianReflectionEdgeWord k 0).val x)=
      (icosianReflectionEdgeWord k 0).val (f x)) :
    ∃ a : GoldenRational, ∀ x i, f x i=(a : IcosianQuaternion)*x i := by
  obtain ⟨q,hq⟩ := icosian_linear_diagonal_of_axis_commutation f hf hs
  have heq (p : Fin 2) : q 0=q (icosianReflectionEdgePartner p) := by
    have h := congrFun (hp p
      (Pi.single (icosianReflectionEdgePartner p) 1 : IcosianRationalCoordinates)) 0
    rw [icosianReflectionSwap_linear] at h
    simp only [icosianReflectionSwapMonomial_apply,hq] at h
    simpa [Equiv.swap_apply_left,icosianReflectionEdgePartner_ne_zero] using h
  have hcommon : ∀ i, q i=q 0 := by
    intro i
    fin_cases i
    · rfl
    · exact (heq 0).symm
    · exact (heq 1).symm
  have hunit (k : Fin 3) : q 0*(icosianReflectionEdgeUnitIntegral k).val=
      (icosianReflectionEdgeUnitIntegral k).val*q 0 := by
    have h := congrFun (hu k (Pi.single 0 1 : IcosianRationalCoordinates)) 0
    rw [icosianReflectionEdgeWord_linear] at h
    simpa only [icosianReflectionEdgeMonomial_apply,hq,icosianReflectionEdgeDiagonalRaw,
      if_pos rfl,Pi.single_eq_same,mul_one,ite_true] using h
  have hi : q 0*icosianI=icosianI*q 0 := by
    have h := hunit 1
    rw [icosianReflectionEdgeUnit_I] at h
    simpa only [mul_neg,neg_mul,neg_inj] using h
  have hj : q 0*icosianJ=icosianJ*q 0 := by
    simpa only [icosianReflectionEdgeUnit_J] using hunit 2
  have hscalar := icosian_scalar_of_commutes_I_J (q 0) hi hj
  exact ⟨(q 0).re, fun x i => by rw [hq,hcommon]; exact congrArg (fun z : IcosianQuaternion => z*x i) hscalar⟩

end Atlas.Conway
