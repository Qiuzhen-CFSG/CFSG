module

public import Theory.Representation.SymmetricEightConstituents
public import Theory.AtlasPort.ExceptionalIsomorphisms.Elementary
public import Mathlib.LinearAlgebra.Matrix.Dual

/-!
# The marked outer-conjugate A₈ four-space is the natural dual

The odd permutation (0 1) swaps the middle hyperbolic coordinates of the
six-dimensional deleted module. Comparing with the exterior-square action
shows that it takes the elementary matrix tᵢⱼ(r) to tₛⱼ,ₛᵢ(r), where
s = (0 2)(1 3). The pairing with matrix s is invariant on these generators;
elementary generation then proves invariance for the whole group.

All coordinate checks use the literal deleted and exterior actions of the
ATLAS exceptional-isomorphism port, and are checked by Lean's kernel on
standard basis vectors. The coordinate conventions are adapted from Gerald
Höhn and the ATLAS contributors, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917. The ATLAS Research and Attribution
License 1.0 applies to that port; see LICENSES/ATLAS.txt and
LICENSES/ATLAS-CITATION.cff.

This comparison supplies the natural-plus-dual description of the induced
eight-space in Guralnick--Malle, Classification of 2F-modules I,
Proposition 5.1, HS paragraph, pp.16--17. The source uses the induced natural
A₈ = L₄(2) module; no dimension-only identification is used here.
-/

public section
namespace Representation.SymmetricEightConstituents

open scoped MatrixGroups
open Atlas.Order20160A8 Matrix Matrix.SpecialLinearGroup ClassicalOrthogonal

/-- On the split six-space, (0 1) interchanges the middle hyperbolic pair. -/
private def switch : DeletedEight.D ≃ₗ[ZMod 2] DeletedEight.D :=
  LinearEquiv.piCongrLeft' (ZMod 2) (fun _ : Index 3 => ZMod 2)
    (Equiv.swap (.inl 1) (.inr 1))

-- Check the actual raw words on the six standard basis vectors.
private theorem switch_raw (x : DeletedEight.D) :
    DeletedEight.evenPerm (Equiv.swap 0 1) (DeletedEight.intoEven x) =
      DeletedEight.intoEven (switch x) := by
  have h : (DeletedEight.evenPerm (Equiv.swap 0 1)).toLinearMap.comp
      DeletedEight.intoEven = DeletedEight.intoEven.comp switch.toLinearMap := by
    apply (Pi.basisFun (ZMod 2) (Index 3)).ext
    intro i
    apply Subtype.ext
    have h : ∀ i : Index 3,
        (DeletedEight.evenPerm (Equiv.swap 0 1)
          (DeletedEight.intoEven (Pi.single i 1))).val =
        (DeletedEight.intoEven (switch (Pi.single i 1))).val := by decide +kernel
    simpa only [Pi.basisFun_apply, LinearMap.comp_apply, LinearEquiv.coe_coe] using h i
  exact LinearMap.congr_fun h x

private theorem transposition_orthogonal :
    (DeletedEight.orthogonalHom transposition).val = switch := by
  apply LinearEquiv.ext
  intro x
  apply DeletedEight.splitEquiv.injective
  change DeletedEight.splitEquiv
    (DeletedEight.splitEquiv.symm
      (DeletedEight.quotientPerm transposition (DeletedEight.splitEquiv x))) = _
  rw [LinearEquiv.apply_symm_apply]
  change Submodule.Quotient.mk (DeletedEight.evenPerm transposition
    (DeletedEight.intoEven x)) = Submodule.Quotient.mk (DeletedEight.intoEven (switch x))
  rw [transposition_eq_swap, switch_raw]

private def dualIndex : Equiv.Perm (Fin 4) := Equiv.swap 0 2 * Equiv.swap 1 3

-- The finite calculation uses only the six basis vectors for each transvection.
private theorem switch_elementary (i j : Fin 4) (hij : i ≠ j) (r : ZMod 2) :
    switch * Exterior.onD (transvection hij r) * switch =
      Exterior.onD (transvection (dualIndex.injective.ne hij.symm) r) := by
  apply LinearEquiv.toLinearMap_injective
  apply (Pi.basisFun (ZMod 2) (Index 3)).ext
  intro k
  have h : ∀ (i j : Fin 4) (hij : i ≠ j) (r : ZMod 2) (k : Index 3),
      switch (Exterior.onD (transvection hij r) (switch (Pi.single k 1))) =
        Exterior.onD (transvection (dualIndex.injective.ne hij.symm) r) (Pi.single k 1) := by
    decide +kernel
  simpa only [Pi.basisFun_apply, LinearEquiv.coe_coe, LinearEquiv.mul_apply] using h i j hij r k

private theorem comparison_outer_elementary (i j : Fin 4) (hij : i ≠ j) (r : ZMod 2) :
    comparison (outer (comparison.symm (transvection hij r))) =
      transvection (dualIndex.injective.ne hij.symm) r := by
  apply Exterior.binary_injective
  rw [← comparison_orthogonal, outer_val, map_mul, map_mul,
    comparison_orthogonal, MulEquiv.apply_symm_apply]
  apply Subtype.ext
  change (DeletedEight.orthogonalHom transposition).val *
    Exterior.onD (transvection hij r) * (DeletedEight.orthogonalHom transposition).val = _
  rw [transposition_orthogonal]
  exact switch_elementary i j hij r

private def dualCoordinates : Four ≃ₗ[ZMod 2] Four :=
  LinearEquiv.piCongrLeft' (ZMod 2) (fun _ : Fin 4 => ZMod 2) dualIndex

/-- The nonsingular pairing matching the fixed exceptional comparison. -/
noncomputable def outerDualEquiv : Four ≃ₗ[ZMod 2] Module.Dual (ZMod 2) Four :=
  dualCoordinates.trans (dotProductEquiv (ZMod 2) (Fin 4))

/-- Explicit coordinates of the comparison with the dual four-space. -/
theorem outerDualEquiv_apply (v w : Four) :
    outerDualEquiv v w = w 0 * v 2 + w 1 * v 3 + w 2 * v 0 + w 3 * v 1 := by
  have hi : dualIndex.symm = dualIndex := by decide +kernel
  change dotProduct (fun i => v (dualIndex.symm i)) w = _
  rw [hi]
  simp [dualIndex, Equiv.Perm.mul_apply, Equiv.swap_apply_def, dotProduct,
    Fin.sum_univ_succ, mul_comm, add_assoc]
  ring


-- Bilinearity reduces invariance to pairs of standard basis vectors.
private theorem elementary_pairing (i j : Fin 4) (hij : i ≠ j) (r : ZMod 2)
    (v w : Four) :
    outerDualEquiv ((transvection (dualIndex.injective.ne hij.symm) r).val *ᵥ v)
      ((transvection hij r).val *ᵥ w) = outerDualEquiv v w := by
  let T := (transvection hij r).val.toLin'
  let U := (transvection (dualIndex.injective.ne hij.symm) r).val.toLin'
  have h : (Module.Dual.transpose T).comp (outerDualEquiv.toLinearMap.comp U) =
      outerDualEquiv.toLinearMap := by
    apply (Pi.basisFun (ZMod 2) (Fin 4)).ext
    intro k
    apply (Pi.basisFun (ZMod 2) (Fin 4)).ext
    intro l
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Pi.basisFun_apply,
      Module.Dual.transpose_apply]
    change outerDualEquiv ((transvection (dualIndex.injective.ne hij.symm) r).val *ᵥ
      Pi.single k 1) ((transvection hij r).val *ᵥ Pi.single l 1) =
      outerDualEquiv (Pi.single k 1) (Pi.single l 1)
    have hc : ∀ (i j : Fin 4) (hij : i ≠ j) (r : ZMod 2) (k l : Fin 4),
        outerDualEquiv ((transvection (dualIndex.injective.ne hij.symm) r).val *ᵥ
          Pi.single k 1) ((transvection hij r).val *ᵥ Pi.single l 1) =
          outerDualEquiv (Pi.single k 1) (Pi.single l 1) := by decide +kernel
    exact hc i j hij r k l
  exact LinearMap.congr_fun (LinearMap.congr_fun h v) w

private theorem pairing_invariant (a : alternatingGroup (Fin 8)) (v w : Four) :
    outerDualEquiv (outerNatural a v) (natural a w) = outerDualEquiv v w := by
  have h (g : SL(4, ZMod 2)) : ∀ v w : Four,
      outerDualEquiv (outerNatural (comparison.symm g) v)
        (natural (comparison.symm g) w) = outerDualEquiv v w := by
    refine Atlas.sl_elementary_induction (fun g => ∀ v w : Four,
      outerDualEquiv (outerNatural (comparison.symm g) v)
        (natural (comparison.symm g) w) = outerDualEquiv v w) ?_ ?_ g
    · intro i j hij r v w
      rw [outerNatural_apply, natural_apply, natural_apply,
        comparison_outer_elementary, MulEquiv.apply_symm_apply]
      exact elementary_pairing i j hij r v w
    · intro g h hg hh v w
      rw [map_mul, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]
      rw [hg, hh]
  simpa only [MulEquiv.symm_apply_apply] using h (comparison a) v w

/-- The literal outer-conjugate action is equivalent to the natural dual action. -/
theorem outerDualEquiv_equivariant (a : alternatingGroup (Fin 8)) (v : Four) :
    outerDualEquiv (outerNatural a v) = natural.dual a (outerDualEquiv v) := by
  apply LinearMap.ext
  intro w
  change outerDualEquiv (outerNatural a v) w = outerDualEquiv v (natural a⁻¹ w)
  have h := pairing_invariant a v (natural a⁻¹ w)
  simpa only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
    Module.End.one_apply] using h

end Representation.SymmetricEightConstituents
