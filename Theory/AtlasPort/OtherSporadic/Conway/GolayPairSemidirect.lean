/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/GolayPairSemidirect.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.GolayTwoCoordinateFiber
public import Theory.AtlasPort.OtherSporadic.Mathieu.Mathieu24PointOrders
/-!
Golay coordinate restrictions and signed-support transport in the Leech lattice.
The proofs retain the explicit code maps and coordinate identities used by the stabilizer geometry.

Source: Gerald Höhn, `Atlas/Conway/GolayPairSemidirect.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies,
preserving the source namespaces and cross-module coordinate reductions.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices

abbrev GolayPairKernel (e : Fin 2 ↪ Omega) := (golayTwoCoordinateProjection (e 0) (e 1)).ker

theorem orderedPair_fixes (e : Fin 2 ↪ Omega) (g : orderedPointStabilizer e) (k : Fin 2) :
    g.val.val (e k) = e k :=
  ((mem_fixingSubgroup_iff Mathieu24CodeModel).mp g.prop) (e k) (Set.mem_range_self k)

theorem orderedPair_inv_fixes (e : Fin 2 ↪ Omega) (g : orderedPointStabilizer e) (k : Fin 2) :
    g.val.val.symm (e k) = e k := by
  rw [Equiv.symm_apply_eq]
  exact (orderedPair_fixes e g k).symm

def golayPairKernelMap (e : Fin 2 ↪ Omega) (g : orderedPointStabilizer e) :
    GolayPairKernel e →ₗ[Bit] GolayPairKernel e where
  toFun c := ⟨golayPermutationEquiv g.val c.val,by
    change (c.val.val (g.val.val.symm (e 0)),c.val.val (g.val.val.symm (e 1))) = (0,0)
    rw [orderedPair_inv_fixes,orderedPair_inv_fixes]
    exact c.prop⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def golayPairKernelEquiv (e : Fin 2 ↪ Omega) (g : orderedPointStabilizer e) :
    GolayPairKernel e ≃ₗ[Bit] GolayPairKernel e where
  toLinearMap := golayPairKernelMap e g
  invFun := golayPairKernelMap e g⁻¹
  left_inv c := by
    apply Subtype.ext; apply Subtype.ext; funext i
    change c.val.val (g.val.val.symm (g.val.val i)) = c.val.val i
    rw [Equiv.symm_apply_apply]
  right_inv c := by
    apply Subtype.ext; apply Subtype.ext; funext i
    change c.val.val (g.val.val (g.val.val.symm i)) = c.val.val i
    rw [Equiv.apply_symm_apply]

def golayPairKernelAction (e : Fin 2 ↪ Omega) :
    orderedPointStabilizer e →* MulAut (Multiplicative (GolayPairKernel e)) where
  toFun g := (golayPairKernelEquiv e g).toAddEquiv.toMultiplicative
  map_one' := by apply MulEquiv.ext; intro c; rfl
  map_mul' g h := by apply MulEquiv.ext; intro c; rfl

abbrev GolayPairMonomialGroup (e : Fin 2 ↪ Omega) :=
  Multiplicative (GolayPairKernel e) ⋊[golayPairKernelAction e] orderedPointStabilizer e

def golayPairSignInclusion (e : Fin 2 ↪ Omega) :
    Multiplicative (GolayPairKernel e) →* Multiplicative golay :=
  (GolayPairKernel e).subtype.toAddMonoidHom.toMultiplicative

def pairMonomialInclusion (e : Fin 2 ↪ Omega) : GolayPairMonomialGroup e →* GolayMonomialGroup :=
  SemidirectProduct.map (golayPairSignInclusion e) (orderedPointStabilizer e).subtype
    (by intro g; rfl)

theorem pairMonomialInclusion_injective (e : Fin 2 ↪ Omega) :
    Function.Injective (pairMonomialInclusion e) := by
  intro a b he
  have hl := congrArg SemidirectProduct.left he
  have hr := congrArg SemidirectProduct.right he
  apply SemidirectProduct.ext
  · exact Subtype.ext hl
  · exact Subtype.ext hr

theorem golayPairMonomialGroup_order (e : Fin 2 ↪ Omega) :
    Nat.card (GolayPairMonomialGroup e) = 1024 * 443520 := by
  rw [SemidirectProduct.card,mathieu24_two_point_order,
    Nat.card_congr (Multiplicative.toAdd : Multiplicative (GolayPairKernel e) ≃ GolayPairKernel e),
    golay_two_coordinate_kernel_card (e 0) (e 1) (e.injective.ne (by decide))]

end Atlas.Conway
