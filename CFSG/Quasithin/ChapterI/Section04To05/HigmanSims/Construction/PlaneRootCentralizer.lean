module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.PlaneMatrices
public import Theory.LinearAlgebra.ZModFourTransvectionFixedSquares

/-!
# A plane lift does not centralize the opposite cyclic-four root

The actual action of a second plane lift on the whole normalizer core has
determinant one and the standard binary reduction. The fixed-square
calculation therefore excludes centralization of any original core element
whose square is the first canonical seed point. This is the nonabelian
relation needed in the full order32 centralizer of a nonseed eight.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.HigmanSims
open BinaryPlane
variable {G : Type*} [Group G] [Finite G] {z : G} {V : Subgroup G}

/-- The actual second plane involution does not centralize a square root
of the first marked point anywhere in the whole original cyclic-four core. -/
theorem TypeAt.plane_root_not_commute (h : TypeAt z V)
    (e : pCore 2 (normalizer (V : Set G)) ≃* Multiplicative (Fin 3 → ZMod 4))
    (b : normalizer (V : Set G)) (hb : b ^ 2 = 1)
    (haction : V.normalizerMonoidHom b = betaAt (h.seedCoordinates e))
    (c : pCore 2 (normalizer (V : Set G)))
    (hc : (((c : normalizer (V : Set G)) : G) ^ 2) =
      ((h.seedCoordinates e).symm e0 : G)) :
    ¬ Commute (b : G) ((c : normalizer (V : Set G)) : G) := by
  let M := normalizer (V : Set G)
  let P := pCore 2 M
  let B := h.coreMatrixAction e b
  have hB : B ^ 2 = 1 := by rw [← map_pow, hb, map_one]
  have hroot : c ^ 2 = e.symm (Multiplicative.ofAdd ![2, 0, 0]) := by
    apply Subtype.ext
    apply Subtype.ext
    rw [h.seedCoordinates_symm_apply e e0] at hc
    have he : (fun i => binaryDouble (e0.toAdd i)) = ![2, 0, 0] := by decide +kernel
    rw [he] at hc
    exact hc
  have hdouble : (e c).toAdd + (e c).toAdd = ![2, 0, 0] := by
    have hh := congrArg (fun q : P => (e q).toAdd) hroot
    simpa only [pow_two, map_mul, toAdd_mul, e.apply_symm_apply, toAdd_ofAdd] using hh
  intro hcomm
  have hconj : MulAut.conjNormal b c = c := by
    apply Subtype.ext
    apply Subtype.ext
    change (b : G) * ((c : M) : G) * (b : G)⁻¹ = ((c : M) : G)
    rw [hcomm.eq, mul_inv_cancel_right]
  have hfixed : B.mulVec (e c).toAdd = (e c).toAdd := by
    rw [h.coreMatrixAction_apply, hconj]
  exact ZModFourTransvectionFixedSquares.not_fixed_of_double_first B hB
    (h.coreMatrixAction_det e b) (h.second_plane_matrix_reduction e b haction)
    (e c).toAdd hdouble hfixed

end CFSG.Quasithin.HigmanSims
