module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Universal.Coroots
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Basic
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Universal.IsogenyConstruction.PointKernel.CorootCoordinates
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Universal.IsogenyConstruction.PointKernel.TorusLift

/-!
# Reduction of the incoming F4 point kernel to lifted coroots

Suppose the four standard displayed F4 coroots form a torus isomorphism.
If they lift through an incoming isogeny with possibly different powers of
two on their parameters, their product is bijective after composition with
the torus map. The torus calculation then proves injectivity of that map.
Containment of the ambient kernel in the connected torus lift completes
the point-kernel argument.

The two geometric premises remain explicit here: containment of the kernel
and construction of the four characteristic-power coroot lifts. Neither a
source root model nor a universal cover is assumed. The simple roots used
are `f4SimpleRoot`, from the standard displayed base, independently of the
model's chosen base. No regular inverse to an inseparable map is asserted.

Source: the fundamental-coroot criterion in GLS3, Theorem 1.12.5(b),
`refs/KGroup/GLS3/Chapter1.tex`, Sections 1.9--1.12.
-/

public section
universe u

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

namespace RootSystemModel
open StandardRootSystem
variable [CharP k 2]

noncomputable local instance modelTorusAlgebraicGroup
    {G : Variety k} [AlgebraicGroup G]
    (M : RootSystemModel typeF4RootPairingULift G) :
    AlgebraicGroup M.torus.carrierVariety := M.torus.carrierAlgebraicGroup

/-- Characteristic-power lifts of the four coroots force injectivity on the source torus. -/
theorem f4_torusMap_injective_of_coroot_lifts
    {G S : Variety k} [AlgebraicGroup G] [AlgebraicGroup S]
    (M : RootSystemModel typeF4RootPairingULift G)
    (hS : IsTorus S)
    (q : Morphism S M.torus.carrierVariety) (hfinite : Finite q.kernel)
    (e : @Iso k _ (dVariety k 4) M.torus.carrierVariety _ M.torus.carrierAlgebraicGroup)
    (he : e.hom = M.f4CorootProduct)
    (μ : Fin 4 → Morphism (KMult k) S) (a : Fin 4 → ℕ)
    (hμ : ∀ i t, q.onPoints ((μ i).onPoints t) =
      (M.rootData.rootCocharacter (M.f4SimpleRoot i)).onPoints (t ^ (2 ^ a i))) :
    Function.Injective q.onPoints := by
  let p := cocharacterTupleProduct hS μ
  let δ : Variety.Point (dVariety k 4) → Variety.Point (dVariety k 4) :=
    fun x => (dPointEquiv 4).symm (fun i => dPointEquiv 4 x i ^ (2 ^ a i))
  have hδ : Function.Bijective δ := diagonal_primePower_bijective 2 a
  have hcoordinate (i : Fin 4) (x : Variety.Point (dVariety k 4)) :
      (dCoordinateCharacter 4 i).onPoints (δ x) =
        ((dCoordinateCharacter 4 i).onPoints x) ^ (2 ^ a i) := by
    apply (dPointEquiv 1).injective
    funext j
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    simp only [dCoordinateCharacter_apply, dPointEquiv_pow, Pi.pow_apply]
    exact congrFun ((dPointEquiv 4).apply_symm_apply _) i
  have hcomp (x : Variety.Point (dVariety k 4)) :
      q.onPoints (p.onPoints x) = M.f4CorootProduct.onPoints (δ x) := by
    rw [show p = cocharacterTupleProduct hS μ from rfl,
      cocharacterTupleProduct_apply, map_list_prod, List.map_ofFn,
      M.f4CorootProduct_apply]
    congr 1
    apply congrArg List.ofFn
    funext i
    dsimp only [Function.comp_apply]
    rw [hμ, hcoordinate]
  apply torus_injective_of_bijective_composite (dVariety_isTorus 4) hS p q hfinite
  have hpoint : (q.comp p).onPoints =
      (fun x => e.toMulEquiv (δ x)) := by
    funext x
    rw [show (q.comp p).onPoints x = q.onPoints (p.onPoints x) from rfl, hcomp]
    exact congrArg (fun f : Morphism (dVariety k 4) M.torus.carrierVariety =>
      f.onPoints (δ x)) he.symm
  rw [hpoint]
  exact e.toMulEquiv.bijective.comp hδ

end RootSystemModel
end Theory.AlgebraicGroup

namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry
open Theory.AlgebraicGroup
variable {F : Type u} [Field F] [IsAlgClosed F] [CharP F 2]

noncomputable local instance modelTorusAlgebraicGroup
    (M : RootSystemModel StandardRootSystem.typeF4RootPairingULift
      (F4Chevalley.Carrier (k := F))) : AlgebraicGroup M.torus.carrierVariety :=
  M.torus.carrierAlgebraicGroup

/-- The point-kernel argument, with its two remaining geometric inputs explicit. -/
theorem f4_incoming_isogeny_injective_of_torus_coroot_lifts
    {H : Variety F} [AlgebraicGroup H]
    (M : RootSystemModel StandardRootSystem.typeF4RootPairingULift
      (F4Chevalley.Carrier (k := F)))
    (φ : Morphism H (F4Chevalley.Carrier (k := F))) (hφ : IsIsogeny φ)
    (e : @Iso F _ (dVariety F 4) M.torus.carrierVariety _ M.torus.carrierAlgebraicGroup)
    (he : e.hom = M.f4CorootProduct)
    (hkernel : φ.kernel ≤ (isogenyTorusLift φ M.torus).toSubgroup)
    (μ : Fin 4 → Morphism (KMult F) (isogenyTorusLift φ M.torus).carrierVariety)
    (a : Fin 4 → ℕ)
    (hμ : ∀ i t, (isogenyTorusLiftMap φ M.torus).onPoints ((μ i).onPoints t) =
      (M.rootData.rootCocharacter (M.f4SimpleRoot i)).onPoints (t ^ (2 ^ a i))) :
    Function.Injective φ.onPoints := by
  let S := isogenyTorusLift φ M.torus
  let q := isogenyTorusLiftMap φ M.torus
  have hq : Function.Injective q.onPoints :=
    M.f4_torusMap_injective_of_coroot_lifts
      (isogenyTorusLift_isSubtorus φ hφ.2 M.torus M.maximalTorus.1)
      q (isogenyTorusLiftMap_kernel_finite φ hφ.2 M.torus) e he μ a hμ
  apply φ.onPoints.ker_eq_bot_iff.mp
  apply le_antisymm
  · intro x hx
    let s : Variety.Point S.carrierVariety := S.pointEquiv.symm ⟨x, hkernel hx⟩
    have hs : S.inclusion.onPoints s = x := by
      exact congrArg Subtype.val (S.pointEquiv.apply_symm_apply _)
    have hqs : q.onPoints s = 1 := by
      apply M.torus.inclusion_injective
      rw [map_one, isogenyTorusLiftMap_apply, hs]
      exact hx
    have hsone : s = 1 := hq (hqs.trans q.onPoints.map_one.symm)
    apply Subgroup.mem_bot.mpr
    rw [← hs, hsone, map_one]
  · exact bot_le

end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry
