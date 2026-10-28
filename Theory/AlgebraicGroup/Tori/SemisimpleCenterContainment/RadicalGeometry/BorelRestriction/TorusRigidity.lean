module

public import Theory.AlgebraicGroup.Tori.SemisimpleCenterContainment.RadicalGeometry.BorelRestriction.TorusRigidity.Geometry
public import Theory.AlgebraicGroup.Tori.SemisimpleCenterContainment.RadicalGeometry.BorelRestriction.TorusRigidity.Torsion

/-!
# Rigidity of a connected geometric family of torus homomorphisms

For every finite-order source point, the family has finite image in the target
and is therefore constant by connectedness. Algebraic characters detect
homomorphisms from their values on these points, so all slices agree. The
source is an arbitrary connected geometric variety; neither completeness nor
an a priori finite list of torus homomorphisms is assumed.

This proves the torus case of Borel, *Linear Algebraic Groups*, §8.10, in the
form used by the fixed-component centralizer argument in §11.15.
-/

namespace Theory.AlgebraicGroup
open Variety.Geometric
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {Y : Variety.Geometric k} {T Q : Variety k} [AlgebraicGroup T] [AlgebraicGroup Q]

@[expose] public noncomputable def torusFamilyPoint
    (α : Variety.Geometric.Morphism (Variety.Geometric.prod Y (ofAffine T)) (ofAffine Q))
    (y : Point Y) (t : Variety.Point T) : Variety.Point Q :=
  affinePointEquiv Q (α (prodPoint y ((affinePointEquiv T).symm t)))

public noncomputable def torusFamilySlice
    (α : Variety.Geometric.Morphism (Variety.Geometric.prod Y (ofAffine T)) (ofAffine Q))
    (h1 : ∀ y, torusFamilyPoint α y 1 = 1)
    (hm : ∀ y a b, torusFamilyPoint α y (a * b) = torusFamilyPoint α y a * torusFamilyPoint α y b)
    (y : Point Y) : AlgebraicGroup.Morphism T Q where
  toVariety := ((Variety.Geometric.Morphism.rightSection Y (ofAffine T) y).comp α).toPresentedAffine
  map_one := by
    rw [Variety.Geometric.Morphism.toPresentedAffine_apply,
      Variety.Geometric.Morphism.comp_apply_point, Variety.Geometric.Morphism.rightSection_apply]
    exact h1 y
  map_mul := by
    intro a b
    rw [Variety.Geometric.Morphism.toPresentedAffine_apply,
      Variety.Geometric.Morphism.toPresentedAffine_apply,
      Variety.Geometric.Morphism.toPresentedAffine_apply,
      Variety.Geometric.Morphism.comp_apply_point,
      Variety.Geometric.Morphism.comp_apply_point,
      Variety.Geometric.Morphism.comp_apply_point,
      Variety.Geometric.Morphism.rightSection_apply,
      Variety.Geometric.Morphism.rightSection_apply,
      Variety.Geometric.Morphism.rightSection_apply]
    exact hm y a b

public theorem torusFamilySlice_apply
    (α : Variety.Geometric.Morphism (Variety.Geometric.prod Y (ofAffine T)) (ofAffine Q))
    (h1 : ∀ y, torusFamilyPoint α y 1 = 1)
    (hm : ∀ y a b, torusFamilyPoint α y (a * b) = torusFamilyPoint α y a * torusFamilyPoint α y b)
    (y : Point Y) (t : Variety.Point T) :
    (torusFamilySlice α h1 hm y).onPoints t = torusFamilyPoint α y t := by
  change (((Variety.Geometric.Morphism.rightSection Y (ofAffine T) y).comp α).toPresentedAffine).toFun t = _
  rw [Variety.Geometric.Morphism.toPresentedAffine_apply,
    Variety.Geometric.Morphism.comp_apply_point, Variety.Geometric.Morphism.rightSection_apply]
  rfl

public theorem torus_family_rigidity
    (hY : Variety.Geometric.IsConnected Y) (hT : IsTorus T) (hQ : IsTorus Q)
    (α : Variety.Geometric.Morphism (Variety.Geometric.prod Y (ofAffine T)) (ofAffine Q))
    (h1 : ∀ y, torusFamilyPoint α y 1 = 1)
    (hm : ∀ y a b, torusFamilyPoint α y (a * b) = torusFamilyPoint α y a * torusFamilyPoint α y b)
    (y z : Point Y) (t : Variety.Point T) :
    torusFamilyPoint α y t = torusFamilyPoint α z t := by
  let F := torusFamilySlice α h1 hm
  have hF : F y = F z := by
    apply torus_morphism_eq_of_torsion hT hQ
    intro x hx
    obtain ⟨m, hm0, hxm⟩ := hx.exists_pow_eq_one
    let β := (Variety.Geometric.Morphism.leftSection Y (ofAffine T)
      ((affinePointEquiv T).symm x)).comp α
    have hβ (w : Point Y) : affinePointEquiv Q (β w) = (F w).onPoints x := by
      rw [torusFamilySlice_apply]
      change affinePointEquiv Q (((Variety.Geometric.Morphism.leftSection Y (ofAffine T)
        ((affinePointEquiv T).symm x)).comp α) w) = _
      rw [Variety.Geometric.Morphism.comp_apply_point,
        Variety.Geometric.Morphism.leftSection_apply]
      rfl
    have hfin : (Set.range β).Finite := by
      have hsub : affinePointEquiv Q '' Set.range β ⊆ {a : Variety.Point Q | a ^ m = 1} := by
        rintro _ ⟨_, ⟨w, rfl⟩, rfl⟩
        rw [Set.mem_ofPred_eq, hβ, ← map_pow, hxm, map_one]
      exact ((torus_bounded_torsion_finite hQ hm0).subset hsub).of_finite_image
        (affinePointEquiv Q).injective.injOn
    have hc := Variety.Geometric.Morphism.finite_range_constant β hY hfin y z
    rw [← hβ, ← hβ]
    exact congrArg (affinePointEquiv Q) hc
  have h := congrArg (fun f : AlgebraicGroup.Morphism T Q => f.onPoints t) hF
  simpa only [F, torusFamilySlice_apply] using h
end Theory.AlgebraicGroup
