module

public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.QuadraticSplitting.LargeFieldComplements.Fibre
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.QuadraticSplitting.LargeFieldComplements.Geometry
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.QuadraticSplitting.LargeFieldComplements.FixedDecomposition


/-!
# Equivariant projection and correction of fixed lifts

For C_V(Q) = C_U(Q) ⊕ W with K preserving both summands, the projection
onto C_U(Q) is binary linear and K-equivariant. Quadraticity makes the
projected displacement of a K-fixed vector an additive K-map from Q to
C_U(Q). When that map is displacement by a vector of C_U(K), subtracting
that vector places the lift in the zero-adjoined fibre without changing
its quotient modulo U.

The natural-module realization of such maps is recorded as an explicit
remaining obligation, independent of quadraticity and fixed lifts. It is
not assumed as a fact about arbitrary representations.
Source: Aschbacher–Smith B.4.9(1), printed pp.93–94, combined manuscript
of 1 March 2004, the homogeneous K-module case.
-/

@[expose] public section

open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.NaturalExtensions.QuadraticSplitting
namespace LargeFieldComplements.Homogeneous

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]

private theorem exists_projection (A W C : Submodule (ZMod 2) V)
    (hC : C = A ⊔ W) :
    ∃ p : C →ₗ[ZMod 2] A, ∀ z : C, (z : V) - (p z : V) ∈ W := by
  let t : A × W →ₗ[ZMod 2] V :=
    A.subtype.comp (LinearMap.fst _ _ _) + W.subtype.comp (LinearMap.snd _ _ _)
  have ht (z : A × W) : t z ∈ C := by
    rw [hC]
    exact Submodule.add_mem_sup z.1.property z.2.property
  let t' : A × W →ₗ[ZMod 2] C := t.codRestrict C ht
  have hs : Function.Surjective t' := by
    intro z
    have hz : (z : V) ∈ A ⊔ W := hC ▸ z.property
    obtain ⟨a, ha, w, hw, he⟩ := Submodule.mem_sup.mp hz
    exact ⟨(⟨a, ha⟩, ⟨w, hw⟩), Subtype.ext he⟩
  obtain ⟨s, hs⟩ := t'.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hs)
  refine ⟨(LinearMap.fst _ _ _).comp s, fun z => ?_⟩
  have hz := congrArg Subtype.val (LinearMap.congr_fun hs z)
  change ((s z).1 : V) + ((s z).2 : V) = z at hz
  change (z : V) - ((s z).1 : V) ∈ W
  rw [← hz, add_sub_cancel_left]
  exact (s z).2.property

private theorem projection_unique (A W C : Submodule (ZMod 2) V)
    (hdis : Disjoint A W) (p : C →ₗ[ZMod 2] A)
    (hp : ∀ z : C, (z : V) - (p z : V) ∈ W)
    (z : C) (a : A) (ha : (z : V) - (a : V) ∈ W) : p z = a := by
  apply Subtype.ext
  apply sub_eq_zero.mp
  apply Submodule.disjoint_def.mp hdis
  · exact A.sub_mem (p z).property a.property
  · have hh := W.sub_mem ha (hp z)
    convert hh using 1
    abel

variable (ρ : Representation (ZMod 2) G V) (K Q : Subgroup G)

/-- An additive map from the actual axis group to the original Q-fixed
natural subspace, equivariant for direct conjugation by the actual Levi.
Its realizability is the precise natural-plane calculation still needed. -/
def NaturalDisplacementRealization (N : Subrepresentation ρ) : Prop :=
  ∀ f : Additive Q →+ ↥(N.toSubmodule ⊓ fixedSpace ρ Q),
    (∀ (k : G) (_hk : k ∈ K) (x y : Q),
      (y : G) = k * x * k⁻¹ →
      (f (Additive.ofMul y) : V) = ρ k (f (Additive.ofMul x))) →
    ∃ u : V, u ∈ N.toSubmodule ∧ u ∈ fixedSpace ρ K ∧
      ∀ x : Q, (f (Additive.ofMul x) : V) = ρ x u - u

private theorem fixed_stable
    (hnorm : ∀ k ∈ K, ∀ x ∈ Q, k * x * k⁻¹ ∈ Q)
    (k : G) (hk : k ∈ K) (z : V) (hz : z ∈ fixedSpace ρ Q) :
    ρ k z ∈ fixedSpace ρ Q := by
  intro x
  change ρ (x : G) (ρ k z) = ρ k z
  have he : ρ (k⁻¹ * x * k) z = z :=
    hz ⟨k⁻¹ * x * k, by simpa only [inv_inv] using hnorm k⁻¹ (K.inv_mem hk) x x.property⟩
  have hh := congrArg (ρ k) he
  rw [← Module.End.mul_apply, ← map_mul] at hh
  simpa only [mul_assoc, mul_inv_cancel_left, map_mul, Module.End.mul_apply] using hh

private theorem projection_equivariant
    (N : Subrepresentation ρ) (W : Submodule (ZMod 2) V)
    (hnorm : ∀ k ∈ K, ∀ x ∈ Q, k * x * k⁻¹ ∈ Q)
    (hdis : Disjoint N.toSubmodule W)
    (hW : K ≤ subspaceStabilizer ρ W)
    (p : fixedSpace ρ Q →ₗ[ZMod 2] ↥(N.toSubmodule ⊓ fixedSpace ρ Q))
    (hp : ∀ z : fixedSpace ρ Q, (z : V) - (p z : V) ∈ W)
    (k : G) (hk : k ∈ K) (z : fixedSpace ρ Q) :
    (p ⟨ρ k z, fixed_stable ρ K Q hnorm k hk z z.property⟩ : V) = ρ k (p z) := by
  let a : ↥(N.toSubmodule ⊓ fixedSpace ρ Q) :=
    ⟨ρ k (p z), N.apply_mem_toSubmodule k (p z).property.1,
      fixed_stable ρ K Q hnorm k hk (p z) (p z).property.2⟩
  apply congrArg Subtype.val
    (projection_unique _ W _ (hdis.mono_left inf_le_left) p hp _ a ?_)
  change ρ k z - ρ k (p z) ∈ W
  rw [← map_sub]
  exact (hW hk _).mpr (hp z)

/-- The projection onto the original Q-fixed part along W is K-equivariant.
The direct-sum identity is used only within C_V(Q). -/
theorem exists_equivariant_projection
    (N : Subrepresentation ρ) (W : Submodule (ZMod 2) V)
    (hnorm : ∀ k ∈ K, ∀ x ∈ Q, k * x * k⁻¹ ∈ Q)
    (hdis : Disjoint N.toSubmodule W)
    (hW : K ≤ subspaceStabilizer ρ W)
    (hC : fixedSpace ρ Q = (N.toSubmodule ⊓ fixedSpace ρ Q) ⊔ W) :
    ∃ p : fixedSpace ρ Q →ₗ[ZMod 2] ↥(N.toSubmodule ⊓ fixedSpace ρ Q),
      (∀ z : fixedSpace ρ Q, (z : V) - (p z : V) ∈ W) ∧
      ∀ (k : G), k ∈ K → ∀ z z' : fixedSpace ρ Q,
        (z' : V) = ρ k z → (p z' : V) = ρ k (p z) := by
  obtain ⟨p, hp⟩ := exists_projection (N.toSubmodule ⊓ fixedSpace ρ Q) W _ hC
  refine ⟨p, hp, fun k hk z z' he => ?_⟩
  have hz' : z' = ⟨ρ k z, fixed_stable ρ K Q hnorm k hk z z.property⟩ :=
    Subtype.ext he
  rw [hz']
  exact projection_equivariant ρ K Q N W hnorm hdis hW p hp k hk z

/-- Every fixed lift can be corrected by a vector of the original natural
submodule, once the natural-plane displacement calculation is supplied. -/
theorem fixed_lift_correction
    (N : Subrepresentation ρ) (W : Submodule (ZMod 2) V)
    (hq : IsQuadratic ρ Q)
    (hnorm : ∀ k ∈ K, ∀ x ∈ Q, k * x * k⁻¹ ∈ Q)
    (hdis : Disjoint N.toSubmodule W)
    (hW : K ≤ subspaceStabilizer ρ W)
    (hC : fixedSpace ρ Q = (N.toSubmodule ⊓ fixedSpace ρ Q) ⊔ W)
    (hreal : NaturalDisplacementRealization ρ K Q N)
    (z : V) (hz : z ∈ fixedSpace ρ K) :
    ∃ u : V, u ∈ N.toSubmodule ∧ u ∈ fixedSpace ρ K ∧
      z - u ∈ displacementFibre ρ K Q W := by
  obtain ⟨p, hp, hpk⟩ := exists_equivariant_projection ρ K Q N W hnorm hdis hW hC
  let a : Additive Q →+ fixedSpace ρ Q :=
    { toFun := fun x => ⟨displacementHom ρ Q hq z x, fun y => hq y y.property x.toMul x.toMul.property z⟩
      map_zero' := Subtype.ext ((displacementHom ρ Q hq z).map_zero)
      map_add' := fun x y => Subtype.ext ((displacementHom ρ Q hq z).map_add x y) }
  let f : Additive Q →+ ↥(N.toSubmodule ⊓ fixedSpace ρ Q) := p.toAddMonoidHom.comp a
  have hequiv (k : G) (hk : k ∈ K) (x y : Q) (hy : (y : G) = k * x * k⁻¹) :
      (f (Additive.ofMul y) : V) = ρ k (f (Additive.ofMul x)) := by
    have hki : ρ k⁻¹ z = z := hz ⟨k⁻¹, K.inv_mem hk⟩
    have he : a (Additive.ofMul y) =
        ⟨ρ k (a (Additive.ofMul x)),
          fixed_stable ρ K Q hnorm k hk _ (a (Additive.ofMul x)).property⟩ := by
      apply Subtype.ext
      change ρ y z - z = ρ k (ρ x z - z)
      rw [hy, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply,
        hki, map_sub, show ρ k z = z from hz ⟨k, hk⟩]
    change (p (a (Additive.ofMul y)) : V) = ρ k (p (a (Additive.ofMul x)))
    exact hpk k hk _ _ (congrArg Subtype.val he)
  obtain ⟨u, huN, huK, hu⟩ := hreal f hequiv
  refine ⟨u, huN, huK, (fixedSpace ρ K).sub_mem hz huK, fun x => ?_⟩
  have hh := hp (a (Additive.ofMul x))
  change (ρ x z - z) - (f (Additive.ofMul x) : V) ∈ W at hh
  rw [hu x] at hh
  rw [map_sub]
  convert hh using 1
  abel

end LargeFieldComplements.Homogeneous
end CFSG.Quasithin.ChapterB.NaturalExtensions.QuadraticSplitting
