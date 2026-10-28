module

public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.GroupTheory.Complement

/-!
# Sylow maximality from a normalizer projection

Let `U` be a p-subgroup of a finite group. If its normalizer lies in `B`,
and a homomorphism from `B` to a group without p-power torsion has kernel
`U`, then `U` is Sylow. Indeed, in a p-overgroup `P`, the relative
normalizer of `U` maps trivially under that homomorphism. Thus `U` is
self-normalizing in `P`; the normalizer condition for p-groups forces `P=U`.

The normalizer containment follows from `U N U` coverage and an escape
witness for each non-Borel representative. A complement to `U` in `B`
constructs the projection. These are the finite-group steps used for the
positive unipotent group in GLS3, Theorem 2.3.4(d); neither Sylow maximality
nor an index condition is a premise.
-/

namespace Subgroup

variable {G H : Type*} [Group G] [Group H] {p : ℕ} [Fact p.Prime]

/-- A `U N U` factorization reduces the positive normalizer calculation to
the torus-normalizer representatives. A representative outside `B` is ruled
out by one positive element which it sends outside `U`. -/
public theorem normalizer_le_of_unipotent_factorization
    (U B N : Subgroup G) (hUB : U ≤ B)
    (hcover : ∀ g : G, ∃ u ∈ U, ∃ n ∈ N, ∃ v ∈ U, g = u * n * v)
    (hescape : ∀ n ∈ N, n ∉ B → ∃ u ∈ U, n * u * n⁻¹ ∉ U) :
    normalizer (U : Set G) ≤ B := by
  intro g hg
  obtain ⟨u, hu, n, hn, v, hv, rfl⟩ := hcover g
  have hnNorm : n ∈ normalizer (U : Set G) := by
    have h := (normalizer (U : Set G)).mul_mem
      ((normalizer (U : Set G)).mul_mem
        ((normalizer (U : Set G)).inv_mem (U.le_normalizer hu)) hg)
      ((normalizer (U : Set G)).inv_mem (U.le_normalizer hv))
    simpa only [← mul_assoc, inv_mul_cancel, one_mul, mul_inv_cancel_right] using h
  have hnB : n ∈ B := by
    by_contra hnot
    obtain ⟨x, hx, hnx⟩ := hescape n hn hnot
    exact hnx ((Subgroup.mem_normalizer_iff.mp hnNorm x).mp hx)
  exact B.mul_mem (B.mul_mem (hUB hu) hnB) (hUB hv)

/-- A p-overgroup cannot grow past the kernel of a p-torsion-free normalizer
projection. The kernel is a subgroup of `B`, not an ambient normal subgroup. -/
public theorem p_overgroup_eq_of_normalizer_projection
    (U B P : Subgroup G) [Finite P] (hP : IsPGroup p P) (hUP : U ≤ P)
    (hnorm : normalizer (U : Set G) ≤ B)
    (f : B →* H) (hker : f.ker = U.subgroupOf B)
    (htorsion : ∀ x : H, ∀ n : ℕ, x ^ (p ^ n) = 1 → x = 1) : P = U := by
  let : Group.IsNilpotent P := hP.isNilpotent
  have hself : normalizer (U.subgroupOf P : Set P) = U.subgroupOf P := by
    apply le_antisymm _ le_normalizer
    rw [← subgroupOf_normalizer_eq hUP]
    intro x hx
    have hxB : (x : G) ∈ B := hnorm hx
    obtain ⟨n, hn⟩ := hP x
    have hxpow : (⟨(x : G), hxB⟩ : B) ^ (p ^ n) = 1 :=
      Subtype.ext (congrArg (fun z : P => (z : G)) hn)
    have hfx : f ⟨(x : G), hxB⟩ = 1 :=
      htorsion _ n (by simpa only [map_pow, map_one] using congrArg f hxpow)
    have hxker : (⟨(x : G), hxB⟩ : B) ∈ f.ker := hfx
    rw [hker] at hxker
    exact hxker
  have htop := normalizerCondition_iff_only_full_group_self_normalizing.mp
    (Group.normalizerCondition_of_isNilpotent (G := P)) _ hself
  exact le_antisymm (subgroupOf_eq_top.mp htop) hUP

/-- Construct the Sylow subgroup from the normalizer projection. -/
@[expose] public def sylowOfNormalizerProjection [Finite G]
    (U B : Subgroup G) (hU : IsPGroup p U)
    (hnorm : normalizer (U : Set G) ≤ B)
    (f : B →* H) (hker : f.ker = U.subgroupOf B)
    (htorsion : ∀ x : H, ∀ n : ℕ, x ^ (p ^ n) = 1 → x = 1) : Sylow p G :=
  { U with
    isPGroup' := hU
    is_maximal' := fun {P} hP hUP =>
      p_overgroup_eq_of_normalizer_projection U B P hP hUP hnorm f hker htorsion }

@[simp] public theorem coe_sylowOfNormalizerProjection [Finite G]
    (U B : Subgroup G) (hU : IsPGroup p U)
    (hnorm : normalizer (U : Set G) ≤ B)
    (f : B →* H) (hker : f.ker = U.subgroupOf B)
    (htorsion : ∀ x : H, ∀ n : ℕ, x ^ (p ^ n) = 1 → x = 1) :
    (sylowOfNormalizerProjection U B hU hnorm f hker htorsion : Subgroup G) = U := rfl

/-- Construct the normalizer projection from an actual normal complement
decomposition, then prove Sylow maximality. -/
@[expose] public noncomputable def sylowOfNormalizerComplement [Finite G]
    (U B : Subgroup G) (H : Subgroup B) [(U.subgroupOf B).Normal]
    (hU : IsPGroup p U) (hnorm : normalizer (U : Set G) ≤ B)
    (hcomp : H.IsComplement' (U.subgroupOf B))
    (htorsion : ∀ x : H, ∀ n : ℕ, x ^ (p ^ n) = 1 → x = 1) : Sylow p G := by
  let e := hcomp.QuotientMulEquiv
  let f : B →* H := e.toMonoidHom.comp (QuotientGroup.mk' (U.subgroupOf B))
  have hker : f.ker = U.subgroupOf B := by
    ext x
    change e (QuotientGroup.mk' (U.subgroupOf B) x) = 1 ↔ x ∈ U.subgroupOf B
    rw [← e.map_one, e.injective.eq_iff]
    exact QuotientGroup.eq_one_iff x
  exact sylowOfNormalizerProjection U B hU hnorm f hker htorsion

@[simp] public theorem coe_sylowOfNormalizerComplement [Finite G]
    (U B : Subgroup G) (H : Subgroup B) [(U.subgroupOf B).Normal]
    (hU : IsPGroup p U) (hnorm : normalizer (U : Set G) ≤ B)
    (hcomp : H.IsComplement' (U.subgroupOf B))
    (htorsion : ∀ x : H, ∀ n : ℕ, x ^ (p ^ n) = 1 → x = 1) :
    (sylowOfNormalizerComplement U B H hU hnorm hcomp htorsion : Subgroup G) = U := rfl

end Subgroup
