module

public import Theory.GroupAction.NoncentralTwoChiefLength.SectionMaps
public import Theory.GroupTheory.PCoreSurjective
public import Theory.GroupTheory.PCoreLocalSetup
public import Theory.GroupTheory.LocalNormalizerUniqueness
import Mathlib.Tactic

/-!
# Restricting local quotient maps to their two-cores

A surjection `P → D` with two-group kernel `N` has full preimage of `O₂(D)`
equal to `O₂(P)`. Restriction therefore constructs a surjective map between
the embedded two-cores with the same kernel. We retain the actor embedding;
the homomorphism law proves equivariance for the literal conjugation actions.

This is the lifting step from the parabolic quotient identifications to the
common two-group in Aschbacher–Smith 13.8.33, printed p.968.
-/

@[expose] public section

open Subgroup
namespace Subgroup
variable {G K : Type*} [Group G] [Group K]

/-- An actual local quotient, retaining the subgroup embedding of the actor. -/
structure LocalCoreQuotient (A N P : Subgroup G) (B D : Subgroup K) (f : A →* B) where
  actor_le : A ≤ P
  kernel_le : N ≤ P
  projection : P →* D
  onto : Function.Surjective projection
  kernel : projection.ker = N.subgroupOf P
  marked : ∀ a : A, (projection (inclusion actor_le a) : K) = (f a : K)

namespace LocalCoreQuotient
variable {A N P : Subgroup G} {B D : Subgroup K} {f : A →* B}
variable [Finite G] [Finite K] (s : LocalCoreQuotient A N P B D f)

/-- Restricting a genuine quotient with two-group kernel to the two-core gives
its exact core quotient, including the conjugation action. -/
noncomputable def coreSection (hN : IsPGroup 2 N)
    (hBD : B ≤ normalizer (D.pCoreIn 2 : Set K)) :
    letI := conjMulDistribMulActionOfLeNormalizer B (D.pCoreIn 2) hBD
    ConjugationSection (Y := D.pCoreIn 2) A N (P.pCoreIn 2) f := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI := conjMulDistribMulActionOfLeNormalizer B (D.pCoreIn 2) hBD
  have hk : IsPGroup 2 s.projection.ker := by
    rw [s.kernel]
    exact hN.comap_subtype
  have hpre := s.projection.comap_pCore_of_ker_isPGroup s.onto hk
  have hNR : N ≤ P.pCoreIn 2 := by
    intro n hn
    have hz : s.projection ⟨n, s.kernel_le hn⟩ = 1 := by
      apply MonoidHom.mem_ker.mp
      rw [s.kernel]
      exact hn
    have hc : (⟨n, s.kernel_le hn⟩ : P) ∈ pCore 2 P := by
      rw [← hpre]
      change s.projection ⟨n, s.kernel_le hn⟩ ∈ pCore 2 D
      rw [hz]
      exact one_mem _
    exact ⟨⟨n, s.kernel_le hn⟩, hc, rfl⟩
  have hAR : A ≤ normalizer (P.pCoreIn 2 : Set G) :=
    s.actor_le.trans (P.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image P (pCore 2 P)))
  let ψ : P.pCoreIn 2 →* D := s.projection.comp (inclusion (pCoreIn_le 2 P))
  have hψ : ∀ r : P.pCoreIn 2, (ψ r : K) ∈ D.pCoreIn 2 := by
    intro r
    obtain ⟨x, hx, he⟩ := r.property
    have hp : s.projection x ∈ pCore 2 D := by
      change x ∈ (pCore 2 D).comap s.projection
      rw [hpre]
      exact hx
    refine ⟨s.projection x, hp, ?_⟩
    exact congrArg (fun z : P => (s.projection z : K)) (Subtype.ext he)
  let π : P.pCoreIn 2 →* D.pCoreIn 2 :=
    { toFun := fun r => ⟨ψ r, hψ r⟩
      map_one' := Subtype.ext (congrArg (fun z : D => (z : K)) ψ.map_one)
      map_mul' := fun x y => Subtype.ext (congrArg (fun z : D => (z : K)) (ψ.map_mul x y)) }
  refine ⟨hNR, hAR, π, ?_, ?_, ?_⟩
  · intro d
    obtain ⟨y, hy, he⟩ := d.property
    obtain ⟨x, hx⟩ := s.onto y
    have hp : x ∈ pCore 2 P := by
      rw [← hpre]
      change s.projection x ∈ pCore 2 D
      rwa [hx]
    refine ⟨⟨x, ⟨x, hp, rfl⟩⟩, ?_⟩
    apply Subtype.ext
    exact (congrArg (fun z : D => (z : K)) hx).trans he
  · ext r
    change (⟨ψ r, hψ r⟩ : D.pCoreIn 2) = 1 ↔ (r : G) ∈ N
    have hm : ψ r = 1 ↔ (r : G) ∈ N := by
      change inclusion (pCoreIn_le 2 P) r ∈ s.projection.ker ↔ _
      rw [s.kernel]
      rfl
    constructor
    · intro hr
      exact hm.mp (Subtype.ext (congrArg (fun z : D.pCoreIn 2 => (z : K)) hr))
    · intro hr
      exact Subtype.ext (congrArg (fun z : D => (z : K)) (hm.mpr hr))
  · let := conjMulDistribMulActionOfLeNormalizer A (P.pCoreIn 2) hAR
    intro a r
    apply Subtype.ext
    change (s.projection (inclusion (pCoreIn_le 2 P) (a • r)) : K) =
      (f a : K) * (ψ r : K) * (f a : K)⁻¹
    have he : inclusion (pCoreIn_le 2 P) (a • r) =
        inclusion s.actor_le a * inclusion (pCoreIn_le 2 P) r * (inclusion s.actor_le a)⁻¹ :=
      Subtype.ext rfl
    rw [he, map_mul, map_mul, map_inv]
    change (s.projection (inclusion s.actor_le a) : K) * (ψ r : K) *
      (s.projection (inclusion s.actor_le a) : K)⁻¹ = _
    rw [s.marked]
end LocalCoreQuotient
end Subgroup
