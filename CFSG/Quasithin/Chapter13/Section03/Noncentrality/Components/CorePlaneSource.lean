module
public import Theory.Representation.BinaryPermutationSixCover.PlanePreimage
public import Theory.GroupTheory.PCoreLocalSetup
public import Mathlib.GroupTheory.Commutator.Basic
/-!
# The actual augmentation-core contradiction in 13.3.14(g)

Transport the five-dimensional A₆ core calculation through the original
multiplicative coordinates of W. The actor is still the subgroup A, and
its embedded two-core is unchanged. The plane is in the actual natural
quotient by the constant line. This proves the needed centralization and
its contradiction with the earlier nontrivial point commutator.

The source construction of the core coordinates remains in the component
module analysis. No faithfulness or vanishing two-core of the raw ambient
J is assumed here.

Source: Aschbacher–Smith, 13.3.14(g), printed p.893.
-/

public section
open Subgroup BinaryPermutation
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter13.Section03.Noncentrality
variable {G : Type*} [Group G] [Finite G]
theorem source_core_plane_centralized
    (A W U : Subgroup G) (hA : IsPPerfect 2 A)
    (hAW : A ≤ normalizer (W : Set G)) (hUW : U ≤ W)
    (f : A →* alternatingGroup (Fin 6)) (e : f.range ≃* alternatingGroup (Fin 4))
    (c : W ≃* Multiplicative (core (Fin 6)))
    (hc : ∀ (a : A) (w : W),
      (c (W.normalizerMonoidHom ⟨a,hAW a.property⟩ w)).toAdd =
        alternatingCoreRepresentation (Fin 6) (f a) (c w).toAdd)
    (E : Submodule (ZMod 2) (natural (Fin 6))) (hE : Nat.card E = 4)
    (hEinv : ∀ a : A, ∀ v ∈ E, alternatingNaturalRepresentation (Fin 6) (f a) v ∈ E)
    (hUE : ∀ (u : G) (hu : u ∈ U),
      coreToNatural (Fin 6) (c ⟨u,hUW hu⟩).toAdd ∈ E) :
    ⁅U, A.pCoreIn 2⁆ = ⊥ := by
  apply le_bot_iff.mp
  apply commutator_le.mpr
  intro u hu g hg
  obtain ⟨a,ha,rfl⟩ := hg
  let w : W := ⟨u,hUW hu⟩
  have hfix := SixCover.four_actor_core_plane_preimage_fixed hA f e E hE hEinv
    a ha (c w).toAdd (hUE u hu)
  have hcoord := hc a w
  rw [hfix] at hcoord
  have he : W.normalizerMonoidHom ⟨a,hAW a.property⟩ w = w := by
    apply c.injective
    exact congrArg Multiplicative.ofAdd hcoord
  have heval : (a:G) * u * (a:G)⁻¹ = u := congrArg Subtype.val he
  change ⁅u,(a:G)⁆ = 1
  apply commutatorElement_eq_one_iff_mul_comm.mpr
  exact (mul_inv_eq_iff_eq_mul.mp heval).symm

theorem source_core_plane_noncentral_contradiction
    (A W U P : Subgroup G) (hA : IsPPerfect 2 A)
    (hAW : A ≤ normalizer (W : Set G)) (hUW : U ≤ W)
    (f : A →* alternatingGroup (Fin 6)) (e : f.range ≃* alternatingGroup (Fin 4))
    (c : W ≃* Multiplicative (core (Fin 6)))
    (hc : ∀ (a : A) (w : W),
      (c (W.normalizerMonoidHom ⟨a,hAW a.property⟩ w)).toAdd =
        alternatingCoreRepresentation (Fin 6) (f a) (c w).toAdd)
    (E : Submodule (ZMod 2) (natural (Fin 6))) (hE : Nat.card E = 4)
    (hEinv : ∀ a : A, ∀ v ∈ E, alternatingNaturalRepresentation (Fin 6) (f a) v ∈ E)
    (hUE : ∀ (u : G) (hu : u ∈ U),
      coreToNatural (Fin 6) (c ⟨u,hUW hu⟩).toAdd ∈ E)
    (hP : P ≠ ⊥) (hm : ⁅U,A.pCoreIn 2⁆ = P) : False := by
  exact hP (hm.symm.trans (source_core_plane_centralized A W U hA hAW hUW f e c hc
    E hE hEinv hUE))
end CFSG.Quasithin.Chapter13.Section03.Noncentrality
