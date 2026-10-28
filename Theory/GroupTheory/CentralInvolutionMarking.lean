module

public import Mathlib.GroupTheory.Sylow
public import Stellmacher.OmegaOneCenterMap

/-!
# Intrinsic marking of a local central involution

If a local subgroup contains a Sylow two-subgroup whose omega-center has
order two, every central involution in the local subgroup generates that
same omega-center in the ambient group. The cyclic subgroup is a normal
two-subgroup of the local group, hence lies in its prescribed Sylow subgroup.
This makes the marking independent of the chosen local-model isomorphism.

Source: the central-involution marking in Aschbacher--Smith 14.2.21.
-/

public section
open Subgroup Stellmacher
namespace Theory.GroupTheory

theorem central_involution_marking
    {G : Type*} [Group G] [Finite G]
    (T : Sylow 2 G) (H : Subgroup G) (hTH : (T : Subgroup G) ≤ H)
    (hcard : Nat.card (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (z : H) (hz : z ∈ center H) (ho : orderOf z = 2) :
    zpowers (z : G) = omegaOneCenterAmbient (T : Subgroup G) := by
  have hpow : z ^ 2 = 1 := ho ▸ pow_orderOf_eq_one z
  let : (zpowers z).Normal := ⟨fun x hx g => by
    have hc := (zpowers_le.mpr hz : zpowers z ≤ center H) hx
    simpa only [mem_center_iff.mp hc g, mul_inv_cancel_right] using hx⟩
  have hp : IsPGroup 2 (zpowers z) :=
    (IsElementaryAbelian.zpowers_of_pow_eq_one hpow).isPGroup
  have hzT : (z : G) ∈ (T : Subgroup G) :=
    hp.le_sylow_of_normal (T.subtype hTH) (mem_zpowers z)
  have hle : zpowers (z : G) ≤ omegaOneCenterAmbient (T : Subgroup G) := by
    apply zpowers_le.mpr
    apply (mem_omegaOneCenterAmbient_iff _ _).mpr
    refine ⟨hzT,congrArg H.subtype hpow,?_⟩
    intro t ht
    exact congrArg H.subtype (mem_center_iff.mp hz ⟨t,hTH ht⟩)
  apply eq_of_le_of_card_ge hle
  have hoG : orderOf (z : G) = 2 :=
    (orderOf_injective H.subtype H.subtype_injective z).trans ho
  rw [hcard,Nat.card_zpowers,hoG]

end Theory.GroupTheory
