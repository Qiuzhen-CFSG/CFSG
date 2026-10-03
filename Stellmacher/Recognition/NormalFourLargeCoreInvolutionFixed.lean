module

public import Stellmacher.Recognition.NormalFourLargeCoreActionSetup
public import Theory.GroupAction.ExtraspecialThirtyTwoInvolutionFixed

/-!
# Fixed core elements of a Sylow involution

The preimage of the literal quotient two-core is an isomorphic copy of that
core. Conjugation by a Sylow involution is an automorphism of square one.
For an extraspecial core of order thirty-two, its fixed subgroup has order
at least four. Mapping the fixed subgroup through the preimage inclusion
identifies it with the intersection of the core preimage and the involution
centralizer in the original Sylow subgroup.

This supplies the local bound in Janko--Thompson, Math. Z. 113 (1970),
Section 4, printed p.389. The theorem does not require Sylow index two.
-/

open Subgroup

namespace Stellmacher.Recognition.NormalFourCentralOmegaTwo

/-- An involution centralizes at least four elements of the actual extraspecial
core of order thirty-two, computed in the original Sylow subgroup. -/
public theorem omegaCorePreimage_large_core_involution_centralizer_card_ge_four
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) [IsExtraspecial 2 (pCore 2 (OmegaQuotient S))]
    (hH : Nat.card (pCore 2 (OmegaQuotient S)) = 32)
    (t : S) (ht : orderOf t = 2) :
    4 ≤ Nat.card (omegaCorePreimage S ⊓ centralizer ({t} : Set S) : Subgroup S) := by
  let H := omegaCorePreimage S
  let : IsExtraspecial 2 H :=
    IsExtraspecial.of_mulEquiv (omegaCorePreimageEquiv S).symm inferInstance
  let a : MulAut H := MulAut.conjNormal t
  have ha : a ^ 2 = 1 := by
    change (MulAut.conjNormal t : MulAut H) ^ 2 = 1
    rw [← map_pow, show t ^ 2 = 1 by simpa only [ht] using pow_orderOf_eq_one t, map_one]
  let F := FixedPoints.subgroup (zpowers a) H
  have heq : F.map H.subtype = H ⊓ centralizer ({t} : Set S) := by
    ext x
    constructor
    · rintro ⟨u, hu, rfl⟩
      refine ⟨u.property, mem_centralizer_singleton_iff.mpr ?_⟩
      have hh : a u = u :=
        ((FixedPoints.mem_subgroup (M := zpowers a) (a := u)).mp hu) ⟨a, mem_zpowers a⟩
      have hv := congrArg Subtype.val hh
      change t * (u : S) * t⁻¹ = u at hv
      exact (mul_inv_eq_iff_eq_mul.mp hv).symm
    · intro hx
      refine ⟨⟨x, hx.1⟩, ?_, rfl⟩
      have hh : a ⟨x, hx.1⟩ = ⟨x, hx.1⟩ := by
        apply Subtype.ext
        change t * x * t⁻¹ = x
        exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp hx.2).symm
      intro k
      exact smul_eq_self_of_mem_zpowers k.property hh
  have hbound := MulAut.fixed_card_ge_four_of_extraspecial_card_thirty_two
    ((card_omegaCorePreimage S).trans hH) a ha
  have hc : Nat.card (H ⊓ centralizer ({t} : Set S) : Subgroup S) = Nat.card F := by
    rw [← heq]
    exact card_map_of_injective H.subtype_injective
  exact hc.symm ▸ hbound

end Stellmacher.Recognition.NormalFourCentralOmegaTwo
