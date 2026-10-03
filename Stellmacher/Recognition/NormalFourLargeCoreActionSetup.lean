module

public import Stellmacher.Recognition.NormalFourNonnormalCoreSetup
public import Theory.GroupTheory.PGroup.RankTwoExtraspecialThirtyTwo
public import Theory.GroupTheory.PCoreFrattiniAction

/-!
# The faithful action of the order-thirty-two actual core

In the literal quotient of the central-omega normalizer by its odd core,
rank two identifies an extraspecial core of order thirty-two as the internal
quaternion-dihedral central product. Self-centralization proves that the
quotient by the core acts faithfully on its Frattini quotient of order sixteen.
The original Sylow core preimage is an isomorphic extraspecial group.

This module prepares the outer-action calculation independently of the
higher-index fusion assembly. Source: Janko–Thompson, Math. Z. 113 (1970),
§4, printed p.389, the quaternion-dihedral case.
-/

namespace Stellmacher.Recognition.NormalFourCentralOmegaTwo

open Subgroup

variable {G : Type*} [Group G] [Finite G]

/-- The actual order-thirty-two quotient core has the minus-type factors. -/
public theorem omegaQuotient_large_core_dihedral_quaternion
    (hrank : ∀ U : Subgroup G, IsElementaryAbelian 2 U → Nat.card U < 8)
    (S : Sylow 2 G) [IsExtraspecial 2 (pCore 2 (OmegaQuotient S))]
    (hH : Nat.card (pCore 2 (OmegaQuotient S)) = 32) :
    ∃ U V : Subgroup (pCore 2 (OmegaQuotient S)),
      Nonempty (U ≃* QuaternionGroup 2) ∧ Nonempty (V ≃* DihedralGroup 4) ∧
      V ≤ centralizer (U : Set (pCore 2 (OmegaQuotient S))) ∧
      U ⊔ V = ⊤ ∧ Nat.card (U ⊓ V : Subgroup (pCore 2 (OmegaQuotient S))) = 2 := by
  apply IsExtraspecial.dihedral_quaternion_factors_of_card_thirty_two
    (elementary_card_lt_eight_of_subgroup ?_ (pCore 2 (OmegaQuotient S))) hH
  intro U hU
  let : IsElementaryAbelian 2 U := hU
  exact omegaQuotient_rank hrank S U

/-- The core preimage in the original Sylow is extraspecial of order thirty-two. -/
public theorem omegaCorePreimage_large_core_structure
    (S : Sylow 2 G) [IsExtraspecial 2 (pCore 2 (OmegaQuotient S))]
    (hH : Nat.card (pCore 2 (OmegaQuotient S)) = 32) :
    IsExtraspecial 2 (omegaCorePreimage S) ∧ Nat.card (omegaCorePreimage S) = 32 :=
  ⟨IsExtraspecial.of_mulEquiv (omegaCorePreimageEquiv S).symm inferInstance,
    (card_omegaCorePreimage S).trans hH⟩

/-- Conjugation on the Frattini quotient of the literal quotient core. -/
public noncomputable def omegaCoreFrattiniAction (S : Sylow 2 G) :
    OmegaQuotient S →*
      MulAut (pCore 2 (OmegaQuotient S) ⧸ frattini (pCore 2 (OmegaQuotient S))) :=
  (quotientAut (frattini (pCore 2 (OmegaQuotient S)))).comp MulAut.conjNormal

omit [Finite G] in
/-- On representatives the canonical action is actual conjugation on the core. -/
public theorem omegaCoreFrattiniAction_apply_mk (S : Sylow 2 G)
    (g : OmegaQuotient S) (x : pCore 2 (OmegaQuotient S)) :
    omegaCoreFrattiniAction S g (QuotientGroup.mk' (frattini (pCore 2 (OmegaQuotient S))) x) =
      QuotientGroup.mk' (frattini (pCore 2 (OmegaQuotient S))) (MulAut.conjNormal g x) :=
  quotientAut_apply_mk _ _ _

/-- Self-centralization makes the canonical action kernel exactly the core. -/
public theorem omegaCoreFrattiniAction_kernel
    (hN : IsNTwoGroup G) (S : Sylow 2 G)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2) :
    (omegaCoreFrattiniAction S).ker = pCore 2 (OmegaQuotient S) :=
  pCore_frattini_action_kernel 2 (omegaQuotient_centralizer_pCore_le hN S hZ)

/-- The quotient by the actual core embeds in the automorphisms of its
Frattini quotient; faithfulness is proved from N₂, not assumed. -/
public theorem omegaQuotient_core_quotient_faithful
    (hN : IsNTwoGroup G) (S : Sylow 2 G)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2) :
    ∃ f : (OmegaQuotient S ⧸ pCore 2 (OmegaQuotient S)) →*
      MulAut (pCore 2 (OmegaQuotient S) ⧸ frattini (pCore 2 (OmegaQuotient S))),
      Function.Injective f := by
  have hk := omegaCoreFrattiniAction_kernel hN S hZ
  refine ⟨QuotientGroup.lift _ (omegaCoreFrattiniAction S) hk.symm.le, ?_⟩
  exact (QuotientGroup.injective_lift_iff _ _ _).mpr hk.symm

/-- The faithful action space for the large core has precisely sixteen elements. -/
public theorem omegaQuotient_large_core_frattini_card
    (S : Sylow 2 G) [IsExtraspecial 2 (pCore 2 (OmegaQuotient S))]
    (hH : Nat.card (pCore 2 (OmegaQuotient S)) = 32) :
    Nat.card (pCore 2 (OmegaQuotient S) ⧸ frattini (pCore 2 (OmegaQuotient S))) = 16 :=
  IsExtraspecial.card_frattini_quotient_of_card_thirty_two hH

/-- An action with kernel the actual core identifies the original Sylow
quotient with a Sylow subgroup of the literal action range. -/
public theorem omegaCorePreimage_quotient_equiv_sylow_range
    (S : Sylow 2 G) {A : Type*} [Group A]
    (f : OmegaQuotient S →* A) (hker : f.ker = pCore 2 (OmegaQuotient S)) :
    ∃ R : Sylow 2 f.range, Nonempty ((S ⧸ omegaCorePreimage S) ≃* R) := by
  let R := (omegaQuotientSylow S).mapSurjective f.rangeRestrict_surjective
  let g := f.rangeRestrict.comp (omegaQuotientHom S)
  have hgker : g.ker = omegaCorePreimage S := by
    rw [← MonoidHom.comap_ker, MonoidHom.ker_rangeRestrict, hker]
  have hgrange : g.range = (R : Subgroup f.range) := by
    rw [MonoidHom.range_comp, omegaQuotientHom_range]
    rfl
  exact ⟨R, ⟨((QuotientGroup.quotientMulEquivOfEq hgker.symm).trans
    (QuotientGroup.quotientKerEquivRange g)).trans (MulEquiv.subgroupCongr hgrange)⟩⟩

end Stellmacher.Recognition.NormalFourCentralOmegaTwo
