module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.Extraspecial.Coordinates
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.Extraspecial.Outside
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.LocalProduct
public import Theory.GroupTheory.CentralBinaryPairingCardinality

/-!
# Relative centralizers of the fixed lift

The actual U-action on V has image of order four. First-isomorphism
counting gives |C_U(V)| = 32. Extraspecial commutator duality independently
gives |C_U(U ∩ V)| = 32 from |U| = 128 and |U ∩ V| = 8. Thus a fixed
lift of order 32 is both relative centralizers. All subgroups stay embedded
in G; the pairing calculation takes place inside U.

The order of the fixed lift is an explicit intermediate premise here;
it is discharged by the natural-plus-dual transvection calculation.
Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.53 and the first paragraph proving 15.3.61(2), pp.1146,1150.
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter15.Section03.Nonabelian
open CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.Extraspecial.FixedLift
variable {G : Type*} [Group G] {Z ZS V : Subgroup G}
variable [(Z.subgroupOf (closureU Z ZS)).Normal]

/-- The fixed lift lies in the literal U. -/
theorem le_closure (a : centralizerH Z) : fixedLift Z ZS a ≤ closureU Z ZS := map_subtype_le _

/-- The relative centralizer of V has fixed image under every a in V. -/
theorem centralizer_le (a : centralizerH Z) (haV : (a : G) ∈ V) :
    closureU Z ZS ⊓ centralizer (V : Set G) ≤ fixedLift Z ZS a := by
  intro x hx
  apply (mem_fixedLift_iff Z ZS a x).mpr
  refine ⟨hx.1, ?_⟩
  rw [quotientAction_mk]
  apply congrArg (QuotientGroup.mk' (Z.subgroupOf (closureU Z ZS)))
  apply Subtype.ext
  change (a : G) * x * (a : G)⁻¹ = x
  rw [hx.2 _ haV, mul_inv_cancel_right]

/-- The conjugation homomorphism of U on V, with no coordinate choices. -/
noncomputable def actionOnV (hUV : closureU Z ZS ≤ normalizer (V : Set G)) :
    closureU Z ZS →* MulAut V := V.normalizerMonoidHom.comp (inclusion hUV)

variable [Finite G]

omit [(Z.subgroupOf (closureU Z ZS)).Normal] [Finite G] in
/-- The genuine order-four action image gives a centralizer of order 32. -/
theorem card_centralizer_V
    (hUV : closureU Z ZS ≤ normalizer (V : Set G))
    (himage : Nat.card (actionOnV hUV).range = 4)
    (hU : Nat.card (closureU Z ZS) = 128) :
    Nat.card (closureU Z ZS ⊓ centralizer (V : Set G) : Subgroup G) = 32 := by
  let f := actionOnV hUV
  have hk : f.ker = (centralizer (V : Set G)).subgroupOf (closureU Z ZS) := by
    ext x
    change inclusion hUV x ∈ V.normalizerMonoidHom.ker ↔ _
    rw [normalizerMonoidHom_ker]
    rfl
  have hc := f.ker.index_mul_card
  rw [index_ker, show Nat.card f.range = 4 from himage, hk, hU] at hc
  have he : Nat.card ((centralizer (V : Set G)).subgroupOf (closureU Z ZS)) =
      Nat.card (closureU Z ZS ⊓ centralizer (V : Set G) : Subgroup G) := by
    rw [← card_map_of_injective (closureU Z ZS).subtype_injective,
      subgroupOf_map_subtype, inf_comm]
  rw [he] at hc
  omega

omit [(Z.subgroupOf (closureU Z ZS)).Normal] in
/-- Extraspecial commutator duality counts the relative centralizer of U ∩ V. -/
theorem card_centralizer_intersection [IsExtraspecial 2 (closureU Z ZS)]
    [IsElementaryAbelian 2 V]
    (hcenter : Z.subgroupOf (closureU Z ZS) = center (closureU Z ZS))
    (hZV : Z ≤ V) (hU : Nat.card (closureU Z ZS) = 128)
    (hW : Nat.card (closureU Z ZS ⊓ V : Subgroup G) = 8) :
    Nat.card (closureU Z ZS ⊓ centralizer ((closureU Z ZS ⊓ V : Subgroup G) : Set G) :
      Subgroup G) = 32 := by
  let U := closureU Z ZS
  let E := V.subgroupOf U
  let : IsElementaryAbelian 2 E := by
    refine { toIsMulCommutative := ⟨⟨?_⟩⟩, exponent_dvd_p := ?_ }
    · intro x y
      apply Subtype.ext
      apply Subtype.ext
      change ((x : U) : G) * ((y : U) : G) = ((y : U) : G) * ((x : U) : G)
      exact congrArg (fun v : V => (v : G)) (mul_comm (⟨x, x.property⟩ : V) (⟨y, y.property⟩ : V))
    · apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
      intro x
      apply Subtype.ext
      apply Subtype.ext
      exact elemPow_eq_one_of_isElementaryAbelian (x : G) x.property
  let := IsExtraspecial.quotient_elementary_abelian 2 U
  have hZE : center U ≤ E := by
    rw [← hcenter]
    exact fun x hx => hZV hx
  have hcomm : ⁅E, (⊤ : Subgroup U)⁆ ≤ center U :=
    (commutator_mono le_top le_rfl).trans
      (IsExtraspecial.quotient_elementary_abelian 2 U).commutator_le_center_of_central_quotient
  have hc := card_mul_card_centralizer_of_central_binary_pairing (center U) E hZE
    (IsExtraspecial.center_order_p 2 U) hcomm (center_le_centralizer _)
  have hEc : Nat.card E = 8 := by
    rw [← card_map_of_injective U.subtype_injective, subgroupOf_map_subtype, inf_comm]
    exact hW
  have he : (centralizer (E : Set U)).map U.subtype =
      U ⊓ centralizer ((U ⊓ V : Subgroup G) : Set G) := by
    ext x
    constructor
    · rintro ⟨u, hu, rfl⟩
      refine ⟨u.property, fun v hv => ?_⟩
      exact congrArg Subtype.val (hu ⟨v, hv.1⟩ hv.2)
    · intro hx
      exact ⟨⟨x, hx.1⟩, fun v hv => Subtype.ext (hx.2 v ⟨v.property, hv⟩), rfl⟩
  rw [hEc, show Nat.card U = 128 from hU,
    ← card_map_of_injective U.subtype_injective, he] at hc
  dsimp only [U] at hc
  omega

/-- Once the transvection fixed space has been counted, both source centralizer
identities follow from the actual conjugation image and extraspecial duality. -/
theorem eq_centralizers_of_card [IsExtraspecial 2 (closureU Z ZS)]
    [IsElementaryAbelian 2 V]
    (a : centralizerH Z) (haV : (a : G) ∈ V)
    (hcenter : Z.subgroupOf (closureU Z ZS) = center (closureU Z ZS))
    (hZV : Z ≤ V) (hU : Nat.card (closureU Z ZS) = 128)
    (hW : Nat.card (closureU Z ZS ⊓ V : Subgroup G) = 8)
    (hUV : closureU Z ZS ≤ normalizer (V : Set G))
    (himage : Nat.card (actionOnV hUV).range = 4)
    (hfixed : Nat.card (fixedLift Z ZS a) = 32) :
    fixedLift Z ZS a = closureU Z ZS ⊓ centralizer (V : Set G) ∧
      fixedLift Z ZS a = closureU Z ZS ⊓
        centralizer ((closureU Z ZS ⊓ V : Subgroup G) : Set G) := by
  have hC := card_centralizer_V hUV himage hU
  have hE := card_centralizer_intersection hcenter hZV hU hW
  have hfirst := (eq_of_le_of_card_ge (centralizer_le (ZS := ZS) a haV) (by omega)).symm
  refine ⟨hfirst, ?_⟩
  rw [hfirst]
  apply eq_of_le_of_card_ge
    (inf_le_inf_left _ (Subgroup.centralizer_le (show ((closureU Z ZS ⊓ V : Subgroup G) : Set G) ⊆ V from inf_le_right)))
  omega
end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.Extraspecial.FixedLift
