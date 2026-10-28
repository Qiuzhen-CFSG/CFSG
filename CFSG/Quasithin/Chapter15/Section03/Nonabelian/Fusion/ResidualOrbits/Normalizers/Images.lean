module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Constructions
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.Action
public import Theory.ElementaryAbelian.ExtraspecialCardBound
public import Theory.ElementaryAbelian.Join

/-!
# Exact actor images and block rank calculations in 15.3.61

The literal projection `H → H/O₂(H)` has kernel `U` after 15.3.59(1).
The order formula therefore retains the actual intersection `B ∩ U`.
Extraspeciality bounds that intersection by sixteen, and the intrinsic
rank-two actor bound then forces orders four and sixteen simultaneously.

The actor bound remains an explicit model input; this module does not
claim the source normalizer construction before that calculation is proved.
Source: Aschbacher–Smith, combined manuscript (1 March 2004), p.1151.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.Normalizers
open Recognition
variable {G : Type*} [Group G]

/-- The quotient projection on the source actor. -/
abbrev actorProjection (Z : Subgroup G) : centralizerH Z →* ActorQuotient Z :=
  QuotientGroup.mk' _

/-- The actual faithful action of `H*`, with the specified source kernel. -/
noncomputable def actorAction (Z ZS : Subgroup G)
    [(Z.subgroupOf (closureU Z ZS)).Normal]
    (hkernel : (quotientAction Z ZS).ker = pCore 2 (centralizerH Z)) :
    ActorQuotient Z →* MulAut (VectorQuotient Z ZS) :=
  (quotientAction Z ZS).range.subtype.comp
    (actorQuotientEquivRange Z ZS hkernel).toMonoidHom

theorem actorAction_mk (Z ZS : Subgroup G)
    [(Z.subgroupOf (closureU Z ZS)).Normal]
    (hkernel : (quotientAction Z ZS).ker = pCore 2 (centralizerH Z))
    (h : centralizerH Z) :
    actorAction Z ZS hkernel (actorProjection Z h) = quotientAction Z ZS h := rfl

/-- The kernel membership test uses `U = Q_H`, with both subgroups embedded in `G`. -/
theorem actorProjection_eq_one_iff (Z ZS : Subgroup G)
    (hU : closureU Z ZS = coreQ Z) (h : centralizerH Z) :
    actorProjection Z h = 1 ↔ (h : G) ∈ closureU Z ZS := by
  change QuotientGroup.mk h = 1 ↔ _
  rw [QuotientGroup.eq_one_iff, hU]
  change h ∈ pCore 2 (centralizerH Z) ↔
    (h : G) ∈ (pCore 2 (centralizerH Z)).map (centralizerH Z).subtype
  exact (mem_map_iff_mem (centralizerH Z).subtype_injective).symm

/-- First isomorphism counting with the literal block intersection as kernel. -/
theorem card_eq_actorImage_mul_intersection (Z ZS B : Subgroup G)
    (hBH : B ≤ centralizerH Z) (hU : closureU Z ZS = coreQ Z) :
    Nat.card B = Nat.card (actorImage Z B) *
      Nat.card (B ⊓ closureU Z ZS : Subgroup G) := by
  let f : B →* ActorQuotient Z := (actorProjection Z).comp (inclusion hBH)
  have hr : f.range = actorImage Z B := by
    ext a
    constructor
    · rintro ⟨b, rfl⟩
      exact ⟨inclusion hBH b, b.property, rfl⟩
    · rintro ⟨b, hb, rfl⟩
      exact ⟨⟨b, hb⟩, rfl⟩
  have hk : f.ker = (closureU Z ZS).subgroupOf B := by
    ext b
    exact actorProjection_eq_one_iff Z ZS hU (inclusion hBH b)
  have hc := f.ker.index_mul_card
  rw [index_ker, hr, hk] at hc
  have he : (closureU Z ZS).subgroupOf B ≃* (B ⊓ closureU Z ZS : Subgroup G) :=
    { toFun x := ⟨x, ⟨x.val.property, x.property⟩⟩
      invFun x := ⟨⟨x, x.property.1⟩, x.property.2⟩
      left_inv _ := rfl
      right_inv _ := rfl
      map_mul' _ _ := rfl }
  rw [Nat.card_congr he.toEquiv] at hc
  exact hc.symm

/-- Elementary abelianness is transported through an actual block equivalence. -/
theorem block_elementary (B : Subgroup G)
    (eB : B ≃* Multiplicative (Fin 6 → ZMod 2)) : IsElementaryAbelian 2 B := by
  refine { toIsMulCommutative := ⟨⟨fun x y => eB.injective (by simp [mul_comm])⟩⟩
           exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_ }
  intro b
  apply eB.injective
  rw [map_pow, map_one, pow_two]
  apply Multiplicative.toAdd.injective
  ext i
  change (eB b).toAdd i + (eB b).toAdd i = 0
  exact ZModModule.add_self _

/-- The actual extraspecial group of order 128 bounds the block intersection. -/
theorem intersection_card_le_sixteen [Finite G] (Z ZS B : Subgroup G)
    [IsExtraspecial 2 (closureU Z ZS)] [IsElementaryAbelian 2 B]
    (hcenter : Z.subgroupOf (closureU Z ZS) = center (closureU Z ZS))
    (hZB : Z ≤ B) (hUcard : Nat.card (closureU Z ZS) = 128) :
    Nat.card (B ⊓ closureU Z ZS : Subgroup G) ≤ 16 := by
  let E := B ⊓ closureU Z ZS
  let : IsElementaryAbelian 2 E := {
    toIsMulCommutative := le_centralizer_iff_isMulCommutative.mp
      ((inf_le_left.trans B.le_centralizer).trans (centralizer_le inf_le_left))
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun e =>
      Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (e : G) e.property.1) }
  let : IsElementaryAbelian 2 (E.subgroupOf (closureU Z ZS)) :=
    IsElementaryAbelian.subgroupOf (show E ≤ closureU Z ZS from inf_le_right)
  have hsq := extraspecial_two_elementary_card_sq_le
    (E.subgroupOf (closureU Z ZS)) (by
      rw [← hcenter]
      intro z hz
      exact ⟨hZB hz, z.property⟩)
  rw [Nat.card_congr (subgroupOfEquivOfLe (show E ≤ closureU Z ZS from inf_le_right)).toEquiv,
    hUcard] at hsq
  dsimp only [E] at hsq
  nlinarith

/-- Rank saturation gives the four-group image and the rank-four intersection.
The elementary actor bound is the remaining intrinsic model calculation. -/
theorem block_image_and_intersection_card [Finite G] (Z ZS B : Subgroup G)
    [IsExtraspecial 2 (closureU Z ZS)]
    (eB : B ≃* Multiplicative (Fin 6 → ZMod 2))
    (hBH : B ≤ centralizerH Z) (hU : closureU Z ZS = coreQ Z)
    (hcenter : Z.subgroupOf (closureU Z ZS) = center (closureU Z ZS))
    (hZB : Z ≤ B) (hUcard : Nat.card (closureU Z ZS) = 128)
    (hbound : ∀ A : Subgroup (ActorQuotient Z), IsElementaryAbelian 2 A → Nat.card A ≤ 4) :
    IsElementaryAbelian 2 (actorImage Z B) ∧ Nat.card (actorImage Z B) = 4 ∧
      Nat.card (B ⊓ closureU Z ZS : Subgroup G) = 16 := by
  let : IsElementaryAbelian 2 B := block_elementary B eB
  let : IsElementaryAbelian 2 (B.subgroupOf (centralizerH Z)) :=
    IsElementaryAbelian.subgroupOf hBH
  have hA : IsElementaryAbelian 2 (actorImage Z B) := IsElementaryAbelian.map _
  have hAcard := hbound (actorImage Z B) hA
  have hEcard := intersection_card_le_sixteen Z ZS B hcenter hZB hUcard
  have hBcard : Nat.card B = 64 := by
    rw [Nat.card_congr eB.toEquiv, Nat.card_eq_fintype_card]
    decide
  have hcount := card_eq_actorImage_mul_intersection Z ZS B hBH hU
  rw [hBcard] at hcount
  refine ⟨hA, ?_, ?_⟩ <;> nlinarith

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.Normalizers
