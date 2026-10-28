module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.Normalizers.Images
public import Theory.ElementaryAbelian.ExtraspecialAbelianBound
public import Theory.GroupAction.CommonFixedNormalizer
public import Theory.GroupAction.SubgroupQuotientSupportLift
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# Recovering a block from its intersection with the extraspecial group

The image of `E = B ∩ U` lies in the fixed subgroup of the actual actor `B*`.
Equality follows from the calculated orders. Saturation of the extraspecial
abelian bound gives `C_U(E)=E`. If the pointwise stabilizer of its quotient
image is `B*`, cancellation of an actor representative gives `C_H(E)=B`,
and hence the source equality `C_TK(E)=B`.

The finite model fixed-space order and pointwise-stabilizer calculation are
explicit inputs here; they are not asserted as source results.
Source: Aschbacher–Smith, combined manuscript (1 March 2004), p.1151.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.Normalizers
open Recognition
variable {G : Type*} [Group G]
variable (Z ZS : Subgroup G) [(Z.subgroupOf (closureU Z ZS)).Normal]

/-- A subgroup of `U` containing `Z` is the full lift of its literal image. -/
theorem vectorImage_full_lift (E : Subgroup G)
    (hEU : E ≤ closureU Z ZS) (hZE : Z ≤ E) :
    ((vectorImage Z ZS E).comap (QuotientGroup.mk' (Z.subgroupOf (closureU Z ZS)))).map
      (closureU Z ZS).subtype = E := by
  rw [vectorImage, comap_map_eq_self, map_subgroupOf_eq_of_le hEU]
  rw [QuotientGroup.ker_mk']
  exact comap_mono hZE

/-- Exact order of the vector image; the kernel is the whole marked center. -/
theorem vectorImage_card_mul_center (E : Subgroup G)
    (hEU : E ≤ closureU Z ZS) (hZE : Z ≤ E) :
    Nat.card (vectorImage Z ZS E) * Nat.card Z = Nat.card E := by
  have h := (lift_support_basic (closureU Z ZS) Z (hZE.trans hEU)
    (vectorImage Z ZS E)).2.2.1
  rw [vectorImage_full_lift Z ZS E hEU hZE] at h
  exact h.symm

/-- An abelian block fixes the image of its actual intersection with `U`. -/
theorem vectorImage_intersection_le_fixed (B : Subgroup G) [IsMulCommutative B]
    (hkernel : (quotientAction Z ZS).ker = pCore 2 (centralizerH Z)) :
    vectorImage Z ZS (B ⊓ closureU Z ZS) ≤
      (actorAction Z ZS hkernel).commonFixed (actorImage Z B) := by
  rintro w ⟨u, hu, rfl⟩
  rw [MonoidHom.mem_commonFixed]
  rintro a ⟨b, hb, rfl⟩
  rw [actorAction_mk, quotientAction_mk]
  congr 1
  apply Subtype.ext
  have hc : (b : G) * (u : G) = (u : G) * (b : G) :=
    congrArg Subtype.val (mul_comm (⟨b, hb⟩ : B) (⟨u, hu.1⟩ : B))
  change (b : G) * (u : G) * (b : G)⁻¹ = u
  rw [hc, mul_inv_cancel_right]

/-- The model fixed-space order forces equality with the literal image of `E`.
Neither fixed-space containment nor equality is an input. -/
theorem vectorImage_intersection_eq_fixed [Finite G] (B : Subgroup G)
    [IsMulCommutative B]
    (hkernel : (quotientAction Z ZS).ker = pCore 2 (centralizerH Z))
    (hZU : Z ≤ closureU Z ZS) (hZB : Z ≤ B) (hZ : Nat.card Z = 2)
    (hE : Nat.card (B ⊓ closureU Z ZS : Subgroup G) = 16)
    (hfixed : Nat.card ((actorAction Z ZS hkernel).commonFixed (actorImage Z B)) = 8) :
    vectorImage Z ZS (B ⊓ closureU Z ZS) =
      (actorAction Z ZS hkernel).commonFixed (actorImage Z B) := by
  apply eq_of_le_of_card_ge (vectorImage_intersection_le_fixed Z ZS B hkernel)
  have hcount := vectorImage_card_mul_center Z ZS (B ⊓ closureU Z ZS)
    inf_le_right (le_inf hZB hZU)
  rw [hZ, hE] at hcount
  rw [hfixed]
  omega

omit [(Z.subgroupOf (closureU Z ZS)).Normal] in
/-- Saturation makes the rank-four intersection self-centralizing in `U`. -/
theorem intersection_centralizer_in_U [Finite G] (B : Subgroup G)
    [IsExtraspecial 2 (closureU Z ZS)] [IsMulCommutative B]
    (hcenter : Z.subgroupOf (closureU Z ZS) = center (closureU Z ZS))
    (hZB : Z ≤ B) (hUcard : Nat.card (closureU Z ZS) = 128)
    (hE : Nat.card (B ⊓ closureU Z ZS : Subgroup G) = 16) :
    closureU Z ZS ⊓ centralizer ((B ⊓ closureU Z ZS : Subgroup G) : Set G) =
      B ⊓ closureU Z ZS := by
  let E := B ⊓ closureU Z ZS
  let EU := E.subgroupOf (closureU Z ZS)
  let : IsMulCommutative E := le_centralizer_iff_isMulCommutative.mp
    ((inf_le_left.trans B.le_centralizer).trans (centralizer_le inf_le_left))
  have hEU : Nat.card EU = 16 :=
    (Nat.card_congr (subgroupOfEquivOfLe (show E ≤ closureU Z ZS from inf_le_right)).toEquiv).trans hE
  have hself : centralizer (EU : Set (closureU Z ZS)) = EU :=
    extraspecial_two_centralizer_eq_of_card_sq EU
      (by rw [← hcenter]; intro z hz; exact ⟨hZB hz, z.property⟩)
      (by rw [hEU, hUcard]; decide)
  apply le_antisymm
  · intro u hu
    have hc : (⟨u, hu.1⟩ : closureU Z ZS) ∈ centralizer (EU : Set (closureU Z ZS)) := by
      intro e he
      exact Subtype.ext (mem_centralizer_iff.mp hu.2 e he)
    rw [hself] at hc
    exact hc
  · exact le_inf inf_le_right E.le_centralizer

/-- Pointwise fixation upstairs implies pointwise fixation of the actual vector image. -/
theorem actor_fixes_vectorImage (E : Subgroup G)
    (hkernel : (quotientAction Z ZS).ker = pCore 2 (centralizerH Z))
    (h : centralizerH Z) (hc : (h : G) ∈ centralizer (E : Set G)) :
    ∀ w ∈ vectorImage Z ZS E, actorAction Z ZS hkernel (actorProjection Z h) w = w := by
  rintro w ⟨u, hu, rfl⟩
  rw [actorAction_mk, quotientAction_mk]
  congr 1
  apply Subtype.ext
  change (h : G) * (u : G) * (h : G)⁻¹ = u
  rw [← mem_centralizer_iff.mp hc u hu, mul_inv_cancel_right]

/-- Recover the full centralizer in `H` from its model pointwise-fixer calculation.
A block representative removes the actor, and the exact kernel then lies in
`C_U(E)=E`. This also proves the required centralizer equality inside `T_K`. -/
theorem block_eq_H_centralizer (B : Subgroup G) [IsMulCommutative B]
    (hBH : B ≤ centralizerH Z) (hU : closureU Z ZS = coreQ Z)
    (hkernel : (quotientAction Z ZS).ker = pCore 2 (centralizerH Z))
    (hself : closureU Z ZS ⊓ centralizer ((B ⊓ closureU Z ZS : Subgroup G) : Set G) =
      B ⊓ closureU Z ZS)
    (hfixer : ∀ a : ActorQuotient Z,
      (∀ w ∈ vectorImage Z ZS (B ⊓ closureU Z ZS), actorAction Z ZS hkernel a w = w) →
        a ∈ actorImage Z B) :
    B = centralizerH Z ⊓ centralizer ((B ⊓ closureU Z ZS : Subgroup G) : Set G) := by
  apply le_antisymm
  · exact le_inf hBH (B.le_centralizer.trans (centralizer_le inf_le_left))
  · intro h hh
    let hH : centralizerH Z := ⟨h, hh.1⟩
    have ha := hfixer (actorProjection Z hH)
      (actor_fixes_vectorImage Z ZS _ hkernel hH hh.2)
    obtain ⟨b, hb, he⟩ := ha
    have hk : actorProjection Z (hH * b⁻¹) = 1 := by
      rw [map_mul, map_inv, he, mul_inv_cancel]
    have hu : h * (b : G)⁻¹ ∈ closureU Z ZS :=
      (actorProjection_eq_one_iff Z ZS hU (hH * b⁻¹)).mp hk
    have hbC : (b : G) ∈ centralizer ((B ⊓ closureU Z ZS : Subgroup G) : Set G) :=
      B.le_centralizer.trans (centralizer_le inf_le_left) hb
    have hd : h * (b : G)⁻¹ ∈ B ⊓ closureU Z ZS := by
      rw [← hself]
      exact ⟨hu, (centralizer ((B ⊓ closureU Z ZS : Subgroup G) : Set G)).mul_mem
        hh.2 ((centralizer ((B ⊓ closureU Z ZS : Subgroup G) : Set G)).inv_mem hbC)⟩
    have hm := B.mul_mem hd.1 hb
    change h * (b : G)⁻¹ * (b : G) ∈ B at hm
    simpa only [inv_mul_cancel_right] using hm

omit [(Z.subgroupOf (closureU Z ZS)).Normal] in
/-- The whole-`H` equality implies the printed relative centralizer equality. -/
theorem block_eq_residualSylow_centralizer (T B : Subgroup G)
    (hBT : B ≤ residualSylow T Z)
    (hcentral : B = centralizerH Z ⊓
      centralizer ((B ⊓ closureU Z ZS : Subgroup G) : Set G)) :
    B = residualSylow T Z ⊓ centralizer ((B ⊓ closureU Z ZS : Subgroup G) : Set G) := by
  apply le_antisymm
  · exact le_inf hBT (hcentral.le.trans inf_le_right)
  · intro x hx
    apply hcentral.ge
    exact ⟨(map_subtype_le (Stellmacher.twoResidualSubgroup (centralizerH Z))) hx.1.2, hx.2⟩

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.Normalizers
