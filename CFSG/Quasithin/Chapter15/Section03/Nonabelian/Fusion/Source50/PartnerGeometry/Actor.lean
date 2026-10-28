module
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry.Kernel

/-!
# The actual partner image in H/O₂(H)

The literal projection on X has kernel X∩Q_H. Thus the source E-order
and the index-two centralizer calculation determine the actor order.
Squares in the conjugate extraspecial group lie in its central line,
which is contained in E; consequently the actual actor image is elementary.
Source: Aschbacher–Smith 15.3.56(3–4), printed pp.1147–1148.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry
open Recognition
variable {G : Type*} [Group G] (Z ZS : Subgroup G)

private theorem actor_mk_eq_one (x : centralizerH Z) :
    QuotientGroup.mk' (pCore 2 (centralizerH Z)) x = 1 ↔ (x : G) ∈ coreQ Z := by
  change (x : centralizerH Z ⧸ pCore 2 (centralizerH Z)) = 1 ↔ _
  rw [QuotientGroup.eq_one_iff]
  constructor
  · exact mem_map_of_mem (centralizerH Z).subtype
  · rintro ⟨u, hu, he⟩
    exact (Subtype.ext he : u = x) ▸ hu

/-- The exact order formula for the literal actor image and its ambient kernel. -/
theorem actor_card_mul_inf_core [Finite G] (X : Subgroup G) (hXH : X ≤ centralizerH Z) :
    Nat.card (X ⊓ coreQ Z : Subgroup G) * Nat.card (actorImage Z X) = Nat.card X := by
  let f : X →* ActorQuotient Z := (QuotientGroup.mk' _).comp (inclusion hXH)
  have hk : f.ker = (X ⊓ coreQ Z).subgroupOf X := by
    ext x
    change f x = 1 ↔ ((x : G) ∈ X ∧ (x : G) ∈ coreQ Z)
    rw [show f x = QuotientGroup.mk' (pCore 2 (centralizerH Z)) (inclusion hXH x) from rfl,
      actor_mk_eq_one]
    exact ⟨fun h => ⟨x.property, h⟩, fun h => h.2⟩
  have hr : f.range = actorImage Z X := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      exact ⟨inclusion hXH x, x.property, rfl⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  have hc := f.ker.card_mul_index
  rw [index_ker, hr, hk, Nat.card_congr (subgroupOfEquivOfLe
    (show X ⊓ coreQ Z ≤ X from inf_le_left)).toEquiv] at hc
  exact hc

/-- The source E-size and index-two F give the required actor order. -/
theorem partner_actor_card [Finite G] (y : G) (s : ℕ)
    (hXH : partnerX Z ZS y ≤ centralizerH Z)
    (hXE : partnerX Z ZS y ⊓ coreQ Z = intersectionE Z ZS y)
    (hindex : (intersectionF Z ZS y).relIndex (closureU Z ZS) = 2)
    (hUcard : Nat.card (closureU Z ZS) = 2 ^ (2*s+5))
    (hEcard : Nat.card (intersectionE Z ZS y) = 2 ^ (s+3)) :
    Nat.card (actorImage Z (partnerX Z ZS y)) = 2 ^ (s+1) := by
  have hF := relIndex_mul_relIndex (⊥ : Subgroup G) (intersectionF Z ZS y)
    (closureU Z ZS) bot_le inf_le_left
  rw [relIndex_bot_left, relIndex_bot_left, hindex, hUcard] at hF
  have hX : Nat.card (partnerX Z ZS y) = Nat.card (intersectionF Z ZS y) :=
    card_map_of_injective (MulAut.conj y⁻¹).injective
  have ha := actor_card_mul_inf_core Z (partnerX Z ZS y) hXH
  rw [hXE, hEcard, hX] at ha
  have he : 2 ^ (s+3) * 2 ^ (s+1) * 2 = 2 ^ (2*s+5) := by
    rw [← pow_add, ← pow_succ]
    congr 1
    omega
  apply Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (by decide : 0 < 2))
  apply Nat.eq_of_mul_eq_mul_right (by decide : 0 < 2)
  rw [ha, hF, he]

/-- The actual quotient image is elementary because conjugate extraspecial
squares lie in the already identified actor kernel. -/
theorem partner_actor_elementary (y : G)
    [IsExtraspecial 2 (rightConjugate (closureU Z ZS) y)]
    (hcenter : center (rightConjugate (closureU Z ZS) y) =
      (rightConjugate Z y).subgroupOf (rightConjugate (closureU Z ZS) y))
    (hZyQ : rightConjugate Z y ≤ coreQ Z) :
    IsElementaryAbelian 2 (actorImage Z (partnerX Z ZS y)) := by
  have hXUy : partnerX Z ZS y ≤ rightConjugate (closureU Z ZS) y := map_mono inf_le_left
  let P := rightConjugate (closureU Z ZS) y
  let := IsExtraspecial.quotient_elementary_abelian 2 P
  have hsquare (x : G) (hx : x ∈ partnerX Z ZS y) : x^2 ∈ rightConjugate Z y := by
    let a : P := ⟨x, hXUy hx⟩
    have hq := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 (P ⧸ center P))
      (QuotientGroup.mk' (center P) a)
    rw [← map_pow] at hq
    have hq' : a^2 ∈ center P := (QuotientGroup.eq_one_iff _).mp hq
    rw [hcenter] at hq'
    exact hq'
  have hp (a : actorImage Z (partnerX Z ZS y)) : a^2 = 1 := by
    obtain ⟨x, hx, he⟩ := a.property
    apply Subtype.ext
    change (a : ActorQuotient Z)^2 = 1
    rw [← he, ← map_pow]
    exact (actor_mk_eq_one Z (x^2)).mpr (hZyQ (hsquare x hx))
  exact {
    toIsMulCommutative := ⟨⟨fun a b =>
      (Commute.of_orderOf_dvd_two (fun x => orderOf_dvd_of_pow_eq_one (hp x)) a b).eq⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hp }

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry
