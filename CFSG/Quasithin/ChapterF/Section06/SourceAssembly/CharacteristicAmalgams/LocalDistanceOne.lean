module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.CharacteristicAmalgams.LocalContext
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.CharacteristicAmalgams.LocalDistanceOne.LocalGeometry

/-!
# Cubic exclusion of commuting critical distance one

The local argument in Stellmacher (9.1)(1)--(4) constructs a two-subgroup
V of the initial vertex with |V : V ∩ Qα| at least four. For an actual S₃
vertex quotient every two-subgroup has image of order at most two. Thus
commuting critical pairs in a characteristic-two Goldschmidt amalgam have
distance greater than one, without any ambient Hypothesis Two.

Source: Stellmacher, Journal of Algebra 190 (1997), (9.1), p.46, and
Aschbacher--Smith F.6.1--F.6.4 for the literal S₃ vertex quotients.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Stellmacher.Later Stellmacher.SectionsFiveToSeven
open Stellmacher.SectionsFiveToSeven.CosetGraphContext
namespace Stellmacher.SectionNine.LocalDistanceOne

private theorem two_subgroup_card_le_twice_intersection
    {H : Type*} [Group H] [Finite H]
    (Q V : Subgroup H) [Q.Normal] (hindex : Q.index = 6)
    (hV : IsPGroup 2 V) : Nat.card V ≤ 2 * Nat.card (V ⊓ Q : Subgroup H) := by
  have hd : Q.relIndex V ∣ 6 := hindex ▸ Q.relIndex_dvd_index_of_normal V
  obtain ⟨n, hn⟩ := hV.index (Q.subgroupOf V)
  change Q.relIndex V = 2 ^ n at hn
  have hcop : Nat.Coprime (Q.relIndex V) 3 := by
    rw [hn]
    exact (by decide : Nat.Coprime 2 3).pow_left n
  have hd2 : Q.relIndex V ∣ 2 := hcop.dvd_mul_right.mp hd
  have hsmall : Q.relIndex V ≤ 2 := Nat.le_of_dvd (by decide) hd2
  have hm := relIndex_mul_relIndex (⊥ : Subgroup H) (V ⊓ Q) V bot_le inf_le_left
  simp only [relIndex_bot_left, inf_relIndex_left] at hm
  nlinarith

/-- Local cubic geometry rules out the commuting distance-one branch. -/
theorem critical_length_ne_one_of_core_index_six
    {G : Type*} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (hindex : (pCore 2 (stabilizer ctx.Γ ctx.criticalPath.a)).index = 6) :
    ctx.criticalPath.length ≠ 1 := by
  intro hb
  obtain ⟨data⟩ := distance_one_initial_geometry ctx hb
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let next := Γ.act data.x⁻¹ cp.a
  let C := z Γ cp.a ⊓ stabilizer Γ next
  let D := z Γ next ⊓ stabilizer Γ cp.a
  let V := C ⊔ D
  let P := stabilizer Γ cp.a
  have hfactors := distance_one_product_factors Γ cp.a next
  have hVP : V ≤ P := hfactors.2.2.1.trans inf_le_left
  have hn : cp.a' ∈ neighborhood Γ cp.a := by
    rw [neighborhood, Γ.neighbors_def]
    exact (Γ.distance_symm _ _).trans (cp.endpoint_distance.trans hb)
  let _ := SevenSix.z_isElementaryAbelian_of_neighbor ctx.sectionSeven Γ hn
  have hfirst : IsPGroup 2 (z Γ cp.a) := IsElementaryAbelian.isPGroup 2 _
  have hsecond : IsPGroup 2 (z Γ next) := by
    dsimp only [next]
    rw [z_act, inv_inv]
    exact hfirst.map _
  have hV : IsPGroup 2 V :=
    (hfirst.to_le (show C ≤ z Γ cp.a from inf_le_left)).to_sup_of_normal_right'
      (hsecond.to_le inf_le_left) hfactors.1
  have hsub : IsPGroup 2 (V.subgroupOf P) :=
    hV.of_equiv (subgroupOfEquivOfLe hVP).symm
  have hbound := two_subgroup_card_le_twice_intersection (pCore 2 P) (V.subgroupOf P)
    hindex hsub
  have heq : (V.subgroupOf P) ⊓ pCore 2 P = (V ⊓ q Γ cp.a).subgroupOf P := by
    rw [q, Γ.twoCoreAt_def]
    change V.comap P.subtype ⊓ pCore 2 P =
      (V ⊓ (pCore 2 P).map P.subtype).comap P.subtype
    rw [comap_inf, comap_map_eq_self_of_injective P.subtype_injective]
  rw [heq, Nat.card_congr (subgroupOfEquivOfLe hVP).toEquiv,
    Nat.card_congr (subgroupOfEquivOfLe (inf_le_left.trans hVP)).toEquiv] at hbound
  have hlarge := (distance_one_local_geometry ctx hb data).2.2
  change 4 * Nat.card (V ⊓ q Γ cp.a : Subgroup G) ≤ Nat.card V at hlarge
  have hpos : 0 < Nat.card (V ⊓ q Γ cp.a : Subgroup G) := Nat.card_pos
  omega

end Stellmacher.SectionNine.LocalDistanceOne

namespace CFSG.Quasithin.ChapterF
universe u
variable {G : Type u} [Group G] [Finite G] {G₁ G₂ : Subgroup G}

/-- The actual Goldschmidt graph has no commuting critical path of length one. -/
theorem IsGoldschmidtTriple.critical_length_gt_one_of_commuting
    (h : IsGoldschmidtTriple G₁ G₂) (hcore : pCore 2 G = ⊥)
    (hgood₁ : generalizedFitting G₁ = pCore 2 G₁)
    (hgood₂ : generalizedFitting G₂ = pCore 2 G₂)
    (Γ : CosetGraphContext.{u,u} G (G₁ ⊓ G₂) G₁ G₂) (cp : CriticalPath Γ)
    (hcomm : ⁅Γ.z cp.a, Γ.z cp.a'⁆ = ⊥) : 1 < cp.length := by
  let ctx : SectionNineLocalContext G (G₁ ⊓ G₂) G₁ G₂ :=
    ⟨h.sectionSeven_of_characteristic_two hcore hgood₁ hgood₂, Γ, cp, hcomm⟩
  have hindex : (pCore 2 (stabilizer Γ cp.a)).index = 6 := by
    rcases cp.edge_stabilizers_are_P with he | he
    · rw [he.1]
      change Nat.card (G₁ ⧸ pCore 2 G₁) = 6
      rw [Nat.card_congr h.quotient_left.some.toEquiv]
      norm_num [Nat.card_eq_fintype_card, Fintype.card_perm]
    · rw [he.1]
      change Nat.card (G₂ ⧸ pCore 2 G₂) = 6
      rw [Nat.card_congr h.quotient_right.some.toEquiv]
      norm_num [Nat.card_eq_fintype_card, Fintype.card_perm]
  have hne := Stellmacher.SectionNine.LocalDistanceOne.critical_length_ne_one_of_core_index_six ctx hindex
  have hpos := cp.length_pos
  change cp.length ≠ 1 at hne
  omega

end CFSG.Quasithin.ChapterF
