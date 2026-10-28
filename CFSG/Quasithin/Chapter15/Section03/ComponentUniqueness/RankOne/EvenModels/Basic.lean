module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.FourGroup
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Containment.RankOnePlane.Recognition
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ComponentIntersection.Basic
public import Theory.GroupTheory.SylowSubnormalIntersection

/-!
# The original four-group and the residual actor

The local normalizer identity puts `S` in `N(Y₊)`. Consequently
`V₂ = [V₂,Y₊]` lies in `Y₊`, and hence in the component itself. If a
concrete component calculation makes this four-group self-centralizing,
the order-three generation of `Y₊` identifies the original actor with A₄.
This avoids trying to lift an isomorphism from the action quotient.

The final centralizer obstruction likewise concerns the original groups:
the fixed plane `V₁` distinguishes `C_S(Y₊)` from `C_S(L)`.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
15.3.43(b)--(e) and its characteristic-two cases, printed pp.1139--1140.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.RankOne.EvenModels

variable {G : Type*} [Group G] {Yplus S M I L V₁ V₂ : Subgroup G}
variable (c : ReducedConfiguration Yplus S M I L V₁ V₂)
include c

theorem sylow_le_local : S ≤ M ⊓ I :=
  le_inf c.sylow_le_M (le_sup_right.trans c.minimal.1.1.2)

theorem actor_le_local : Yplus ≤ M ⊓ I := by
  rw [← c.theta_eq]
  exact theta_le _

theorem local_normalizes_actor : M ⊓ I ≤ normalizer (Yplus : Set G) :=
  c.normalizer_eq.ge.trans inf_le_right

/-- The normal four-group is contained in the actual actor, before quotienting. -/
theorem plane_le_actor : V₂ ≤ Yplus := by
  rw [← c.plane_two_commutator]
  exact le_normalizer_iff_commutator_le_right.mp
    (c.plane_two_le.trans ((sylow_le_local c).trans (local_normalizes_actor c)))

theorem plane_le_component : V₂ ≤ L := (plane_le_actor c).trans c.y_le_component

theorem plane_isKleinFour : IsKleinFour V₂ := by
  let : IsElementaryAbelian 2 V₂ := c.plane_two_elementary
  let : Finite V₂ := Nat.finite_of_card_ne_zero (by rw [c.plane_two_card]; decide)
  let : Nontrivial V₂ := Finite.one_lt_card_iff_nontrivial.mp (by
    rw [c.plane_two_card]
    decide)
  exact ⟨c.plane_two_card, IsElementaryAbelian.exponent_eq_prime⟩

theorem actor_isPPerfect [Finite G] : IsPPerfect 2 Yplus :=
  c.theta_eq ▸ ComponentIntersection.theta_isPPerfect (M ⊓ I)

/-- The embedded centre identity is also an intrinsic identity in `L`. -/
theorem center_eq_twoCore : center L = pCore 2 L :=
  Subgroup.map_injective L.subtype_injective c.component_center

/-- In particular the triple-cover alternative in 1.1.5(c) cannot survive
the already established component-centre condition. -/
theorem center_card_ne_three [Finite G] : Nat.card (center L) ≠ 3 := by
  have hp : IsPGroup 2 (center L) := by
    rw [center_eq_twoCore c]
    exact pCore_isPGroup
  obtain ⟨k, hk⟩ := hp.exists_card_eq
  have hcop : Nat.Coprime 3 (Nat.card (center L)) := by
    rw [hk]
    exact (by decide : Nat.Coprime 3 2).pow_right k
  intro hc
  rw [hc] at hcop
  norm_num at hcop

/-- Restrict the given Sylow subgroup to the actual component. -/
theorem component_sylow [Finite G] :
    ∃ P : Sylow 2 L, (P : Subgroup L).map L.subtype = S ⊓ L := by
  obtain ⟨P, hP⟩ := c.sylow
  obtain ⟨Q, hQ⟩ := P.exists_subgroupOf_eq_of_subnormal (L.subgroupOf I) c.component.1
  let e := subgroupOfEquivOfLe c.component_le
  let R := Q.mapSurjective (f := e.toMonoidHom) e.surjective
  have hR : (R : Subgroup L) = S.subgroupOf L := by
    change (Q : Subgroup (L.subgroupOf I)).map e.toMonoidHom = _
    rw [hQ, ← hP]
    ext x
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a.val, ha, rfl⟩
    · rintro ⟨a, ha, he⟩
      refine ⟨⟨a, ?_⟩, ha, ?_⟩
      · change (a : G) ∈ L
        change (a : G) = (x : G) at he
        exact he.symm ▸ x.property
      · exact Subtype.ext he
  exact ⟨R, by rw [hR, subgroupOf_map_subtype]⟩

/-- This is the upstairs centralizer inequality in 15.3.43(c). -/
theorem centralizers_ne :
    S ⊓ centralizer (Yplus : Set G) ≠ S ⊓ centralizer (L : Set G) := by
  intro he
  have hle : V₁ ≤ S ⊓ centralizer (Yplus : Set G) :=
    le_inf c.plane_one_le (commutator_eq_bot_iff_le_centralizer.mp c.plane_one_centralizes)
  rw [he] at hle
  exact c.plane_one_acts (commutator_eq_bot_iff_le_centralizer.mpr
    (hle.trans inf_le_right))

/-- A trivial Sylow centralizer in the actual action quotient yields the
required upstairs equality. Only the forward image of a centralizer is
used; no unrestricted quotient-centralizer equality is asserted. -/
theorem centralizers_eq_of_quotient_centralizer
    (hq : c.toComponentAction.image S ⊓
      centralizer (c.toComponentAction.image Yplus : Set c.toComponentAction.Quotient) = ⊥) :
    S ⊓ centralizer (Yplus : Set G) = S ⊓ centralizer (L : Set G) := by
  apply le_antisymm
  · intro s hs
    have hSI : S ≤ I := (sylow_le_local c).trans inf_le_right
    let si : I := ⟨s, hSI hs.1⟩
    have hqS : c.toComponentAction.quotientMap si ∈ c.toComponentAction.image S :=
      mem_map.mpr ⟨si, hs.1, rfl⟩
    have hqC : c.toComponentAction.quotientMap si ∈
        centralizer (c.toComponentAction.image Yplus : Set c.toComponentAction.Quotient) := by
      rintro _ ⟨y, hy, rfl⟩
      rw [← map_mul, ← map_mul]
      exact congrArg c.toComponentAction.quotientMap (Subtype.ext (hs.2 y hy))
    have hzero : c.toComponentAction.quotientMap si = 1 := hq.le ⟨hqS, hqC⟩
    have hk : si ∈ c.toComponentAction.kernel := (QuotientGroup.eq_one_iff si).mp hzero
    exact ⟨hs.1, hk⟩
  · exact inf_le_inf_left S (centralizer_le c.y_le_component)

/-- The concrete centralizer bound recognizes `Y₊` itself as A₄. -/
theorem actor_alternating_four_of_plane_centralizer [Finite G]
    (hc : L ⊓ centralizer (V₂ : Set G) ≤ V₂) :
    Nonempty (Yplus ≃* alternatingGroup (Fin 4)) := by
  let : IsKleinFour V₂ := plane_isKleinFour c
  have hVY := plane_le_actor c
  let K := V₂.subgroupOf Yplus
  let : K.Normal := (normal_subgroupOf_iff_le_normalizer hVY).mpr
    ((actor_le_local c).trans c.plane_two_normalized)
  let e : K ≃* V₂ := subgroupOfEquivOfLe hVY
  let : IsKleinFour K :=
    ⟨(Nat.card_congr e.toEquiv).trans IsKleinFour.card_four,
      (Monoid.exponent_eq_of_mulEquiv e).trans IsKleinFour.exponent_two⟩
  have hK : centralizer (K : Set Yplus) = K := by
    apply le_antisymm
    · intro x hx
      apply hc
      refine ⟨c.y_le_component x.property, ?_⟩
      intro w hw
      exact congrArg Subtype.val (hx (⟨w, hVY hw⟩ : Yplus) hw)
    · intro x hx y hy
      exact congrArg Subtype.val
        ((IsKleinFour.isMulCommutative (G := K)).is_comm.comm ⟨y, hy⟩ ⟨x, hx⟩)
  exact RankTwo.RankOnePlane.alternating_four_of_pPerfect_selfCentralizing_kleinFour
    K hK (actor_isPPerfect c)

/-- A self-centralizing component plane contradicts 15.3.43(d). -/
theorem false_of_plane_centralizer [Finite G]
    (hc : L ⊓ centralizer (V₂ : Set G) ≤ V₂) : False :=
  c.not_alternating_four (actor_alternating_four_of_plane_centralizer c hc)

end CFSG.Quasithin.Chapter15.Section03.RankOne.EvenModels
