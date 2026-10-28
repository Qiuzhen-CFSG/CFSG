module
public import Theory.Representation.AlternatingSixPairedCovers.QuadraticComponent
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.ElementaryOuter
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.Transport
/-!
# Whole quadratic actor bounds for paired A₆ covers

Conjugation embeds the ambient actor in Aut(A₆), since the marked component
is self-centralizing. An elementary subgroup has at most two inner cosets.
Simultaneous quadraticity on the original two covers bounds its component
intersection by order two, so the whole actor has order at most four.
Every elementary subgroup of rank greater than one meets the component in
an actual involution. These statements allow the actor to exchange the covers.

Source: Aschbacher–Smith, original 14.6.24(2), printed p.1041. The rank-one
movement exclusion and the construction of the source markings remain
separate obligations; the source application is AlternatingSix.QuadraticActors.
-/

public section
open Representation Representation.BinaryOffender Subgroup
namespace AlternatingSixPairedCovers.Data
variable {H E : Type*} [Group H] [AddCommGroup E] [Module (ZMod 2) E]
  {ρ : Representation (ZMod 2) H E} (C : Data ρ)

/-- The actual elementary actor has at most two cosets modulo its intersection
with the embedded component. -/
theorem elementary_card_le_twice_component (B : Subgroup H) [IsElementaryAbelian 2 B] :
    Nat.card B ≤ 2 * Nat.card (B.comap C.component) := by
  let K := C.component.range
  let : K.Normal := C.normal
  let e : K ≃* alternatingGroup (Fin 6) := (MonoidHom.ofInjective C.injective).symm
  let f := AlternatingSix.ShadowLocal.conjugationAction K e
  let : IsElementaryAbelian 2 (B.map f) := IsElementaryAbelian.map f
  have hpre : AlternatingSix.ShadowLocal.inner.comap f = K := by
    rw [AlternatingSix.ShadowLocal.conjugationAction_preimage_inner,C.centralizer,sup_bot_eq]
  have hi : K.relIndex B ≤ 2 := by
    rw [←hpre,relIndex_comap]
    exact AlternatingSix.ShadowLocal.elementary_inner_relIndex (B.map f)
  have hk : Nat.card (K.subgroupOf B) = Nat.card (B.comap C.component) := by
    calc
      _ = Nat.card ((K.subgroupOf B).map B.subtype) :=
        (card_map_of_injective B.subtype_injective).symm
      _ = Nat.card (B ⊓ K : Subgroup H) := by rw [subgroupOf_map_subtype,inf_comm]
      _ = Nat.card ((B.comap C.component).map C.component) := by rw [map_comap_eq,inf_comm]
      _ = _ := card_map_of_injective C.injective
  have hm := (K.subgroupOf B).card_mul_index
  change Nat.card (K.subgroupOf B) * K.relIndex B = Nat.card B at hm
  rw [hk] at hm
  nlinarith

include C in
/-- Simultaneous quadraticity on the two original covers bounds the whole
actor by order four, including actors which interchange the covers. -/
theorem quadratic_card_le_four (B : Subgroup H) [IsElementaryAbelian 2 B]
    (hq : IsQuadratic ρ B) : Nat.card B ≤ 4 := by
  have hi := C.elementary_card_le_twice_component B
  have hc := C.quadratic_component_card B hq
  omega

include C in
/-- Rank form of the whole-actor bound. -/
theorem quadratic_rank_le_two (B : Subgroup H) [IsElementaryAbelian 2 B]
    (hq : IsQuadratic ρ B) : rank B ≤ 2 := by
  exact (Nat.log_monotone (b := 2) (C.quadratic_card_le_four B hq)).trans (by decide)

/-- Every elementary actor of rank greater than one contains an involution
of the same embedded component. -/
theorem component_involution_of_rank_gt_one
    (B : Subgroup H) [IsElementaryAbelian 2 B] (hr : 1 < rank B) :
    ∃ t : alternatingGroup (Fin 6), orderOf t = 2 ∧ C.component t ∈ B := by
  have hd : B.comap C.component ≠ ⊥ := by
    intro hz
    have hi := C.elementary_card_le_twice_component B
    rw [hz,Subgroup.card_bot,mul_one] at hi
    have hh := Nat.log_monotone (b := 2) hi
    change rank B ≤ 1 at hh
    omega
  have hex : ∃ t ∈ B.comap C.component, t ≠ 1 := by
    by_contra! hn
    apply hd
    exact le_antisymm (fun t ht => mem_bot.mpr (hn t ht)) bot_le
  obtain ⟨t,ht,hn⟩ := hex
  let : IsElementaryAbelian 2 (B.comap C.component) :=
    IsElementaryAbelian.comap_of_injective C.component C.injective B
  exact ⟨t,orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian t ht) hn,ht⟩
end AlternatingSixPairedCovers.Data
