module
public import CFSG.Quasithin.ChapterC.Section01.LocalCoreAction
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Baumann.AlternatingFive.NaturalAction.FixedKernel

/-!
# Displacement bounds for a local alternating-five component

A local C-component is subnormal in its join with the prescribed full Sylow.
That join contains the ambient two-core. Subnormal two-perfect action therefore
puts its full core commutator in the block's literal U-layer. For an A5 block,
fixed-kernel vanishing identifies U with the deleted permutation module of
order 16. Thus every cyclic actor in the block moves at most 16 core elements.

The final criterion excludes such a local component when every order-five
actor moves more than 16 elements of a normal binary subgroup. Its literal
consumer is the second J4 involution centralizer in Aschbacher–Smith 2.4.25, printed p.543.
The full Sylow and local-component guards are retained throughout.
-/

public section
namespace CFSG.Quasithin.ChapterC
open Subgroup
variable {G : Type*} [Group G] [Finite G]

theorem local_short_core_commutator_le_blockU (S : Sylow 2 G) (B : Subgroup G)
    (hb : IsShort B) (hl : B ∈ ChapterA.Section03.localCComponents S) :
    ⁅pCore 2 G, B⁆ ≤ (blockU B).map B.subtype := by
  let H := B ⊔ (S : Subgroup G)
  let B' := B.subgroupOf H
  have hBH : B ≤ H := le_sup_left
  let eB : B' ≃* B := subgroupOfEquivOfLe hBH
  have hp' : IsPPerfect 2 B' := hb.twoPerfect.of_surjective eB.symm.toMonoidHom eB.symm.surjective
  have heB : (blockU B').map eB.toMonoidHom = blockU B := by
    rw [blockU, map_commutator, pCore_map_iso,
      map_top_of_surjective _ eB.surjective, blockU]
  have hs : B'.IsSubnormal := hl.subnormal
  have hQH : pCore 2 G ≤ H := (pCore_isPGroup.le_sylow_of_normal S).trans le_sup_right
  let Q := (pCore 2 G).subgroupOf H
  have hc : ⁅Q, B'⁆ ≤ (blockU B').map B'.subtype :=
    commutator_le_core_commutator_of_isSubnormal B' Q hs hp'
      pCore_isPGroup.comap_subtype le_normalizer_of_normal
  have he : (⁅Q, B'⁆).map H.subtype = ⁅pCore 2 G, B⁆ := by
    rw [map_commutator, map_subgroupOf_eq_of_le hQH,
      map_subgroupOf_eq_of_le hBH]
  rw [← he]
  intro x hx
  obtain ⟨y, hy, rfl⟩ := hx
  obtain ⟨u, hu, he⟩ := hc hy
  refine ⟨eB u, heB ▸ mem_map_of_mem eB.toMonoidHom hu, ?_⟩
  exact congrArg H.subtype he

omit [Finite G] in
theorem IsAlternatingBlock.blockU_card (hA : IsAlternatingBlock G 5) :
    Nat.card (blockU G) = 16 := by
  have hb : Function.Bijective (QuotientGroup.mk' (blockFixed G)) :=
    ⟨(MonoidHom.ker_eq_bot_iff _).mp (by rw [QuotientGroup.ker_mk', hA.blockFixed_eq_bot]),
      QuotientGroup.mk'_surjective _⟩
  let e := MulEquiv.ofBijective (QuotientGroup.mk' (blockFixed G)) hb
  calc
    Nat.card (blockU G) = Nat.card (BlockModule G) := Nat.card_congr e.toEquiv
    _ = 16 := by simpa using hA.module_card_odd (by decide : Odd 5)

theorem local_alternating_five_core_commutator_card_le (S : Sylow 2 G)
    (A : Subgroup G) (hA : IsAlternatingBlock A 5)
    (hl : A ∈ ChapterA.Section03.localCComponents S)
    (E : Subgroup G) (hE : E ≤ pCore 2 G) (x : G) (hx : x ∈ A) :
    Nat.card (⁅E, zpowers x⁆ : Subgroup G) ≤ 16 := by
  have hle : ⁅E, zpowers x⁆ ≤ (blockU A).map A.subtype :=
    (commutator_mono hE (zpowers_le.mpr hx)).trans
      (local_short_core_commutator_le_blockU S A hA.2.1 hl)
  have hc := Nat.card_le_card_of_injective (inclusion hle) (inclusion_injective hle)
  rw [card_map_of_injective A.subtype_injective, hA.blockU_card] at hc
  exact hc

theorem not_local_alternating_five_of_five_displacement
    (E : Subgroup G) (hE : E ≤ pCore 2 G)
    (hfive : ∀ x : G, orderOf x = 5 → 16 < Nat.card (⁅E, zpowers x⁆ : Subgroup G))
    (S : Sylow 2 G) (A : Subgroup G) (hA : IsAlternatingBlock A 5) :
    A ∉ ChapterA.Section03.localCComponents S := by
  intro hl
  obtain ⟨e⟩ := hA.2.2.quotient_iso
  have hq : Nat.card (A ⧸ pCore 2 A) = 60 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
    decide
  have hd : 5 ∣ Nat.card A := (show 5 ∣ Nat.card (A ⧸ pCore 2 A) by rw [hq]; decide).trans
    (pCore 2 A).card_quotient_dvd_card
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := A) 5 hd
  have hxG : orderOf (x : G) = 5 := (Subgroup.orderOf_coe x).trans hx
  exact (not_lt_of_ge (local_alternating_five_core_commutator_card_le
    S A hA hl E hE x x.property)) (hfive x hxG)
end CFSG.Quasithin.ChapterC
