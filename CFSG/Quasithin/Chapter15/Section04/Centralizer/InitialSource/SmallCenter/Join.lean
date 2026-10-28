module
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.InitialSource.SmallCenter.NaturalModels

/-!
# The original maximal local is the family member's minimal parabolic

When the central omega subgroup has order two, the natural action has
one or two binary planes. Comparing its dimension with the actual member's
moved rank identifies the full core quotient order as 6^s s!. The original
member contributes the full odd part, of order 3^s. Its join with the given
Sylow subgroup therefore has index both odd and a power of two, hence one.
The already proved original-family minimal-parabolic theorem now applies
to this same maximal local, without selecting a different overgroup.

Source: Aschbacher--Smith 15.4.7, printed p.1158, and C.1.26.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section04.InitialSource.SmallCenter
open FamilySource FamilySource.ModuleStructure ChapterA.Section05To06
universe u
variable {G : Type u} [Group G] [Finite G]

theorem core_quotient_card {T : Sylow 2 G} {M X : Subgroup G} {s : ℕ}
    (h : Input KnownSimple.IsKnownSimple T M X s)
    (hZ : Nat.card (omegaOneCenterAmbient (T : Subgroup G)) = 2) :
    Nat.card (CoreQuotient M) = 6^s * s.factorial := by
  let U := internalModule T M
  let := internalModule_elementary T M h.sylow_le
    (h.ambient.evenCharacteristic T M h.maximal h.sylow_le)
  have hU : IsPReduced 2 U := ⟨inferInstance,inferInstance,
    internalModule_reduced T M h.sylow_le h.center_centralizer⟩
  have hJ : ¬ elementaryAbelianMaxJ
      ((T.subtype h.sylow_le : Sylow 2 M) : Subgroup M) ≤ centralizer (U : Set M) := by
    intro hh
    apply h.thompson_moved
    have hm := map_mono (f := M.subtype) hh
    rw [←elementaryAbelianMaxJ_map_injective M.subtype M.subtype_injective,
      Sylow.coe_subtype,map_subgroupOf_eq_of_le h.sylow_le,map_centralizer_subtype] at hm
    exact commutator_eq_bot_iff_le_centralizer.mpr
      (le_centralizer_iff.mp (hm.trans inf_le_right))
  obtain ⟨d,_,_,_,_,hd,hcard⟩ :=
    Section03.InitialSource.solvable_small_action_of_central_order_two h.ambient T
      ⟨h.maximal,h.sylow_le⟩ hZ h.solvable U hU hJ
  have hu : Nat.card U = 2^(2*s) := by
    rw [←card_map_of_injective (f := M.subtype) M.subtype_injective]
    change Nat.card (localV T M) = _
    rw [←member_moved_eq h hZ]
    exact h.moved_card
  have hu' : Nat.card U = 2^(2*d.count) := by
    change Nat.card (Additive U) = _
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,hd]
  have hn : d.count = s := by
    have he := Nat.pow_right_injective (by decide : 1 < 2) (hu.symm.trans hu')
    omega
  let a : CoreQuotient M ≃* (M ⧸ centralizer (U : Set M)) :=
    QuotientGroup.quotientMulEquivOfEq (internal_centralizer T M h.sylow_le h.center_centralizer).symm
  rw [Nat.card_congr a.toEquiv,hcard,hn]

private theorem contains_sylow_and_full_odd_part {A : Type*} [Group A] [Finite A]
    (S : Sylow 2 A) (R K : Subgroup A) (hRK : R ≤ K) (hSK : (S : Subgroup A) ≤ K)
    (n : ℕ) (hc : Nat.card A = Nat.card R * 2^n) : K = ⊤ := by
  have hm : Nat.card R * K.index ∣ Nat.card R * 2^n := by
    rw [←hc,←K.card_mul_index]
    exact Nat.mul_dvd_mul_right (card_dvd_of_le hRK) K.index
  have hi : K.index ∣ 2^n := Nat.dvd_of_mul_dvd_mul_left (Nat.card_pos (α := R)) hm
  have hp : Nat.Coprime (2^n) (S : Subgroup A).index :=
    (Nat.prime_two.coprime_iff_not_dvd.mpr S.not_dvd_index).pow_left n
  exact index_eq_one.mp (Nat.eq_one_of_dvd_coprimes hp hi (index_dvd_of_le hSK))

/-- Every actual family member in a small-center maximal local, together
with the original Sylow subgroup, generates that same local. -/
theorem member_join_eq {T : Sylow 2 G} {M X : Subgroup G} {s : ℕ}
    (h : Input KnownSimple.IsKnownSimple T M X s)
    (hZ : Nat.card (omegaOneCenterAmbient (T : Subgroup G)) = 2) :
    X ⊔ (T : Subgroup G) = M := by
  let S := T.subtype h.sylow_le
  let q := quotientMap M
  let K := (X ⊔ (T : Subgroup G)).subgroupOf M
  have hKM : X ⊔ (T : Subgroup G) ≤ M := sup_le h.member_le h.sylow_le
  have hSK : (S : Subgroup M) ≤ K := by
    change (T : Subgroup G).subgroupOf M ≤ (X ⊔ (T : Subgroup G)).subgroupOf M
    exact subgroupOf_mono M le_sup_right
  obtain ⟨e,_⟩ := member_quotient_compatible h.member_le h.normal
  have hR : Nat.card (image M X) = 3^s :=
    (Nat.card_congr e.toEquiv).symm.trans h.quotient_card
  have hRK : image M X ≤ K.map q := map_mono (subgroupOf_mono M le_sup_left)
  have hbar : K.map q = ⊤ := by
    have hc := core_quotient_card h hZ
    rcases h.parameter with hs | hs
    · apply contains_sylow_and_full_odd_part (S.mapSurjective (QuotientGroup.mk'_surjective _))
        (image M X) (K.map q) hRK (map_mono hSK) 1
      rw [hc,hR,hs]
      decide
    · apply contains_sylow_and_full_odd_part (S.mapSurjective (QuotientGroup.mk'_surjective _))
        (image M X) (K.map q) hRK (map_mono hSK) 3
      rw [hc,hR,hs]
      decide
  have hk : q.ker ≤ K := by
    change (QuotientGroup.mk' (pCore 2 M)).ker ≤ K
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup.le_sylow_of_normal S |>.trans hSK
  have he := congrArg (Subgroup.comap q) hbar
  rw [comap_map_eq_self hk,comap_top] at he
  have hm := congrArg (Subgroup.map M.subtype) he
  rwa [map_subgroupOf_eq_of_le hKM,←MonoidHom.range_eq_map,range_subtype] at hm

/-- Thus the same selected original maximal local is itself the genuine
minimal parabolic to which the fixed-pair source argument is applied. -/
theorem member_minimal_parabolic {T : Sylow 2 G} {M X : Subgroup G} {s : ℕ}
    (h : Input KnownSimple.IsKnownSimple T M X s)
    (hZ : Nat.card (omegaOneCenterAmbient (T : Subgroup G)) = 2) :
    ChapterB.IsMinimalParabolicOver (T.subtype h.sylow_le) ⊤ := by
  have he := member_join_eq h hZ
  subst M
  exact member_internal_minimalParabolic T h.member h.quotient_elementary

end CFSG.Quasithin.Chapter15.Section04.InitialSource.SmallCenter
