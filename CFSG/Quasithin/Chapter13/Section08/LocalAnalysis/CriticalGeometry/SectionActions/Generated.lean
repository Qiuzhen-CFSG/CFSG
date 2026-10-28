module
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.SectionActions.Basic
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.QuotientActions

/-!
# The common center on the generated endpoint section

Normality is restricted to the vertex group J. The noncentral commutator
bound then identifies the order-two displacement in V/U as ZU/U, and proves
that every actor is a transvection with a nonidentity actor among them.
Equality of star images is connected to equality in the literal quotient by
the ambient bound and its converse on quotient images.

Source: Aschbacher–Smith 13.8.9 and 13.8.11, combined manuscript
(1 March 2004), printed pp.949–950.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.CriticalGeometry.SectionActions
variable {G : Type*} [Group G] [Finite G]

theorem line_of_relative_noncentral (J F V U Z : Subgroup G)
    (hFJ : F ≤ J) (hVJ : V ≤ J) (hZJ : Z ≤ J) (hUV : U ≤ V)
    (hJV : J ≤ normalizer (V : Set G)) (hJU : J ≤ normalizer (U : Set G))
    (hZ : Nat.card Z = 2) (hb : ⁅F, V⁆ ≤ U ⊔ Z) (hn : ¬ ⁅F, V⁆ ≤ U) :
    Z ≤ V ∧ ¬ Z ≤ U ∧ U ⊔ ⁅F, V⁆ = U ⊔ Z := by
  let _ : (V.subgroupOf J).Normal := normal_subgroupOf_of_le_normalizer hJV
  let _ : (U.subgroupOf J).Normal := normal_subgroupOf_of_le_normalizer hJU
  have hUJ := hUV.trans hVJ
  have hZ' : Nat.card (Z.subgroupOf J) = 2 := by
    rwa [Nat.card_congr (subgroupOfEquivOfLe hZJ).toEquiv]
  have hb' : ⁅F.subgroupOf J, V.subgroupOf J⁆ ≤ U.subgroupOf J ⊔ Z.subgroupOf J := by
    apply (map_le_map_iff_of_injective J.subtype_injective).mp
    rwa [map_commutator, Subgroup.map_sup, map_subgroupOf_eq_of_le hFJ,
      map_subgroupOf_eq_of_le hVJ, map_subgroupOf_eq_of_le hUJ, map_subgroupOf_eq_of_le hZJ]
  have hn' : ¬ ⁅F.subgroupOf J, V.subgroupOf J⁆ ≤ U.subgroupOf J := by
    intro hh
    apply hn
    have hm := map_mono (f := J.subtype) hh
    rwa [map_commutator, map_subgroupOf_eq_of_le hFJ,
      map_subgroupOf_eq_of_le hVJ, map_subgroupOf_eq_of_le hUJ] at hm
  obtain ⟨h1, h2, h3⟩ := line_le_of_noncentral_commutator (F.subgroupOf J)
    (V.subgroupOf J) (U.subgroupOf J) (Z.subgroupOf J) (subgroupOf_mono J hUV) hZ' hb' hn'
  refine ⟨?_, fun h => h2 (subgroupOf_mono J h), ?_⟩
  · have hh := map_mono (f := J.subtype) h1
    simpa only [map_subgroupOf_eq_of_le hZJ, map_subgroupOf_eq_of_le hVJ] using hh
  · have hh := congrArg (Subgroup.map J.subtype) h3
    simpa only [Subgroup.map_sup, map_commutator, map_subgroupOf_eq_of_le hFJ,
      map_subgroupOf_eq_of_le hVJ, map_subgroupOf_eq_of_le hUJ, map_subgroupOf_eq_of_le hZJ] using hh

omit [Finite G] in
/-- The ambient bound is also sufficient for equality in the literal quotient. -/
theorem quotientCommutator_eq_of_bound (F P R U Z : Subgroup G)
    [(Z.subgroupOf U).Normal] (hPR : P ≤ R) (hFU : F ≤ U) (hZU : Z ≤ U)
    (hRF : R ≤ normalizer (F : Set G)) (hb : ⁅F, R⁆ ≤ ⁅F, P⁆ ⊔ Z) :
    quotientCommutator F P U Z = quotientCommutator F R U Z := by
  apply le_antisymm (map_mono (subgroupOf_mono U (commutator_mono le_rfl hPR)))
  have hFP : ⁅F, P⁆ ≤ U :=
    (le_normalizer_iff_commutator_le_left.mp (hPR.trans hRF)).trans hFU
  have hh := map_mono (f := QuotientGroup.mk' (Z.subgroupOf U)) (subgroupOf_mono U hb)
  rw [subgroupOf_sup hFP hZU, Subgroup.map_sup] at hh
  have hzero : (Z.subgroupOf U).map (QuotientGroup.mk' (Z.subgroupOf U)) = ⊥ :=
    (Subgroup.map_eq_bot_iff _).mpr (by rw [QuotientGroup.ker_mk'])
  simpa only [hzero, sup_bot_eq] using hh

/-- An order-two common center for the specified, literal quotient action. -/
def HasTransvectionCenter (P V U Z : Subgroup G) [IsElementaryAbelian 2 V]
    (hn : P ≤ normalizer (V : Set G)) (hu : P ≤ normalizer (U : Set G)) : Prop :=
  Z ≤ V ∧ ¬ Z ≤ U ∧
  commutatorAction (quotientAction P V U hn hu).range (V ⧸ U.subgroupOf V) =
    (Z.subgroupOf V).map (QuotientGroup.mk' (U.subgroupOf V)) ∧
  Nat.card (commutatorAction (quotientAction P V U hn hu).range (V ⧸ U.subgroupOf V)) = 2 ∧
  ∀ p : P, binaryLinear (quotientAction P V U hn hu p) ∈
    LinearEquiv.transvections (ZMod 2) (Additive (V ⧸ U.subgroupOf V))

theorem center_of_bound (J F V U Z : Subgroup G) [IsElementaryAbelian 2 V]
    (hFJ : F ≤ J) (hVJ : V ≤ J) (hZJ : Z ≤ J) (hUV : U ≤ V)
    (hJV : J ≤ normalizer (V : Set G)) (hJU : J ≤ normalizer (U : Set G))
    (hZ : Nat.card Z = 2) (hb : ⁅F, V⁆ ≤ ⁅F, U⁆ ⊔ Z) (hn : ¬ ⁅F, V⁆ ≤ U) :
    HasTransvectionCenter F V U Z (hFJ.trans hJV) (hFJ.trans hJU) := by
  have hFV : ⁅F, V⁆ ≤ V := le_normalizer_iff_commutator_le_right.mp (hFJ.trans hJV)
  have hFU : ⁅F, U⁆ ≤ U := le_normalizer_iff_commutator_le_right.mp (hFJ.trans hJU)
  obtain ⟨hZV, hZU, hs⟩ := line_of_relative_noncentral J F V U Z hFJ hVJ hZJ hUV
    hJV hJU hZ (hb.trans (sup_le_sup_right hFU Z)) hn
  let q := QuotientGroup.mk' (U.subgroupOf V)
  have heq : (⁅F, V⁆.subgroupOf V).map q = (Z.subgroupOf V).map q := by
    have hh := congrArg (fun A : Subgroup G => (A.subgroupOf V).map q) hs
    rw [subgroupOf_sup hUV hFV, subgroupOf_sup hUV hZV,
      Subgroup.map_sup, Subgroup.map_sup] at hh
    simpa only [(Subgroup.map_eq_bot_iff (U.subgroupOf V) (f := q)).mpr (by simp [q]),
      bot_sup_eq] using hh
  have hc : Nat.card ((Z.subgroupOf V).map q) = 2 := by
    have hdiv : Nat.card ((Z.subgroupOf V).map q) ∣ 2 := by
      have hh := (Z.subgroupOf V).card_map_dvd q
      rwa [Nat.card_congr (subgroupOfEquivOfLe hZV).toEquiv, hZ] at hh
    refine ((Nat.dvd_prime Nat.prime_two).mp hdiv).resolve_left ?_
    intro hone
    have hh := (Subgroup.map_eq_bot_iff _).mp (card_eq_one.mp hone)
    apply hZU
    intro z hz
    have hzker := hh (show (⟨z, hZV hz⟩ : V) ∈ Z.subgroupOf V from hz)
    simpa only [q, QuotientGroup.ker_mk', mem_subgroupOf] using hzker
  have hd := (quotientAction_displacement F V U (hFJ.trans hJV) (hFJ.trans hJU)).trans heq
  have hcard : Nat.card (commutatorAction
      (quotientAction F V U (hFJ.trans hJV) (hFJ.trans hJU)).range
      (V ⧸ U.subgroupOf V)) = 2 := by rwa [hd]
  exact ⟨hZV, hZU, hd, hcard, fun p => transvections_of_displacement_card_two _ hcard _ ⟨p, rfl⟩⟩

omit [Finite G] in
theorem exists_nonidentity_of_center (P V U Z : Subgroup G) [IsElementaryAbelian 2 V]
    (hn : P ≤ normalizer (V : Set G)) (hu : P ≤ normalizer (U : Set G))
    (hc : HasTransvectionCenter P V U Z hn hu) :
    ∃ p : P, quotientAction P V U hn hu p ≠ 1 ∧
      binaryLinear (quotientAction P V U hn hu p) ∈
        LinearEquiv.transvections (ZMod 2) (Additive (V ⧸ U.subgroupOf V)) := by
  classical
  by_contra hh
  have htriv : ∀ p, quotientAction P V U hn hu p = 1 := by
    intro p
    by_contra hntr
    exact hh ⟨p, hntr, hc.2.2.2.2 p⟩
  have hb := (quotientAction_all_eq_one_iff P V U hn hu).mp htriv
  have hd : commutatorAction (quotientAction P V U hn hu).range (V ⧸ U.subgroupOf V) = ⊥ := by
    rw [quotientAction_displacement]
    apply (Subgroup.map_eq_bot_iff _).mpr
    simpa only [QuotientGroup.ker_mk'] using subgroupOf_mono V hb
  have hcard := hc.2.2.2.1
  rw [hd] at hcard
  have hone : Nat.card (⊥ : Subgroup (V ⧸ U.subgroupOf V)) = 1 := Nat.card_unique
  omega

end CFSG.Quasithin.Chapter13.Section08.CriticalGeometry.SectionActions

end
