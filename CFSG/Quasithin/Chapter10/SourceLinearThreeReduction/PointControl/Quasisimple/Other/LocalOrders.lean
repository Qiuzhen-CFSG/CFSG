module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Quasisimple.MovedDegree
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.TwoLocalOrder
public import Theory.SpecificGroups.Held.TwoLocalCandidates.OrderObstruction

/-!
# Held and Rudvalis point carriers for the original rank-one quotient

The literal moved image is nonzero and elementary, and both the original
local image and the full restricted Sylow normalize it. The native local
order bounds therefore apply to its ambient normalizer. Central passage
preserves the original two-core quotient, whose order divides that of this
normalizer. Its factors nine and 63 exclude Rudvalis and Held for PSL₂(8).

This keeps fixed vectors and every module row. Other.Source combines the
comparison with the earlier degree sieve to discharge both remaining
rank-one sporadic rows. Source: Aschbacher–Smith 10.2.9, pp.750–751,
using A.3.12, pp.47–48, and GLS3 Tables 5.3p,r.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.PointControl.Quasisimple.Other
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  {t v : G} {I : Subgroup G} (c : EscapingComponent D t v I)
include D c

/-- Apply a native two-local order obstruction to the actual local quotient. -/
theorem quotient_not_dvd_of_twoLocal_orders [Group.IsPerfect I]
    {H : Type*} [Group H] [Finite H] (e : (I ⧸ center I) ≃* H) {k : ℕ}
    (horders : ∀ (S : Sylow 2 H) (N : Subgroup H), IsTwoLocal N →
      (S : Subgroup H) ≤ N → ¬ k ∣ Nat.card N) : ¬ k ∣ Nat.card (L ⧸ pCore 2 L) := by
  obtain ⟨S,_,_,_,hSN,_,_,hE,hEB,hne,hm⟩ := center_quotient_data D c
  let q := QuotientGroup.mk' (center I)
  let B := (L.subgroupOf I).map q
  let E := ((⁅D.fullModule,L⁆).subgroupOf I).map q
  let A := B.map e.toMonoidHom
  let U := E.map e.toMonoidHom
  let R := S.mapSurjective (QuotientGroup.mk'_surjective (center I))
  let P := R.mapSurjective (f := e.toMonoidHom) e.surjective
  let := hE
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.map e.toMonoidHom
  have hU : U ≠ ⊥ := fun h => hne ((map_eq_bot_iff_of_injective _ e.injective).mp h)
  have hPN : (P : Subgroup H) ≤ normalizer (U : Set H) :=
    (map_mono hSN).trans (le_normalizer_map e.toMonoidHom)
  have hAN : A ≤ normalizer (U : Set H) :=
    (map_mono (le_normalizer_iff_commutator_le_left.mpr hm.le)).trans
      (le_normalizer_map e.toMonoidHom)
  have hc := Nat.card_congr (markedCoreQuotientEquiv D c.strict.le e).toEquiv
  have heA : (L.subgroupOf I).map (e.toMonoidHom.comp q) = A := (map_map _ _ _).symm
  rw [heA] at hc
  intro hd
  exact horders P _ ⟨U,hU,IsElementaryAbelian.isPGroup 2 U,rfl⟩ hPN
    ((hc ▸ hd).trans ((card_quotient_dvd_card (pCore 2 A)).trans (card_dvd_of_le hAN)))

/-- The Rudvalis local obstruction on the original two-core quotient. -/
theorem not_rudvalis_of_nine [Group.IsPerfect I]
    (h9 : 9 ∣ Nat.card (L ⧸ pCore 2 L))
    (e : (I ⧸ center I) ≃* Rudvalis.Model) : False :=
  quotient_not_dvd_of_twoLocal_orders D c e Rudvalis.SylowOvergroups.not_nine_dvd_card_twoLocal h9

/-- The Held local obstruction on the original two-core quotient. -/
theorem not_held_of_sixtythree [Group.IsPerfect I]
    (h63 : 63 ∣ Nat.card (L ⧸ pCore 2 L))
    (e : (I ⧸ center I) ≃* Held.He) : False :=
  quotient_not_dvd_of_twoLocal_orders D c e Held.TwoLocalCandidates.not_sixtythree_dvd_card_twoLocal h63

omit D c in
private theorem degree_three_sixtythree {H : Type*} [Group H]
    (h : ClassicalGroup.IsPSL H 2 (2^3)) : 63 ∣ Nat.card H := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := h
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  let d := e.trans (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := F)).symm
  rw [Nat.card_congr d.toEquiv,GorensteinWalter.sl2_card_formula,hF]
  norm_num

theorem not_rudvalis_of_degree_three [Group.IsPerfect I]
    (hL : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^3))
    (e : (I ⧸ center I) ≃* Rudvalis.Model) : False :=
  not_rudvalis_of_nine D c ((by decide : 9 ∣ 63).trans (degree_three_sixtythree hL)) e

theorem not_held_of_degree_three [Group.IsPerfect I]
    (hL : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^3))
    (e : (I ⧸ center I) ≃* Held.He) : False :=
  not_held_of_sixtythree D c (degree_three_sixtythree hL) e
end CFSG.Quasithin.Chapter10.PointControl.Quasisimple.Other
