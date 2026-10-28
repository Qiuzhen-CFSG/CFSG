module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Quasisimple.MovedDegree
public import Theory.Mathieu.M24.LargeElementaryPerfectNormalizer

/-!
# Excluding M₂₄ for the remaining original binary degree three

The literal central image of the original perfect local component has
order divisible by 63. Its normalized elementary moved image has at least
64 elements by the binary degree bound. The native sextet/trio normalizer
comparison excludes this configuration. No irreducibility of the selected
full module or later generation bound is assumed.

Other.Source applies this to its surviving degree-three row.
Source: Aschbacher–Smith A.3.12 and 10.2.9, pp.47–48,750–751.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter10.PointControl.Quasisimple.Other
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  {t v : G} {I : Subgroup G} (c : EscapingComponent D t v I)
include D c

theorem not_mathieuTwentyFour_of_degree_three [Group.IsPerfect I]
    (hL : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^3))
    (eI : (I ⧸ center I) ≃* Sporadic.Mathieu.M24) : False := by
  obtain ⟨S,_,_,_,_,_,_,hE,hEB,hne,hm⟩ := center_quotient_data D c
  let q := QuotientGroup.mk' (center I)
  let B := ((L.subgroupOf I).map q).map eI.toMonoidHom
  let E := (((⁅D.fullModule,L⁆).subgroupOf I).map q).map eI.toMonoidHom
  let := Chapter1.mem_L_isPerfect D.maximal.1
  have heB : (L.subgroupOf I).map (eI.toMonoidHom.comp q) = B := (map_map _ _ _).symm
  let : Group.IsPerfect B := heB ▸ Group.IsPerfect.ofSurjective
    (markedLocalHom_surjective c.strict.le eI)
  let := hE
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map eI.toMonoidHom
  have hBN : B ≤ normalizer (E : Set Sporadic.Mathieu.M24) :=
    (map_mono (le_normalizer_iff_commutator_le_left.mpr hm.le)).trans
      (le_normalizer_map eI.toMonoidHom)
  have h64 := center_moved_card_of_binary_quotient D c (by decide : 0 < 3) hL
  have hc : 64 ≤ Nat.card E := by
    rw [card_map_of_injective eI.injective]
    exact h64
  obtain ⟨F,_,_,hF,⟨d⟩⟩ := hL
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  have h63 : 63 ∣ Nat.card (L ⧸ pCore 2 L) := by
    rw [Nat.card_congr (d.trans
      (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := F)).symm).toEquiv,
      GorensteinWalter.sl2_card_formula,hF]
    norm_num
  have he := Nat.card_congr (markedCoreQuotientEquiv D c.strict.le eI).toEquiv
  rw [heB] at he
  exact Sporadic.Mathieu.M24ChapterHStabilizers.ElementaryFusion.no_perfect_large_elementary_normalizer
    B E hBN hc ((he ▸ h63).trans (card_quotient_dvd_card (pCore 2 B)))
end CFSG.Quasithin.Chapter10.PointControl.Quasisimple.Other
