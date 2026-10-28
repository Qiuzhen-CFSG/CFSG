module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Quasisimple.Preparation
public import Theory.SpecificGroups.Triality.BinaryMovedElementary

/-!
# Excluding the genuine binary triality point carrier

The original local and moved subgroups descend through the containing
center. The complete restricted Sylow normalizes the proper perfect local
image. The actual binary triality placement then identifies its quotient
with SL₂(8), forcing a moved elementary subgroup of order at least 64
inside a radical whose elementary subgroups have order at most 32.

This applies to every original quotient and module row, including the
four-natural binary-three row. RankTwo.Source consumes the contradiction.
Source: Aschbacher–Smith A.3.12 and 10.2.9, pp.47–48,750–751.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter10.PointControl.Quasisimple.RankTwo
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  {t v : G} {I : Subgroup G} (c : EscapingComponent D t v I)
include D c

theorem not_binary_triality [Group.IsPerfect I]
    (eI : (I ⧸ center I) ≃* Triality.Standard.BinaryCarrier 1 Nat.zero_lt_one) : False := by
  obtain ⟨S,_,hB,hSN,_,hproper,_,hE,hEB,hne,hm⟩ := center_quotient_data D c
  let q := QuotientGroup.mk' (center I)
  let B := (L.subgroupOf I).map q
  let E := ((⁅D.fullModule,L⁆).subgroupOf I).map q
  let R := S.mapSurjective (QuotientGroup.mk'_surjective (center I))
  let := hB.perfect
  let d := subgroupOfEquivOfLe (show B ≤ B ⊔ (R : Subgroup _) from le_sup_left)
  let : Group.IsPerfect B := Group.IsPerfect.ofSurjective (f := d.toMonoidHom) d.surjective
  let : IsElementaryAbelian 2 E := hE
  have hns : ¬ Group.IsSolvable B := by
    intro hs
    let := hs
    exact hB.not_isSolvable (Group.isSolvable_of_isSolvable_injective
      (f := d.toMonoidHom) d.injective)
  exact Triality.Standard.BinaryLocalSections.no_moved_elementary eI R B E
    hproper hns hSN hEB hne hm
end CFSG.Quasithin.Chapter10.PointControl.Quasisimple.RankTwo
