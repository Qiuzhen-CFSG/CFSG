module
public import Theory.SpecificGroups.Triality.BinaryLocalSections
public import Theory.SpecificGroups.Triality.StandardTwoRank.Sylow.RadicalBounds.Arms
public import Theory.Representation.SL2.MovedElementaryDegree

/-!
# No fully moved elementary local subgroup in binary triality

The actual Sylow alignment places a proper perfect local subgroup in the
arms parabolic and identifies its two-core quotient with SL₂(8). A nonzero
fully moved elementary subgroup therefore has at least 64 elements by
chief-factor degree. The equation on quotient representatives puts that
same elementary subgroup inside the arms radical, where the nondegenerate
commutator pairing bounds its order by 32. This excludes the configuration
without perfectness of the whole arms factor or a source module marking.

Source: Aschbacher–Smith A.3.12 and 10.2.9, pp.47–48,750–751; the actual
triality radical calculation uses GLS3 §§2.4–2.6. The consumer is the
binary triality branch of the non-A₅ point-component inspection.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace Triality.Standard.BinaryLocalSections
open Parabolics
variable {G : Type*} [Group G] [Finite G]

/-- A full-Sylow normalized proper perfect subgroup cannot contain a nonzero
fully moved elementary binary subgroup in the genuine binary triality carrier. -/
theorem no_moved_elementary
    (eG : G ≃* BinaryCarrier 1 Nat.zero_lt_one) (S : Sylow 2 G)
    (B E : Subgroup G) [Group.IsPerfect B] [IsElementaryAbelian 2 E]
    (hne : B ≠ ⊤) (hns : ¬ Group.IsSolvable B)
    (hn : (S : Subgroup G) ≤ normalizer (B : Set G))
    (hEB : E ≤ B) (hE : E ≠ ⊥) (hm : ⁅E,B⁆ = E) : False := by
  obtain ⟨a,_,hBL,e,he⟩ := marked_arm_quotient eG S B hne hns hn
  let P := binaryParameters 1 Nat.zero_lt_one
  let A := localFactor P .arms
  let d := e.trans ((localFactorArmsQuotientEquivPSL2 P rfl).trans
    (Theory.PSL2.sl2QuotientEquiv (ExtensionField P)).symm)
  let : CharP (ExtensionField P) 2 := inferInstance
  have hcard : Nat.card (ExtensionField P) = 2 ^ 3 := by
    rw [card_extensionField]
    rfl
  have hl := Representation.SL2.moved_subgroup_card_bound B E hEB hE hm d
    (by decide : 3 ≠ 0) hcard
  let U := E.subgroupOf B
  let : U.Normal := normal_subgroupOf_of_le_normalizer
    (le_normalizer_iff_commutator_le_left.mpr hm.le)
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf hEB
  have hU : U ≤ pCore 2 B := le_sSup ⟨inferInstance,IsElementaryAbelian.isPGroup 2 U⟩
  let E' := E.map a.toMonoidHom
  let : IsElementaryAbelian 2 E' := IsElementaryAbelian.map a.toMonoidHom
  have hER : E' ≤ radical P .arms := by
    rintro _ ⟨x,hx,rfl⟩
    let b : B := ⟨x,hEB hx⟩
    have hb : b ∈ pCore 2 B := hU hx
    have hbq : QuotientGroup.mk' (pCore 2 B) b = 1 :=
      (QuotientGroup.eq_one_iff b).mpr hb
    have ht := he b
    rw [hbq,map_one] at ht
    have hc : inclusion hBL (a.subgroupMap B b) ∈ pCore 2 A :=
      (QuotientGroup.eq_one_iff _).mp ht.symm
    rw [←localFactor_twoCore_map P rfl .arms]
    exact ⟨inclusion hBL (a.subgroupMap B b),hc,rfl⟩
  let : IsElementaryAbelian 2 (E'.subgroupOf (radical P .arms)) :=
    IsElementaryAbelian.subgroupOf hER
  have hu := TwoRank.RadicalBounds.arms_radical_card_le P rfl
    (E'.subgroupOf (radical P .arms))
  rw [Nat.card_congr (subgroupOfEquivOfLe hER).toEquiv,
    card_map_of_injective a.injective] at hu
  norm_num [P,Parameters.q,binaryParameters] at hu hl
  omega
end Triality.Standard.BinaryLocalSections
