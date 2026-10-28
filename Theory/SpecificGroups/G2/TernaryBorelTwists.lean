module
public import Theory.SpecificGroups.G2.TernaryBorel
public import Theory.GroupTheory.Amalgam.SylowRigidity

/-!
# Restrictions on a faithful ternary Borel twist

The six-root Sylow subgroup is characteristic in the whole Borel. The
order-243 radicals of the two parabolics are normal under their respective
endpoint embeddings. A twist carrying the first radical onto the second
would therefore give a nontrivial common normal subgroup, contradicting
intrinsic amalgam faithfulness.

The original I.4.5 completion in MaximalMiddleAlignment supplies both that
faithfulness and its actual whole-middle discrepancy. These results exclude
the radical-exchanging case; they do not assert that every remaining twist
extends to the endpoints. Source: Aschbacher–Smith I.4.5, p.417, via F.4.26,
p.288. The root coordinates retain the ATLAS license in LICENSES/ATLAS.txt.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace Atlas.G2.TernaryBorel

/-- Each entire parabolic radical is contained in the standard Borel. -/
theorem radical_le_borel (side : Bool) : TernaryLevi.radical side≤B := by
  cases side
  · exact (LieParabolicSetup.fiveRootSubgroup_le_unipotent 5 (Or.inr rfl)).trans le_sup_left
  · exact (LieParabolicSetup.fiveRootSubgroup_le_unipotent 4 (Or.inl rfl)).trans le_sup_left

/-- The two marked order-243 radicals, as subgroups of the whole middle. -/
abbrev middleRadical (side : Bool) : Subgroup B := (TernaryLevi.radical side).subgroupOf B

theorem middleRadical_card (side : Bool) : Nat.card (middleRadical side)=243 := by
  rw [Nat.card_congr (subgroupOfEquivOfLe (radical_le_borel side)).toEquiv]
  cases side
  · rw [show TernaryLevi.radical false=LieParabolicSetup.radical₁ from rfl,
      LieParabolicSetup.card_radical₁]
    norm_num [Nat.card_eq_fintype_card]
  · rw [show TernaryLevi.radical true=LieParabolicSetup.radical₂ from rfl,
      LieParabolicSetup.card_radical₂]
    norm_num [Nat.card_eq_fintype_card]

theorem middleRadical_map (side : Bool) :
    (middleRadical side).map (inclusion (borel_le_endpoint side))=
      (TernaryLevi.radical side).subgroupOf (P side) := by
  ext x
  constructor
  · rintro ⟨y,hy,he⟩
    exact he ▸ hy
  · intro hx
    exact ⟨⟨(x:Model (ZMod 3)),radical_le_borel side hx⟩,hx,Subtype.ext rfl⟩

theorem middleRadical_map_normal (side : Bool) :
    ((middleRadical side).map (inclusion (borel_le_endpoint side))).Normal := by
  rw [middleRadical_map]
  exact normal_subgroupOf_of_le_normalizer (TernaryLevi.endpoint_normalizes side)

/-- A faithful twist cannot identify the first radical with the second.
Such an exchange would create a common nontrivial normal subgroup. -/
theorem faithful_twist_not_exchange (δ : MulAut B)
    (hf : RankTwoAmalgam.Faithful (RankTwoAmalgam.twistRight
      (RankTwoAmalgam.ofSubgroups (P false) B (P true)
        (borel_le_endpoint false) (borel_le_endpoint true)) δ)) :
    (middleRadical false).map δ.toMonoidHom≠middleRadical true := by
  intro he
  have hn : ((middleRadical false).map
      ((inclusion (borel_le_endpoint true)).comp δ.toMonoidHom)).Normal := by
    rw [←map_map,he]
    exact middleRadical_map_normal true
  have hb := hf (middleRadical false) (middleRadical_map_normal false) hn
  have hh := middleRadical_card false
  rw [hb,card_bot] at hh
  omega

/-- The normal Sylow three-subgroup is characteristic in the whole Borel. -/
theorem unipotent_subgroupOf_characteristic : (U.subgroupOf B).Characteristic := by
  let S := sylow.subtype (show U≤B from le_sup_left)
  apply S.characteristic_of_normal
  exact normal_subgroupOf_of_le_normalizer borel_normalizes

/-- Every possible middle discrepancy preserves the whole six-root subgroup. -/
theorem automorphism_unipotent (δ : MulAut B) :
    (U.subgroupOf B).map δ.toMonoidHom=U.subgroupOf B := by
  let := unipotent_subgroupOf_characteristic
  exact characteristic_iff_map_eq.mp inferInstance δ

end Atlas.G2.TernaryBorel
