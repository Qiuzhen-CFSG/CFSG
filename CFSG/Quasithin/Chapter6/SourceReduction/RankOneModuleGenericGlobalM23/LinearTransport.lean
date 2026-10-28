module
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.LinearThreeFour.Recognition
public import Theory.SpecificGroups.PSL3.LinearThreeFieldTransport.Diagram
public import Theory.GroupTheory.Amalgam.LocalStructure
public import Theory.GroupTheory.Amalgam.GeneratedCompletion.Overlap

/-!
# The full four-field marking and exact dihedral order

Transport an arbitrary field of order four to the native field by an actual
field equivalence. Restrict its entrywise projective map to both parabolics
and the entire Borel, so both amalgam squares commute. The completion in the
literal join retains both source endpoint ranges and the whole intersection,
including in the reversed orientation.

For endpoint involutions outside that intersection, the already proved
short-geodesic bound forces every positive dihedral exponent at most three
to equal three. This discharges the difference between the source's bound
and the exact-order-three premise of the existing F.4.26 specialization.

Source: Aschbacher–Smith 5.2.16, printed p.655, and F.3.6/F.4.26,
printed pp.272,288 (`refs/quasithin.pdf`). The original source hypotheses
supply the involutions in `LinearCompletion.lean`.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.M23Completion
open CFSG.Quasithin.ChapterF.SourceCompletion.LinearThreeFour
open Subgroup.CosetGeometry Subgroup.CosetGeometry.RankTwo

/-- The source upper bound on the dihedral product gives exact order three. -/
theorem endpoint_product_order {G : Type*} [Group G] [Finite G] (c : Completion G)
    (s t : G) (hs : s ∈ c.left.range) (ht : t ∈ c.right.range)
    (hsout : s ∉ c.middle.range) (htout : t ∉ c.middle.range)
    (hs2 : orderOf s = 2) (ht2 : orderOf t = 2) (hst : orderOf (s*t) ≤ 3) :
    orderOf (s*t) = 3 := by
  have hsx : s • RankTwo.base c.family false = RankTwo.base c.family false := by
    change s ∈ stabilizer c.family (RankTwo.base c.family false)
    simpa only [stabilizer,RankTwo.base,stabilizer_base,Completion.family_false] using hs
  have htl : t • RankTwo.base c.family true = RankTwo.base c.family true := by
    change t ∈ stabilizer c.family (RankTwo.base c.family true)
    simpa only [stabilizer,RankTwo.base,stabilizer_base,Completion.family_true] using ht
  have hsl : s • RankTwo.base c.family true ≠ RankTwo.base c.family true := by
    intro hh
    have hh' : s ∈ c.right.range := by
      change s ∈ stabilizer c.family (RankTwo.base c.family true) at hh
      simpa only [stabilizer,RankTwo.base,stabilizer_base,Completion.family_true] using hh
    exact hsout (c.overlap ▸ show s ∈ c.left.range ⊓ c.right.range from ⟨hs,hh'⟩)
  have htx : t • RankTwo.base c.family false ≠ RankTwo.base c.family false := by
    intro hh
    have hh' : t ∈ c.left.range := by
      change t ∈ stabilizer c.family (RankTwo.base c.family false) at hh
      simpa only [stabilizer,RankTwo.base,stabilizer_base,Completion.family_false] using hh
    exact htout (c.overlap ▸ show t ∈ c.left.range ⊓ c.right.range from ⟨hh',ht⟩)
  exact GroupAction.DihedralPolygon.edge_exponent_eq c.bipartiteAction
    c.uniqueGeodesicsBelow_three (orderOf_pos (s*t)) hst
    ⟨Bool.false_ne_true,incident_base c.family false true⟩
    (hs2 ▸ pow_orderOf_eq_one s) (ht2 ▸ pow_orderOf_eq_one t) hsx hsl htl htx
    (by rw [pow_orderOf_eq_one,one_smul]) (by rw [pow_orderOf_eq_one,one_smul])

open Matrix.PSL3.LinearThree
open CFSG.Quasithin.ChapterF.GreenBook.LieModels
/-- Coefficient transport uses one ambient map on both endpoints and the full Borel. -/
def fieldIso {E F : Type*} [Field E] [Finite E] [Field F] [Finite F]
    (a : E ≃+* F) : RankTwoAmalgam.Iso (LinearThree.amalgam E) (LinearThree.amalgam F) :=
  RankTwoAmalgam.ofSubgroupsIso (Atlas.fieldEquivPSL 3 a)
    (LinearThree.borel_le_point E) (LinearThree.borel_le_line E)
    (LinearThree.borel_le_point F) (LinearThree.borel_le_line F)
    (FieldTransport.field_map_pointParabolic a) (FieldTransport.field_map_borel a)
    (FieldTransport.field_map_lineParabolic a)


/-- The literal generated subgroup carries the native amalgam, with the
whole intersection preserved in either orientation. -/
theorem native_completion {G : Type*} [Group G] (P Q : Subgroup G)
    (E : Type*) [Field E] [Finite E] (hE : Nat.card E = 4)
    (he : Nonempty (RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups P (P ⊓ Q) Q inf_le_left inf_le_right)
      (LinearThree.amalgam E)) ∨ Nonempty (RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups P (P ⊓ Q) Q inf_le_left inf_le_right)
      (LinearThree.amalgam E).reverse)) :
    ∃ c : Completion (P ⊔ Q : Subgroup G),
      ((c.left.range = P.subgroupOf (P ⊔ Q) ∧ c.right.range = Q.subgroupOf (P ⊔ Q)) ∨
       (c.left.range = Q.subgroupOf (P ⊔ Q) ∧ c.right.range = P.subgroupOf (P ⊔ Q))) ∧
      c.middle.range = (P ⊓ Q).subgroupOf (P ⊔ Q) := by
  let := Fintype.ofFinite E
  let := Fintype.ofFinite Matrix.PSL3Four.F
  let a : E ≃+* Matrix.PSL3Four.F := FiniteField.ringEquivOfCardEq (by
    simpa only [← Nat.card_eq_fintype_card,Matrix.PSL3Four.card_F] using hE)
  let c₀ := RankTwoAmalgam.FaithfulCompletion.ofGeneratedSubgroups P (P ⊓ Q) Q
    inf_le_left inf_le_right
  rcases he with he | he <;> obtain ⟨e⟩ := he
  · let c := (c₀.comapIso e.symm).comapIso (fieldIso a).symm
    refine ⟨c,Or.inl ⟨?_,?_⟩,?_⟩ <;>
      simp only [c,c₀,RankTwoAmalgam.FaithfulCompletion.comapIso_left_range,
        RankTwoAmalgam.FaithfulCompletion.comapIso_right_range,
        RankTwoAmalgam.FaithfulCompletion.comapIso_middle_range,
        RankTwoAmalgam.FaithfulCompletion.ofGeneratedSubgroups_left_range,
        RankTwoAmalgam.FaithfulCompletion.ofGeneratedSubgroups_right_range,
        RankTwoAmalgam.FaithfulCompletion.ofGeneratedSubgroups_middle_range]
  · let c₁ : RankTwoAmalgam.FaithfulCompletion (LinearThree.amalgam E)
        (G := (P ⊔ Q : Subgroup G)) := (c₀.comapIso e.symm).reverse
    let c := c₁.comapIso (fieldIso a).symm
    refine ⟨c,Or.inr ⟨?_,?_⟩,?_⟩
    · exact (RankTwoAmalgam.FaithfulCompletion.comapIso_left_range c₁ (fieldIso a).symm).trans
        ((RankTwoAmalgam.FaithfulCompletion.comapIso_right_range c₀ e.symm).trans
          (RankTwoAmalgam.FaithfulCompletion.ofGeneratedSubgroups_right_range _ _ _ _ _))
    · exact (RankTwoAmalgam.FaithfulCompletion.comapIso_right_range c₁ (fieldIso a).symm).trans
        ((RankTwoAmalgam.FaithfulCompletion.comapIso_left_range c₀ e.symm).trans
          (RankTwoAmalgam.FaithfulCompletion.ofGeneratedSubgroups_left_range _ _ _ _ _))
    · exact (RankTwoAmalgam.FaithfulCompletion.comapIso_middle_range c₁ (fieldIso a).symm).trans
        ((congrArg MonoidHom.range (RankTwoAmalgam.FaithfulCompletion.reverse_middle
          (c₀.comapIso e.symm))).trans
          ((RankTwoAmalgam.FaithfulCompletion.comapIso_middle_range c₀ e.symm).trans
            (RankTwoAmalgam.FaithfulCompletion.ofGeneratedSubgroups_middle_range _ _ _ _ _)))
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.M23Completion
