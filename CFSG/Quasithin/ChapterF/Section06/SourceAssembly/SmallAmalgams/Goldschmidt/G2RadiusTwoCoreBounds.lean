module
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.G2RadiusTwoLocalAction
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.SourceCuts

/-!
# The nonabelian first core in the original radius-two source action

The literal order-sixteen distance-two label subgroup is normal in every
intermediate subgroup of its vertex stabilizer. In particular it lies in
the two-core of the first generated source group and of the original
vertex stabilizer. This supplies noncommutativity and the lower bound
sixteen for these actual two-cores. The original S₃ local quotient then
forces the first vertex stabilizer to have order at least ninety-six.

Source: Goldschmidt (1980), (6.9), printed p.401.
-/

public section
open Subgroup SimpleGraph
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
open Subgroup.CosetGeometry
variable {G : Type*} [Group G] {F : Bool → Subgroup G} {s : ℕ}

private theorem first_core_le {c : CanonicalLabelSetup F s} (hr : c.radius = 2)
    (hs : 4 ≤ s) (h : CubicTreeAction F) {a : RankTwo.Vertex F}
    (ha : a.type = c.side) {H : Subgroup G}
    (hQH : c.sphereLabelGroup a 2 ≤ H) (hHa : H ≤ RankTwo.stabilizer F a) :
    (c.sphereLabelGroup a 2).subgroupOf H ≤ pCore 2 H := by
  have hn : ((c.sphereLabelGroup a 2).subgroupOf H).Normal :=
    (normal_subgroupOf_iff_le_normalizer hQH).mpr
      (hHa.trans (c.stabilizer_le_normalizer_sphereLabelGroup a 2))
  have hp : IsPGroup 2 ((c.sphereLabelGroup a 2).subgroupOf H) :=
    (IsPGroup.of_card (n := 4) (c.radiusTwo_sphere_two_card hr hs h a ha)).of_equiv
      (subgroupOfEquivOfLe hQH).symm
  exact le_sSup ⟨hn, hp⟩

private theorem first_core_bounds {c : CanonicalLabelSetup F s} (hr : c.radius = 2)
    (hs : 4 ≤ s) (h : CubicTreeAction F) {a : RankTwo.Vertex F}
    (ha : a.type = c.side) {H : Subgroup G}
    (hQH : c.sphereLabelGroup a 2 ≤ H) (hHa : H ≤ RankTwo.stabilizer F a) :
    16 ≤ Nat.card (pCore 2 H) ∧ ¬ IsMulCommutative (pCore 2 H) := by
  let : Finite (RankTwo.stabilizer F a) := h.finite_stabilizer a
  let : Finite H := Finite.of_injective (Subgroup.inclusion hHa) (Subgroup.inclusion_injective _)
  let Q := (c.sphereLabelGroup a 2).subgroupOf H
  have hQP : Q ≤ pCore 2 H := first_core_le hr hs h ha hQH hHa
  let e := subgroupOfEquivOfLe hQH
  have hQcard : Nat.card Q = 16 :=
    (Nat.card_congr e.toEquiv).trans (c.radiusTwo_sphere_two_card hr hs h a ha)
  refine ⟨?_, ?_⟩
  · rw [← hQcard]
    exact Nat.card_le_card_of_injective (Subgroup.inclusion hQP) (Subgroup.inclusion_injective _)
  · intro hp
    have hQcomm : IsMulCommutative Q := isMulCommutative_iff.mpr fun x y => by
      apply (Subgroup.inclusion_injective hQP)
      exact isMulCommutative_iff.mp hp (Subgroup.inclusion hQP x) (Subgroup.inclusion hQP y)
    apply (c.radiusTwo_sphere_two_structure hr hs h a ha).2
    apply isMulCommutative_iff.mpr
    intro x y
    apply e.symm.injective
    simpa only [map_mul] using isMulCommutative_iff.mp hQcomm (e.symm x) (e.symm y)

/-- The radius-two first source group has a nonabelian two-core of order
at least sixteen, witnessed by its actual distance-two label subgroup. -/
theorem CanonicalLabelSetup.radiusTwo_first_twoCore_structure
    (c : CanonicalLabelSetup F s) (hr : c.radius = 2) (hs : 4 ≤ s)
    (h : CubicTreeAction F) {a β : RankTwo.Vertex F}
    (ha : a.type = c.side) (haβ : (RankTwo.graph F).Adj a β) :
    16 ≤ Nat.card (pCore 2 (c.radiusTwoFirstGroup a β)) ∧
      ¬ IsMulCommutative (pCore 2 (c.radiusTwoFirstGroup a β)) :=
  first_core_bounds hr hs h ha
    (c.radiusTwo_sphere_two_le_first hr (by omega) h haβ)
    (c.radiusTwo_first_le_stabilizer a β)

/-- The same literal subgroup supplies the first original vertex two-core. -/
theorem CanonicalLabelSetup.radiusTwo_stabilizer_twoCore_structure
    (c : CanonicalLabelSetup F s) (hr : c.radius = 2) (hs : 4 ≤ s)
    (h : CubicTreeAction F) {a : RankTwo.Vertex F} (ha : a.type = c.side) :
    16 ≤ Nat.card (pCore 2 (RankTwo.stabilizer F a)) ∧
      ¬ IsMulCommutative (pCore 2 (RankTwo.stabilizer F a)) :=
  first_core_bounds hr hs h ha
    (c.sphereLabelGroup_le_stabilizer a 2 (by omega) (by omega)) le_rfl

/-- Application to the original large source: the first labelled stabilizer
has order at least ninety-six. The two-core and the S₃ quotient are both
constructed from the original action. -/
theorem LargeTreeSource.radiusTwo_stabilizer_card_ge
    (h : LargeTreeSource F s) (c : CanonicalLabelSetup F s) (hr : c.radius = 2)
    {a : RankTwo.Vertex F} (ha : a.type = c.side) :
    96 ≤ Nat.card (RankTwo.stabilizer F a) := by
  have hQ := (c.radiusTwo_stabilizer_twoCore_structure hr (by have := h.five_le; omega)
    h.action.toCubicTreeAction ha).1
  obtain ⟨e⟩ := h.action.toCubicTreeAction.stabilizer_quotient_symmetricThree_of_large_residual
    h.not_cubic h.not_alternating a
  rw [SymmetricThreeTwoCore.card_eq e]
  omega

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
