module
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.MathieuRadiusThree.LocalGroupsOppositeRaw

/-!
# Recognition of the literal opposite source endpoint

The three-arm quotient has order six and kernel the radius-three group of
order 32. Source labels and a cubic branch actor supply the marked extension
relations, which identify the generated group with the concrete second M₁₂
parabolic. The radius-four order premise is supplied by the independent
labelled-endpoint quotient calculation.

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980), the last
paragraph of (6.12), printed p.406.
-/

public section
noncomputable section
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt.MathieuRadiusThree
open Subgroup.CosetGeometry
open Sporadic.Mathieu.M12SmallPair
open Sporadic.Mathieu.M12SmallPair.ExceptionalParabolics
open Sporadic.Mathieu.M12SmallPair.ExceptionalParabolics.SourceRecognition
variable {G : Type*} [Group G] {F : Bool → Subgroup G} {s : ℕ}

/-- The literal source opposite group is the second M₁₂ parabolic. -/
theorem LocalRelations.oppositeGroup_equiv_secondParabolic
    {h : LargeTreeSource F s} {d : CanonicalLabelSetup F s}
    (r : LocalRelations h d) (hr : d.radius = 3)
    (v : RankTwo.Vertex F) (hv : v.type ≠ d.side)
    (hcards : ∀ a, (RankTwo.graph F).Adj v a → Nat.card (d.labelBall a 4) = 192) :
    Nonempty (oppositeGroup d v ≃* secondParabolic) := by
  have hc := r.oppositeGroup_card_of_radiusFour_card hr v hv hcards
  let : Finite (oppositeGroup d v) := Nat.finite_of_card_ne_zero (by rw [hc]; decide)
  obtain ⟨x,y,z,a,b,T,C,hraw,hgen⟩ := r.oppositeGroup_raw_generators hr v hv hcards
  exact secondParabolic_equiv_of_raw_coreExtension_relations x y z a b T C hraw hgen
    (by rw [hc])

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt.MathieuRadiusThree
