module
public import Theory.Representation.SL3.AdjointCubicCentralizer.GraphExtension.FrattiniDescent
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockEndgameLinearSourceExtension
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockEndgameLinearAdjoint

/-!
# The original nonblock Frattini action under a graph crossing

Apply graph-extension recognition to the literal component and its cubic
extension in the original root normalizer. The ordinary adjoint action and
the source PGL quotient square retain the given full marking. At the same
group-marked diagonal cubic, FixedLevi supplies at least 256 fixed elements.

The full Frattini marking, graph component and corrected action-kernel descent
are explicit earlier-source witnesses. The group-generator marker is the
same premise used by NonblockEndgameLinearAdjoint, and is not an ordinary
PGL-module marking. The source owner constructs these witnesses and compares
the lower bound with the original fixed-section upper bound. The generic
Frattini adapter does not require strict secondary-core enlargement.

Source: Aschbacher–Smith B.4.14, printed p.98, and the terminal argument
for original 4.3.2, pp.618–619. This is a conditional representation consequence,
not a construction of the earlier-source witnesses from MSData.
-/

open Matrix Representation Subgroup
open scoped MatrixGroups
open Matrix.PSL3.OuterSolvable Matrix.PSL3.ExtensionBorel
open Representation.SL3.AdjointCubicCentralizer
open Representation.SL3.AdjointCubicCentralizer.GraphExtension
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.SourceEndgame
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]
  {T : Sylow 2 G} {L : Subgroup G} {c : SourceConfiguration T L}
attribute [local instance] ZMod.algebra SecondarySourceData.normal

/-- The representation witnesses for the literal original component and its
cubic extension. No ordinary PGL module marking occurs in this input. -/
abbrev SourceFrattiniGraphData (s : SecondarySourceData c 2) (X : Subgroup G) :=
  FrattiniDescent.FrattiniGraphData (F := F) s.component (cubicExtension s X) le_sup_left

def sourceCubicInclusion (s : SecondarySourceData c 2) (X : Subgroup G)
    (hXr : X ≤ rootNormalizer c) : X →* cubicExtension s X where
  toFun x := ⟨⟨x,hXr x.property⟩,
    (le_sup_right : X.subgroupOf (rootNormalizer c) ≤ cubicExtension s X)
      (show (⟨x,hXr x.property⟩ : rootNormalizer c) ∈
        X.subgroupOf (rootNormalizer c) from x.property)⟩
  map_one' := rfl
  map_mul' _ _ := rfl

omit [Finite G] in
/-- Recognition preserves the whole original module coordinates and the
original source quotient square. This theorem only uses the explicit earlier
source witnesses; it does not construct them from MSData. -/
theorem source_full_frattini_adjoint (s : SecondarySourceData c 2) (X : Subgroup G)
    (d : SourceFrattiniGraphData (F := F) s X) (hF : Nat.card F = 4) :
    d.representation = restrictScalars (k := ZMod 2) (projectiveAdjoint F) ∧
      ∀ (g : cubicExtension s X) (z : s.component ⧸ pCore 2 s.component),
        d.componentMarking (s.action g z) =
          (pglEquivInnerDiagonal F (d.projection g)).val (d.componentMarking z) := by
  exact ⟨d.ordinary hF,cubic_extension_action s d.componentMarking X d.projection d.componentSquare⟩

omit [Finite G] in
/-- The marked generator acts ordinarily on the same full Frattini quotient;
the input marks its group image, not its module action. -/
theorem source_frattini_generator_action (s : SecondarySourceData c 2)
    (X : Subgroup G) (hXr : X ≤ rootNormalizer c)
    (d : SourceFrattiniGraphData (F := F) s X) (hF : Nat.card F = 4)
    (x : X) (ω : Fˣ)
    (hdiag : d.projection (sourceCubicInclusion s X hXr x) =
      ProjGenLinGroup.mk (diagonalUnit F ω)) (v : FrattiniDescent.Frattini s.component) :
    (d.coordinates (FrattiniDescent.coreAction s.component
      (⟨x,hXr x.property⟩ : rootNormalizer c) v)).toAdd =
      projectiveAdjoint F (ProjGenLinGroup.mk (diagonalUnit F ω)) (d.coordinates v).toAdd := by
  exact (d.ordinary_action hF (sourceCubicInclusion s X hXr x) v).trans (by rw [hdiag])

/-- The original cubic fixes at least 256 elements of the whole component-core
Frattini quotient. The source owner compares this with its original section
bound and constructs the full marking and corrected crossing witnesses. -/
theorem source_frattini_fixed_card_ge (s : SecondarySourceData c 2)
    (X : Subgroup G) (hX : Nat.card X = 3) (hXr : X ≤ rootNormalizer c)
    (d : SourceFrattiniGraphData (F := F) s X) (hF : Nat.card F = 4)
    (x : X) (hx : x ≠ 1) (ω : Fˣ)
    (hdiag : d.projection (sourceCubicInclusion s X hXr x) =
      ProjGenLinGroup.mk (diagonalUnit F ω)) :
    letI : MulDistribMulAction X (FrattiniDescent.Frattini s.component) :=
      MulDistribMulAction.compHom _ ((FrattiniDescent.coreAction s.component).comp
        ((cubicExtension s X).subtype.comp (sourceCubicInclusion s X hXr)))
    256 ≤ Nat.card (FixedPoints.subgroup X (FrattiniDescent.Frattini s.component)) := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  exact d.fixed_card_ge hF (sourceCubicInclusion s X hXr) x
    (zpowers_eq_top_of_prime_card hX hx) ω hdiag

end
end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.SourceEndgame
