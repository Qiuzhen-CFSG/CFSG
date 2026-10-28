module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.MathieuRadiusThree.ActionKernels
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.SourceCuts

/-!
# Source obligations for the radius-three branch

The first obligation is the literal six-point action and six-arc label
calculation (6.12.2)--(6.12.5). The second constructs the two endpoint
isomorphisms from these relations by identifying the generated local groups
in (6.12.6) and the final paragraphs. The second argument can be developed
with the first calculation explicit. Neither obligation asserts compatible
amalgam recognition; that assembly uses the already proved M₁₂ twist rigidity.

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980),
(6.12), pp.403--406. The labeled vertex corresponds to the involution
centralizer, the first endpoint of the GreenBook model.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt.MathieuRadiusThree
open Subgroup SimpleGraph Theory.GroupAction.CubicTree
open Subgroup.CosetGeometry
open scoped commutatorElement
universe u
variable {G : Type u} [Group G] {F : Bool → Subgroup G} {s : ℕ}

/-- The local conclusions needed to identify the generated endpoint groups.
The commutator uses the actual labels on every six-edge path. -/
structure LocalRelations (h : LargeTreeSource F s) (d : CanonicalLabelSetup F s) : Prop where
  action_image : ∀ (a : RankTwo.Vertex F), a.type = d.side →
    ∀ f : BranchFrame F a,
      Nonempty ((f.blockAction h.action.toCubicTreeAction).range ≃* Equiv.Perm (Fin 4))
  labelBall_card : ∀ (a : RankTwo.Vertex F), a.type = d.side →
    Nat.card (d.labelBall a 2) = 8
  six_arc : ∀ (a b : RankTwo.Vertex F) (p : (RankTwo.graph F).Walk a b),
    a.type = d.side → p.IsPath → p.length = 6 →
      ⁅d.label a, d.label b⁆ = d.label (p.getVert 2) * d.label (p.getVert 4)

/-- Actual endpoint carriers, with orientation determined by the canonical label.
No overlap isomorphism or compatibility is assumed. -/
def EndpointTypes (d : CanonicalLabelSetup F s) : Prop :=
  Nonempty ((F d.side) ≃* GreenBook.MathieuTwelve.P 0) ∧
    Nonempty ((F (!d.side)) ≃* GreenBook.MathieuTwelve.P 1)

def LocalRelationsInput : Prop :=
  ∀ (G : Type u) [Group G] (F : Bool → Subgroup G) (s : ℕ)
    (h : LargeTreeSource F s) (d : CanonicalLabelSetup F s),
    d.radius = 3 → LocalRelations h d

def LocalGroupsInput : Prop :=
  ∀ (G : Type u) [Group G] (F : Bool → Subgroup G) (s : ℕ)
    (h : LargeTreeSource F s) (d : CanonicalLabelSetup F s),
    d.radius = 3 → LocalRelations h d → EndpointTypes d

/-- The first source obligation identifies the genuine ball-kernel quotient,
using the proved action-kernel equality rather than an abstract action tag. -/
noncomputable def LocalRelations.radiusTwoQuotientEquiv
    {h : LargeTreeSource F s} {d : CanonicalLabelSetup F s}
    (r : LocalRelations h d) {a : RankTwo.Vertex F} (ha : a.type = d.side)
    (f : BranchFrame F a) :
    (RankTwo.stabilizer F a ⧸
      (RankTwo.ballKernel F a 2).subgroupOf (RankTwo.stabilizer F a)) ≃*
        Equiv.Perm (Fin 4) :=
  (f.radiusTwoQuotientEquiv h.action.toCubicTreeAction).trans
    (Classical.choice (r.action_image a ha f))

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt.MathieuRadiusThree
