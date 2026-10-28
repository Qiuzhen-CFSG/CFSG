module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.NaturalTerminal.AlphaEntrance
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.NaturalTerminal.Source

/-!
# The original odd Cartan-axis test with its module premises discharged

The original natural marking and Hall containment give a trivial paired
coordinate kernel and place the Thompson alpha subgroup in the module.
The odd fixed-vector calculation therefore puts any subgroup of the
original Hall with a nontrivial alpha fixed point on one coordinate axis.
The paired coordinate maps remain the literal orbit action maps.
Source: Aschbacher–Smith 10.2.3(4), printed pp.746–747.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter10.MovingHall
open Chapter3.Section02 ChapterB
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  {F : Type} [Field F] [Finite F] [CharP F 2]
local instance : Algebra (ZMod 2) F := ZMod.algebra F 2

variable {E : Type*} [Field E] [CharP E 2]
local instance : Algebra (ZMod 2) E := ZMod.algebra E 2

/-- The original Cartan-axis test with coordinate faithfulness and alpha placement discharged. -/
theorem Context.original_odd_axis_of_natural_marking
    {H : Subgroup G} {B : Subgroup H} (ctx : Context D H B)
    (degree : ℕ) (hdegree : 1 < degree) (hF : Nat.card F = 2 ^ degree)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F)) (mark : NaturalMarking D e)
    (hBR : B.map H.subtype ≤ localOrbit T L)
    (q₁ q₂ : localOrbit T L →* SL(2,E))
    (c : BinaryConjugationSection (localOrbit T L) D.moduleSubgroup
      (D.moduleSubgroup ⊓ centralizer (localOrbit T L : Set G))
      (Representation.prod (SL2.BinarySmall.natural.comp q₁) (SL2.BinarySmall.natural.comp q₂)))
    (P : Subgroup G) (hPB : P ≤ B.map H.subtype)
    (hfixed : thompsonAlpha (T : Subgroup G) ⊓ centralizer (P : Set G) ≠ ⊥) :
    P ≤ q₁.ker.map (localOrbit T L).subtype ∨ P ≤ q₂.ker.map (localOrbit T L).subtype := by
  exact source_original_odd_axis_of_alpha_fixed D ctx (localOrbit T L) P le_rfl q₁ q₂
    c.coordinates (ctx.original_coordinates_injective D degree hdegree hF e mark hBR c)
    (fun p v => c.equivariant p v)
    ((ctx.original_alpha_le_moved D degree hdegree hF e mark hBR).trans
      (le_normalizer_iff_commutator_le_left.mp D.orbit_normalizes_module))
    (hPB.trans hBR) hPB hfixed
end CFSG.Quasithin.Chapter10.MovingHall
