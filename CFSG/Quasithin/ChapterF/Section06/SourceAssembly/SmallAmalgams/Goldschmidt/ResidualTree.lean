module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.Residual
public import Theory.GroupAction.RankTwoCosetGeometry.NormalRestriction

/-!
# The tree for the actual two-perfect residual

The normal-subgroup restriction in Goldschmidt (3.2) uses the actual ambient
two-residual and the original edge stabilizer as its supplement. The literal
inclusion on coset representatives identifies its graph with the original tree;
the right-coset convention and the residual action are preserved.

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980), (3.2),
printed pp.386--387.
-/

@[expose] public section
open Subgroup Theory.GroupTheory Subgroup.CosetGeometry
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
variable {G : Type*} [Group G] {F : Bool → Subgroup G}

/-- The graph of the actual two-residual is the original coset tree. -/
noncomputable def CubicTreeAction.residual_graphIso (h : CubicTreeAction F) :
    RankTwo.graph (fun i => (F i).subgroupOf (pResidual 2 G)) ≃g RankTwo.graph F :=
  RankTwo.NormalRestriction.graphIso F (pResidual 2 G) h.residual_source.2.2

/-- Inclusion on the source right cosets is the literal vertex map. -/
@[simp] theorem CubicTreeAction.residual_graphIso_rightVertex (h : CubicTreeAction F)
    (i : Bool) (n : pResidual 2 G) :
    h.residual_graphIso (RankTwo.rightVertex
      (fun i => (F i).subgroupOf (pResidual 2 G)) i n) =
      RankTwo.rightVertex F i (n : G) :=
  RankTwo.NormalRestriction.vertex_rightVertex F (pResidual 2 G) i n

/-- The residual still acts on the same tree, with its intersected local groups. -/
theorem CubicTreeAction.residual_tree (h : CubicTreeAction F) :
    (RankTwo.graph (fun i => (F i).subgroupOf (pResidual 2 G))).IsTree :=
  h.residual_graphIso.isTree_iff.mpr h.tree

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
