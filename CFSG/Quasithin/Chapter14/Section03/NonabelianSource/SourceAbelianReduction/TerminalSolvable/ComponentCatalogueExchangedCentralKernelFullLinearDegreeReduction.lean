module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueExchangedCentralKernelFullLinear
public import Theory.SpecificGroups.BinaryLinear.ElementaryOuterSylowReduction

/-!
# The source consumer of the graph Sylow degree calculation

The actual full-linear equivalence transports the outer Sylow action to a
coordinate space of exactly the selected constituent's dimension. Arbitrary-degree
automorphism coverage is proved in the lower layer. The only extra premise
below is the graph-coset Sylow displacement calculation; after it is proved,
`fullLinear_degree_of_graphSylowDegreeBound` supplies the literal `hbound` in
`not_fullLinear_of_outer_bound_and_four`.

The independent original-source degree-four exclusion remains with the full-GL
assembly owner. These conditional declarations do not establish G.10.15(3).
Source: Aschbacher--Smith G.10.15(3), printed p.363.
-/

public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open scoped IsMulCommutative
namespace ExchangedCentralSource
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {M Mc : Subgroup G}
  {F : InvariantFlag T (rankTwoSeed T M) 2}
  [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
  {g : G} [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
  {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
  {L : Subgroup F.TerminalHdot} {I : Submodule (ZMod 2) (Additive F.Uhat)}
  (s : ExchangedCentralSource T M Mc F g B v L I)

include s

/-- The exact degree-bound adapter, conditional only on the remaining matrix
calculation. The group equivalence and outer action are the caller's actual ones. -/
theorem fullLinear_degree_of_graphSylowDegreeBound
    (hgraph : BinaryLinear.ElementaryOuterSylow.GraphSylowDegreeBound)
    (a : ElementaryOuterSylowAction (componentOrbit L ⊤))
    (e : (componentOrbit L ⊤) ≃* LinearMap.GeneralLinearGroup (ZMod 2) I) :
    finrank (ZMod 2) I = 4 :=
  BinaryLinear.ElementaryOuterSylow.finrank_eq_four_of_graphSylowDegreeBound
    hgraph a e (by have := s.dimension_gt_two; omega)

/-- Application to the unchanged full-linear exclusion: the matrix calculation
supplies `hbound`, while the independent degree-four branch remains explicit. -/
theorem not_fullLinear_of_graphSylowDegreeBound_and_four
    (hgraph : BinaryLinear.ElementaryOuterSylow.GraphSylowDegreeBound)
    (hfour : finrank (ZMod 2) I = 4 → ¬ Function.Surjective
      (invariantSubspace F.terminalRepresentation (componentOrbit L ⊤) I
        s.selected.invariant).toRepresentation.asGroupHom) :
    ¬ Function.Surjective (invariantSubspace F.terminalRepresentation (componentOrbit L ⊤) I
      s.selected.invariant).toRepresentation.asGroupHom :=
  s.not_fullLinear_of_outer_bound_and_four
    (s.fullLinear_degree_of_graphSylowDegreeBound hgraph) hfour

end ExchangedCentralSource
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
