module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Existence.FittingCenter.Action
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Existence.FittingCenter.Commutator
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Existence.FittingCenter.Marking
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Existence.FittingCenter.Generation

/-!
# The Fitting-center equality after 13.6.13

The genuine Thompson image has a faithful offender-generated binary action
with an SQTK cover, so the complete universal B.5.6 input classifies it.
The actual T_v image supplies the Sylow and normalization markings.

The candidate X = [F(J(G_v)*), J(G_v)*] is normal and solvable,
and has its literal two-residual equal to itself. Every FF alternative,
including the double-S₃ case with its actual Sylow marking, gives
[X,J(T_v)*] = X. Thus noncentrality would put X in the literal X-family,
contradicting 13.6.13. This proves F(J(G_v)*) = Z(J(G_v)*).

The final adapter takes the complete universal B.5.6 implication and the
earlier local setup: the seed lies in G_v, U_v is elementary abelian,
G_v is SQTK, T_v is Sylow in G_v, and O₂(G_v*) = 1. It constructs the
classification for the literal Thompson image, without assuming a factor
decomposition or a commutator identity. The universal classification and
the solvable exclusion remain explicit inputs for the parent source assembly;
the latter is supplied independently by its 13.6.13 branch.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
the first sentence after 13.6.13, printed p.929.
-/

public section

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FittingCenter
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The first assertion after 13.6.13, from the complete classification of
the actual Thompson action and the explicit solvable exclusion. Generation
of the solvable normal commutator, including every X-family clause, is proved
by the imported structural argument. -/
theorem fitting_eq_center_of_classification
    (L T : Subgroup G) (z v : G) (hz : z ∈ Gv v)
    [IsElementaryAbelian 2 (Uv z v)]
    (hSyl : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (hcore : pCore 2 (Gstar z v) = ⊥)
    (hclassification : FFAlternatives.ProjectiveLine.SourceAlternative
      (thompsonRepresentation z v hz))
    (hexclude : ∀ X ∈ XFamily L T z v, ¬ Group.IsSolvable X) :
    fittingSubgroup (JGstar z v) = center (JGstar z v) :=
  fitting_eq_center_of_commutator_generation L T z v hcore
    (Generation.thompson_generation T z v hz hSyl hcore hclassification) hexclude

/-- Construct the B.5.6 hypothesis on the literal J(G_v)* action and deduce
its Fitting-center equality. The earlier local facts, the complete universal
B.5.6 input, and the independent 13.6.13 exclusion are the only premises
left for the parent existence assembly. -/
theorem fitting_eq_center {K : GroupClass.{u}}
    (classification : FFAlternatives.ProjectiveLine.GeneralClassificationInput.{u,u} K)
    (L T : Subgroup G) (z v : G) (hz : z ∈ Gv v)
    [IsElementaryAbelian 2 (Uv z v)]
    (hlocal : IsSQTK K (Gv v))
    (hSyl : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (hcore : pCore 2 (Gstar z v) = ⊥)
    (hexclude : ∀ X ∈ XFamily L T z v, ¬ Group.IsSolvable X) :
    fittingSubgroup (JGstar z v) = center (JGstar z v) :=
  fitting_eq_center_of_classification L T z v hz hSyl hcore
    (classify_thompson z v hz classification hlocal hcore) hexclude

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FittingCenter
