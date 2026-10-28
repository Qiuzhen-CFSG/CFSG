module

public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.FactorSelfCentralizing.ModelExclusion.Even.Action
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.FactorSelfCentralizing.ModelExclusion.Even.Models

/-!
# The original even marked-component exclusion

The faithful action of the actual quotient centralizer and the intrinsic
even-model centralizer bound discharge the two inputs of the even exclusion.
Both constructions retain the original marked point, component and action.
The resulting theorem feeds the marked-model assembly, whose independent
quaternion-extension and sporadic inputs remain explicit.

Source: Aschbacher--Smith, 14.3.20, printed p.998, and 1.1.5(3)(a--b).
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.SelfCentralizing
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
universe u
variable {G : Type u} [Group G] [Finite G]

variable
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)]
    (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P (sourceResidual M Mc)) (hgH : g ∉ F.H)
    (hs : Group.IsSolvable F.TerminalHdot)

include hG hempty hM hu hmany hcard e hnot hne hgP hgH hs

/-- The original even exclusion, with both independent centralizer inputs
discharged and the original solvability hypothesis retained. -/
theorem evenExclusionSource_of_source_inputs :
    EvenExclusionSource F (sourceResidual M Mc) :=
  evenExclusionSource_of_source_inputs_and_model_bounds
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
    evenModelCentralizerBounds

/-- The literal marked-model consumer after discharging the even branch.
Its independent local-extension and sporadic obligations remain explicit. -/
theorem modelExclusionSource_of_source_inputs_and_local_sporadic
    (hlocal : QuotientCentralizerSource F (sourceResidual M Mc))
    (hsporadic : SporadicExclusionSource F (sourceResidual M Mc)) :
    ModelExclusionSource F (sourceResidual M Mc) :=
  modelExclusionSource_of_local_inputs F (sourceResidual M Mc) hlocal
    (evenExclusionSource_of_source_inputs
      hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs) hsporadic

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.SelfCentralizing
