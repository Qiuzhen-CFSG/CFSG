module

public import Theory.SpecificGroups.Rudvalis.SylowAutomorphismSolvability.InvolutionFibers
public import Theory.SpecificGroups.Held.SylowAutomorphismSolvability
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.ComponentReduction.OuterModels.Solvability.SylowModels

/-!
# Full Rudvalis outer solvability from intrinsic involution fibers

The original Rudvalis Sylow candidate has a solvable automorphism group:
its Frattini action permutes three generating involution cosets, with a
two-group kernel. The existing Sylow restriction and S₂ theorem therefore
give full outer solvability, inheriting simplicity only in the actual model
branch. Combining this with the proved Held profile discharges both local
premises of the full Theorem C outer-solvability companion and the literal
perfect-actor action on L/O(L).

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
Proposition A.3.9, pp.45--46. Full A.3.9 recognition and component generation,
and the stronger model realization and Xi restriction statements, retain
their separate owners.
-/

namespace CFSG.Quasithin.Chapter1.XiEmbedding.OuterModels
open Subgroup Theory.GroupTheory

/-- Full Rudvalis outer solvability with simplicity inherited from the source
branch, and no additional local automorphism premise. -/
public theorem rudvalis_outer_isSolvable_of_involution_fibers [IsSimpleGroup Rudvalis.Model] :
    Group.IsSolvable (MulAut.Outer Rudvalis.Model) :=
  rudvalis_outer_isSolvable_of_candidate_aut
    Rudvalis.SylowAutomorphismSolvability.InvolutionFibers.candidate_mulAut_isSolvable

/-- The full Theorem C outer-solvability companion with both literal Sylow
automorphism inputs discharged. -/
public theorem theoremC_outer_isSolvable_of_sylow_profiles
    {S : Type*} [Group S] [Finite S] [IsSimpleGroup S] [Group.IsPerfect S]
    (hS : Section02.LocalModels.TheoremCModel S) :
    Group.IsSolvable (MulAut.Outer S) :=
  theoremC_outer_isSolvable_of_model_sylowAut
    Held.SylowAutomorphismSolvability.representative_mulAut_isSolvable
    Rudvalis.SylowAutomorphismSolvability.InvolutionFibers.candidate_mulAut_isSolvable hS

/-- The actual perfect-actor equality on the literal odd-core quotient, with
both Held and Rudvalis local solvability premises proved. -/
public theorem perfect_actor_sup_oddCore_quotient_centralizer_of_sylow_profiles
    {G : Type*} [Group G] [Finite G] [Group.IsPerfect G]
    (L : Subgroup G) [L.Normal]
    (hQ : IsQuasisimple (L ⧸ pPrimeCore 2 L))
    (hmodel : Section02.LocalModels.TheoremCModel
      ((L ⧸ pPrimeCore 2 L) ⧸ center (L ⧸ pPrimeCore 2 L))) :
    L ⊔ (normalQuotientAction L (pPrimeCore 2 L)).ker = ⊤ :=
  perfect_actor_sup_oddCore_quotient_centralizer_of_model_sylowAut
    Held.SylowAutomorphismSolvability.representative_mulAut_isSolvable
    Rudvalis.SylowAutomorphismSolvability.InvolutionFibers.candidate_mulAut_isSolvable L hQ hmodel

end CFSG.Quasithin.Chapter1.XiEmbedding.OuterModels
