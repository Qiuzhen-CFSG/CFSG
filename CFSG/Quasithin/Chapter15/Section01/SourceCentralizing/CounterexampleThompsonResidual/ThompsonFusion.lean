module
public import CFSG.Quasithin.Chapter15.Section01.SourceThompsonFixed.CentralizerFusion
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.CounterexampleThompsonResidual

/-!
# The centralizer fusion criterion at the original counterexample Resolver

Apply fusion inside C_G(Z) to the literal full module or original proper
support selected by the Resolver. Retain the source hypotheses, both
counterexample exclusions, and the actual quotient/action conventions in
SourceChosenOrigin. The only new premise asks J(T) to stabilize each conjugate
of the same E, and CentralizerFusion converts it to original 15.1.14.

This is a conditional application. The original ambient stabilization proof
and its full/proper cases remain with qt-e-1514-global-thompson-residual.
The rank-two and subsequent chosen-exclusion inputs retain their existing
owners; none is used to justify the earlier stabilization premise.

Source: Aschbacher--Smith 15.1.3 and 15.1.14, printed pp.1084,1091.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The literal Resolver application, retaining all full source ambient
hypotheses and the two original choices of W. -/
theorem source_centralizing_resolver_of_conjugates_maxJ_normalized
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {Mc : Subgroup G}
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hrank : RankTwoResolver T Mc)
    (hconj : ¬ ClassificationModels.IsTheoremEModel G →
      (∀ N : Subgroup G, IsOrderingMaximal T N →
        ¬ Nonempty (NaturalOrthogonalAction N (localModule T N))) →
      ∀ (M : Subgroup G) (hM : IsOrderingMaximal T M), M ≠ Mc →
        elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G) →
        letI := localModule_elementary_from_source hG T
          ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
        ∀ W : Subgroup G, SourceChosenOrigin T M Mc W → PreparedChosenModule T M W →
          ∀ g ∈ centralizer (centralInvolutions T : Set G),
            elementaryAbelianMaxJ (T : Subgroup G) ≤
              normalizer ((thompsonFixed T W).map (MulAut.conj g).toMonoidHom : Set G))
    (hlarge : SourceLargeChosenExclusionInput hG T Mc)
    (hsmall : SourceSmallChosenExclusionInput hG T Mc) :
    CentralizingResolver T Mc := by
  have hres : SourceCounterexampleThompsonResidualInput hG T Mc := by
    intro hmodel hno M hM hne hJ W hW hp
    exact (hp.thompsonFixed_residual_iff_conjugates_maxJ_normalized hG T hM hJ).mpr
      (hconj hmodel hno M hM hne hJ W hW hp)
  exact source_centralizing_resolver_of_counterexample_residual hG T hempty hu hmany
    hrank hres hlarge hsmall

end CFSG.Quasithin.Chapter15.Section01
