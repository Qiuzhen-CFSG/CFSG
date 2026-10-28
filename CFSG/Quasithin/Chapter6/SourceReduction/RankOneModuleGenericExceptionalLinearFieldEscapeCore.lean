module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldEscapeDefs
public import Theory.GroupTheory.TwoLocalCoreObstruction

/-!
# Trivial two-core of the group generated in the escaping branch

The original uniqueness of the maximal two-local over H makes the join
⟨L₂,T,H⟩ have trivial two-core whenever C escapes N_G(O²(H)). Otherwise
a maximal two-local over this join would equal that normalizer and contain
C ≤ L₂. This supplies the generated-core clause of the F.8 construction
directly, without the normalizing-branch argument in 5.1.20.

Source: Aschbacher--Smith, 5.1.14(1), 5.1.20 and the final paragraph
on printed p.646 of `refs/quasithin.pdf`.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.CubicEscape
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {H C : Subgroup G}

theorem generated_core_eq_bot
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hTH : (T : Subgroup G) ≤ H)
    (hK : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hout : ¬ C ≤ normalizer (residual H : Set G)) :
    pCore 2 ((actor T C ⊔ (T : Subgroup G)) ⊔ H : Subgroup G) = ⊥ := by
  by_contra hcore
  obtain ⟨M, hM, hJM⟩ := exists_maximalTwoLocal_overgroup_of_twoCore_ne_bot _ hcore
  have hMN := residual_unique_of_maximal hG hTH hK M hM (le_sup_right.trans hJM)
  apply hout
  rw [← hMN]
  exact (le_conjugateSpanBy C (T : Subgroup G)).trans
    (le_sup_left.trans (le_sup_left.trans hJM))

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.CubicEscape
