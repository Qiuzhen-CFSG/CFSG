module

public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationNaturalHStarSourceOvercomponent
public import CFSG.Quasithin.Chapter12.Section02.ModuleClassification.ComponentUniqueness

/-!
# The original H-star component is the two-residual

The nonquasisimple-overcomponent exclusion produces a faithful maximal Y
satisfying the original 12.2.3 hypotheses. Its seven-module classification
implies uniqueness of C-components in intrinsic Sylow overgroups. Applying
that uniqueness to the chain X ≤ Y forces T to normalize X. The E.2.2
orbit identity therefore becomes the literal equality X = O²(H).

This yields quasisimplicity of the original residual modulo its own two-core
and removes the normalization premise from the existing A₅ rank consumer.
The A₅ identification and the remaining module restrictions of 12.2.7 are
still owned by qt-d-12213-hstar-natural, along with final 12.2.19 assembly.
Structural1222At and Theorem1222ModulesAt remain the allowed earlier inputs.

Source: Aschbacher–Smith, 12.2.7, printed pp.797–798, using 1.2.8(1)
and E.2.2. The same-G,T multiple-overgroup standing hypothesis is explicit.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02
open Chapter1.Section02.MovedMaximality
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G}

namespace RecognitionSource
open ChapterI.Section06To08
variable {H X Y : Subgroup G}

/-- The seven module alternatives on the actual containing component
force T to normalize the original generating component. -/
theorem HStarGeneratingComponent.normalized_of_overcomponent_at
    (C : HStarGeneratingComponent T L H X)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hXY : X ≤ Y) (hY : Hypothesis1223 KnownSimple.IsKnownSimple T Y) :
    (T : Subgroup G) ≤ normalizer (X : Set G) := by
  obtain ⟨⟨W,⟨E⟩⟩⟩ := (structural Y hY).2.1
  exact local_chain_normalizes_of_sylow_overgroup_unique T
    (C.exists_maximal_overcomponent hH).1 hY.maximal_faithful.1.1 hXY
    (structural Y hY).1
    (E.sylowOvergroupComponentUnique_of_alternatives hY.quasisimple (modules Y W hY E))

/-- The original component is literally the embedded O²(H), and its
faithful maximal overcomponent satisfies the original source hypotheses. -/
theorem chosen_hstar_exists_residual_overcomponent_of_many_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hnone : NoEscape L V) (hTI : IsTISubgroup V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hs : ¬ Group.IsSolvable H) :
    ∃ X Y : Subgroup G, HStarGeneratingComponent T L H X ∧
      X = (pResidual 2 H).map H.subtype ∧ X ≤ Y ∧
      Hypothesis1223 KnownSimple.IsKnownSimple T Y := by
  obtain ⟨X,Y,C,hXY,hY⟩ := chosen_hstar_exists_quasisimple_overcomponent_of_many_at
    h D structural hmany hnone hTI hH hs
  exact ⟨X,Y,C,C.eq_residual_of_normalized
    (C.normalized_of_overcomponent_at structural modules hH hXY hY),hXY,hY⟩

/-- Transport through the original residual inclusion gives quasisimplicity
of its own two-core quotient, with no model marking assumed. -/
theorem chosen_hstar_residual_quasisimple_of_many_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hnone : NoEscape L V) (hTI : IsTISubgroup V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hs : ¬ Group.IsSolvable H) :
    IsQuasisimple (pResidual 2 H ⧸ pCore 2 (pResidual 2 H)) := by
  obtain ⟨X,Y,C,he,_,_⟩ := chosen_hstar_exists_residual_overcomponent_of_many_at
    h D structural modules hmany hnone hTI hH hs
  let e : X ≃* pResidual 2 H := (MulEquiv.subgroupCongr he).trans
    ((pResidual 2 H).equivMapOfInjective H.subtype H.subtype_injective).symm
  let := C.quasisimple
  exact IsQuasisimple.of_mulEquiv (QuotientGroup.congr _ _ e (pCore_map_iso 2 e))

/-- Apply the original rank consumer with the Sylow-normalization premise
discharged. The remaining A₅ identification is the model comparison in
12.2.7(2), retained with qt-d-12213-hstar-natural. -/
theorem chosen_hstar_quotient_rank_of_five_overcomponent_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (hTI : IsTISubgroup V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (C : HStarGeneratingComponent T L H X) (hXY : X ≤ Y)
    (hY : Hypothesis1223 KnownSimple.IsKnownSimple T Y)
    (hf : Nonempty ((X ⧸ pCore 2 X) ≃* alternatingGroup (Fin 5))) :
    primeRank 2 (H ⧸ pCore 2 H) ≤ 2 :=
  chosen_hstar_quotient_rank_of_generating_five_component_at h D structural hTI hH C
    (C.normalized_of_overcomponent_at structural modules hH hXY hY) hf

end RecognitionSource
end CFSG.Quasithin.Chapter12.Section02
