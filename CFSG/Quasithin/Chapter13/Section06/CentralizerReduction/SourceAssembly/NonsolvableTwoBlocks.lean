module
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.TwoBlocks
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly.NonsolvableNoncommuting

/-!
# Residual lifts and exclusion for two original blocks

Construct the second original Context on the literal embedded O²(H).
If both components have their relative block placements, the joined-module
normalizer contradiction forces their natural modules not to commute.
The existing noncommuting extension construction supplies an elementary
A ≤ O²(H) whose image under the literal H → H/O₂(H) has order four.
Thus n(H)=2, discharging the generation premise of original 5.2.3.

The universal exclusion preserves SourceHypothesis after every rechoice
and transports the multiple-overgroup guard. The one-block and
opposite-normalizer alternatives, unrestricted hparameter, earlier-source
discharge, full 13.2.7/13.6.7 and literal nonsingular hCv remain open.
Source: Aschbacher--Smith 13.2.8(1), printed p.880, and 5.2.3.
-/

public section

namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly
open Subgroup Theory.GroupTheory Stellmacher
open Section05.A5Source Section02.A5Outside
open Section02.A5Outside.OriginalCentralization ChapterC
open ComponentElimination.SourceContainment.RankTwo.LocalApplication
open TerminalContradiction.Components.SuzukiIsolation
universe u
variable {G : Type u} [Group G] [Finite G]

theorem original_nonsolvable_two_blocks_parameter
    {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}
    (d : Context T L V V₁ V₂ V₃) (hc : IsA5Counterexample G)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (h1332 : ∀ (S : Sylow 2 G) (I : Subgroup G),
      Chapter14.Section03.FaithfulSource.Hypothesis1331 S I →
        (S : Subgroup G) ≤ normalizer (I : Set G))
    (hcontexts : ∀ (S : Sylow 2 G) (I : Subgroup G), SourceHypothesis S I →
      ∃ W W₁ W₂ W₃ : Subgroup G, Nonempty (Context S I W W₁ W₂ W₃))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : ¬ Group.IsSolvable H)
    (hbL : IsBlock (L.subgroupOf (L ⊔ (T : Subgroup G))))
    (hbH : IsBlock (((pResidual 2 H).map H.subtype).subgroupOf H)) :
    (∃ A : Subgroup H, IsElementaryAbelian 2 A ∧ A ≤ pResidual 2 H ∧
      Nat.card (A.map (QuotientGroup.mk' (pCore 2 H))) = 4) ∧
      ChapterE.generationParameter H = 2 := by
  obtain ⟨W,W₁,W₂,W₃,e,q,_,hq,hk,_,hr,he⟩ :=
    original_nonsolvable_marked_action d hc hmany h1332 hcontexts hH hZ hs
  have hjoin : (pResidual 2 H).map H.subtype ⊔ (T : Subgroup G) = H := by
    have hh := congrArg (map H.subtype) (pResidual_sup_sylow_eq_top (T.subtype hH.1.1.2))
    rw [Subgroup.map_sup,←MonoidHom.range_eq_map,range_subtype] at hh
    change (pResidual 2 H).map H.subtype ⊔
      ((T : Subgroup G).subgroupOf H).map H.subtype = H at hh
    rwa [map_subgroupOf_eq_of_le hH.1.1.2] at hh
  have hm := original_block_pair_noncommuting d e hjoin hH hbL hbH
  exact original_nonsolvable_noncommuting_parameter d h1332 hH hZ hs e q hq hk hr he hm

/-- The generation premise for original 5.2.3 is discharged in the two-block case. -/
theorem original_nonsolvable_two_blocks_model
    {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}
    (d : Context T L V V₁ V₂ V₃) (hc : IsA5Counterexample G)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (h1332 : ∀ (S : Sylow 2 G) (I : Subgroup G),
      Chapter14.Section03.FaithfulSource.Hypothesis1331 S I →
        (S : Subgroup G) ≤ normalizer (I : Set G))
    (hcontexts : ∀ (S : Sylow 2 G) (I : Subgroup G), SourceHypothesis S I →
      ∃ W W₁ W₂ W₃ : Subgroup G, Nonempty (Context S I W W₁ W₂ W₃))
    (h523 : Source523.EarlierTheorem.{u} KnownSimple.IsKnownSimple)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : ¬ Group.IsSolvable H)
    (hbL : IsBlock (L.subgroupOf (L ⊔ (T : Subgroup G))))
    (hbH : IsBlock (((pResidual 2 H).map H.subtype).subgroupOf H)) :
    ClassificationModels.IsQTKEModel G := by
  have hn := (original_nonsolvable_two_blocks_parameter d hc hmany h1332 hcontexts
    hH hZ hs hbL hbH).2
  exact main_model_of_source523_omega_movement d h523 hH hZ (by omega)

/-- The two relative block placements cannot both survive any guarded original rechoice. -/
theorem universal_original_nonsolvable_not_two_blocks
    (T : Sylow 2 G)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hc : IsA5Counterexample G) (hno : ¬ ClassificationModels.IsQTKEModel G)
    (h1332 : ∀ (S : Sylow 2 G) (I : Subgroup G),
      Chapter14.Section03.FaithfulSource.Hypothesis1331 S I →
        (S : Subgroup G) ≤ normalizer (I : Set G))
    (hcontexts : ∀ (S : Sylow 2 G) (I : Subgroup G), SourceHypothesis S I →
      ∃ W W₁ W₂ W₃ : Subgroup G, Nonempty (Context S I W W₁ W₂ W₃))
    (h523 : Source523.EarlierTheorem.{u} KnownSimple.IsKnownSimple)
    (S : Sylow 2 G) (I : Subgroup G) (standing : SourceHypothesis S I)
    (H : Subgroup G)
    (hH : H ∈ Chapter3.HStar (S : Subgroup G) (normalizer (I : Set G)))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (S : Subgroup G) : Set G))
    (hs : ¬ Group.IsSolvable H) :
    ¬ (IsBlock (I.subgroupOf (I ⊔ (S : Subgroup G))) ∧
      IsBlock (((pResidual 2 H).map H.subtype).subgroupOf H)) := by
  obtain ⟨V,V₁,V₂,V₃,⟨d⟩⟩ := hcontexts S I standing
  have hmanyS : 1 < (maximalTwoLocalOvergroups (S : Subgroup G)).ncard := by
    rwa [maximalTwoLocalOvergroups_ncard_sylow S T]
  rintro ⟨hbI,hbH⟩
  exact hno (original_nonsolvable_two_blocks_model d hc hmanyS h1332 hcontexts
    h523 hH hZ hs hbI hbH)
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly
