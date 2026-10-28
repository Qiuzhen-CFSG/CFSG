module
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.OneBlock
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly.NonsolvableBlocks
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly.NonsolvableNoncommuting

/-!
# Residual lifts from either original alternating block

A single block in either original relative overgroup forces the natural
modules not to commute. The block core split and the Sylow fixed-line
calculation produce a hyperplane centralized by that block; original
13.2.3(2) contradicts outside placement. The established noncommuting
construction then supplies an elementary subgroup of the literal O²(H)
whose image under H → H/O₂(H) has order four. Thus n(H)=2 and original
5.2.3 excludes both block alternatives.

The universal application leaves only opposite normalization of the same
Baumann pair, after every guarded original rechoice. The multiple-overgroup
hypothesis is transported. The opposite-normalizer case, unrestricted
hparameter, earlier-source discharge, full 13.2.7/13.6.7 assembly and the
literal nonsingular hCv remain open.
Source: Aschbacher--Smith 13.2.3(2), 13.2.8(1), pp.879--880;
C.1.13(c), pp.124--125; C.1.24(a), pp.130--131; and 5.2.3.
-/

public section

namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly
open Subgroup Theory.GroupTheory Stellmacher
open Section05.A5Source Section02.A5Outside
open Section02.A5Outside.OriginalCentralization ChapterB ChapterC
open ComponentElimination.SourceContainment.RankTwo.LocalApplication
open TerminalContradiction.Components.SuzukiIsolation
universe u
variable {G : Type u} [Group G] [Finite G]

theorem original_nonsolvable_one_block_parameter
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
    (hb : (IsBlock (L.subgroupOf (L ⊔ (T : Subgroup G))) ∧ IsAlternatingBlock L 5) ∨
      (IsBlock (((pResidual 2 H).map H.subtype).subgroupOf H) ∧
        IsAlternatingBlock ((pResidual 2 H).map H.subtype) 5)) :
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
  have hm := original_one_block_noncommuting d e hjoin hH
    (localActor_surjective_of_omega_movement d hH hZ) q hq hk hb
  exact original_nonsolvable_noncommuting_parameter d h1332 hH hZ hs e q hq hk hr he hm

/-- The generation premise for original 5.2.3 is discharged for either original block. -/
theorem original_nonsolvable_one_block_model
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
    (hb : (IsBlock (L.subgroupOf (L ⊔ (T : Subgroup G))) ∧ IsAlternatingBlock L 5) ∨
      (IsBlock (((pResidual 2 H).map H.subtype).subgroupOf H) ∧
        IsAlternatingBlock ((pResidual 2 H).map H.subtype) 5)) :
    ClassificationModels.IsQTKEModel G := by
  have hn := (original_nonsolvable_one_block_parameter d hc hmany h1332 hcontexts
    hH hZ hs hb).2
  exact main_model_of_source523_omega_movement d h523 hH hZ (by omega)

/-- Only opposite normalization of the same universal pair survives the
original 5.2.3 comparison. Both single-block alternatives are excluded. -/
theorem original_nonsolvable_opposite_baumann
    {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}
    (d : Context T L V V₁ V₂ V₃) (hc : IsA5Counterexample G)
    (hno : ¬ ClassificationModels.IsQTKEModel G)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (h1332 : ∀ (S : Sylow 2 G) (I : Subgroup G),
      Chapter14.Section03.FaithfulSource.Hypothesis1331 S I →
        (S : Subgroup G) ≤ normalizer (I : Set G))
    (hcontexts : ∀ (S : Sylow 2 G) (I : Subgroup G), SourceHypothesis S I →
      ∃ W W₁ W₂ W₃ : Subgroup G, Nonempty (Context S I W W₁ W₂ W₃))
    (h523 : Source523.EarlierTheorem.{u} KnownSimple.IsKnownSimple)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : ¬ Group.IsSolvable H) :
    ∃ D : GlaubermanNiles.CharacteristicPair (baumann (T : Subgroup G)),
      Nat.card (omegaOneCenterAmbient (T : Subgroup G)) = 4 ∧
      D.Universal.{u,u} ∧ D.first ≠ D.second ∧
      ((L ⊔ (T : Subgroup G) ≤ normalizer
          (D.first.map (baumann (T : Subgroup G)).subtype : Set G) ∧
        H ≤ normalizer (D.second.map (baumann (T : Subgroup G)).subtype : Set G)) ∨
      (L ⊔ (T : Subgroup G) ≤ normalizer
          (D.second.map (baumann (T : Subgroup G)).subtype : Set G) ∧
        H ≤ normalizer (D.first.map (baumann (T : Subgroup G)).subtype : Set G))) := by
  obtain ⟨W,W₁,W₂,W₃,e,D,hfour,hD,_,_,hcases⟩ :=
    original_nonsolvable_baumann_block_alternatives d hc hno hmany h1332 hcontexts h523 hH hZ hs
  rcases hcases with hL | hK | hn
  · exact (hno (original_nonsolvable_one_block_model d hc hmany h1332 hcontexts h523
      hH hZ hs (Or.inl ⟨hL.1,hL.2.1⟩))).elim
  · exact (hno (original_nonsolvable_one_block_model d hc hmany h1332 hcontexts h523
      hH hZ hs (Or.inr ⟨hK.1,hK.2.1⟩))).elim
  · exact ⟨D,hfour,hD,hn⟩

/-- The opposite-normalizer reduction holds after every original guarded
Sylow/component rechoice, retaining the multiple-overgroup hypothesis. -/
theorem universal_original_nonsolvable_opposite_baumann
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
    ∃ D : GlaubermanNiles.CharacteristicPair (baumann (S : Subgroup G)),
      Nat.card (omegaOneCenterAmbient (S : Subgroup G)) = 4 ∧
      D.Universal.{u,u} ∧ D.first ≠ D.second ∧
      ((I ⊔ (S : Subgroup G) ≤ normalizer
          (D.first.map (baumann (S : Subgroup G)).subtype : Set G) ∧
        H ≤ normalizer (D.second.map (baumann (S : Subgroup G)).subtype : Set G)) ∨
      (I ⊔ (S : Subgroup G) ≤ normalizer
          (D.second.map (baumann (S : Subgroup G)).subtype : Set G) ∧
        H ≤ normalizer (D.first.map (baumann (S : Subgroup G)).subtype : Set G))) := by
  obtain ⟨V,V₁,V₂,V₃,⟨d⟩⟩ := hcontexts S I standing
  have hmanyS : 1 < (maximalTwoLocalOvergroups (S : Subgroup G)).ncard := by
    rwa [maximalTwoLocalOvergroups_ncard_sylow S T]
  exact original_nonsolvable_opposite_baumann d hc hno hmanyS h1332 hcontexts h523 hH hZ hs
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly
