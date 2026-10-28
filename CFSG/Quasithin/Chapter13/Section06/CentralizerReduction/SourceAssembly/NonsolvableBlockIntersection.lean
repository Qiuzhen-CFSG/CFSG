module
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.BlockIntersection
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly.NonsolvableDerived

/-!
# Frattini constraints on the surviving original block alternatives

Construct the second Context on the literal embedded O²(H). The existing
noncommuting-module lift and original 5.2.3 force the natural modules to
commute in a remaining counterexample. The original core actions then give
noncyclic derived subgroups in both cores, hence noncyclic Frattini images.
Each image is normalized by its own local group. Original maximal-local
uniqueness excludes its normalization by the other group.

If an original local group is a block, the short-block square calculation
makes it centralize its core Frattini image. If both are blocks, their
Frattini images are disjoint and commute, and the actual core intersection
is elementary abelian. The relative subnormal placements are kept in their
separate local groups. No commutation of the blocks, core equality or lift
is assumed. The universal application preserves SourceHypothesis and the
multiple-overgroup guard after every Sylow/component rechoice.

These constraints do not close either individual block alternative or the
opposite-normalizer branch. The residual four-group lift, unrestricted
hparameter, earlier-source discharge, full 13.2.7/13.6.7 and literal hCv
remain with the original assembly owner.
Source: Aschbacher--Smith C.1.7--8, pp.123--124; 1.2.7, pp.506--507;
13.2.3--4 and the nonsolvable step of 13.2.8(1), pp.878--880; and 5.2.3.
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

private theorem noncyclic_frattini_of_derived (Q : Subgroup G) (hp : IsPGroup 2 Q)
    (hd : ¬ IsCyclic (⁅Q,Q⁆ : Subgroup G)) :
    ¬ IsCyclic ((frattini Q).map Q.subtype) := by
  intro hc
  let := hc
  let : Fact (IsPGroup 2 Q) := ⟨hp⟩
  have he : ⁅Q,Q⁆ ≤ (frattini Q).map Q.subtype := by
    have hh := map_mono (f := Q.subtype) (commutator_le_frattini_of_isPGroup (p := 2) (R := Q))
    rwa [map_subtype_commutator] at hh
  exact hd (isCyclic_of_injective (inclusion he) (inclusion_injective _))

/-- Every surviving original pair has two noncyclic core Frattini images whose
normalizers escape the opposite local group. A block centralizes its image;
two blocks force the literal core intersection to be elementary. -/
theorem original_nonsolvable_block_frattini
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
    let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
    let P := H.pCoreIn 2
    let FQ := (frattini Q).map Q.subtype
    let FP := (frattini P).map P.subtype
    ¬ IsCyclic FQ ∧ ¬ IsCyclic FP ∧
      ¬ H ≤ normalizer (FQ : Set G) ∧
      ¬ L ⊔ (T : Subgroup G) ≤ normalizer (FP : Set G) ∧
      (IsBlock (L.subgroupOf (L ⊔ (T : Subgroup G))) → FQ ≤ centralizer (L : Set G)) ∧
      (IsBlock (((pResidual 2 H).map H.subtype).subgroupOf H) →
        FP ≤ centralizer ((pResidual 2 H).map H.subtype : Set G)) ∧
      (IsBlock (L.subgroupOf (L ⊔ (T : Subgroup G))) →
        IsBlock (((pResidual 2 H).map H.subtype).subgroupOf H) →
        IsElementaryAbelian 2 (Q ⊓ P : Subgroup G) ∧ Disjoint FQ FP ∧ ⁅FQ,FP⁆ = ⊥) := by
  obtain ⟨W,W₁,W₂,W₃,e,q,_,hq,hk,_,hr,he⟩ :=
    original_nonsolvable_marked_action d hc hmany h1332 hcontexts hH hZ hs
  have hjoin : (pResidual 2 H).map H.subtype ⊔ (T : Subgroup G) = H := by
    have hh := congrArg (map H.subtype) (pResidual_sup_sylow_eq_top (T.subtype hH.1.1.2))
    rw [Subgroup.map_sup,←MonoidHom.range_eq_map,range_subtype] at hh
    change (pResidual 2 H).map H.subtype ⊔
      ((T : Subgroup G).subgroupOf H).map H.subtype = H at hh
    rwa [map_subgroupOf_eq_of_le hH.1.1.2] at hh
  have hVW : V ≤ centralizer (W : Set G) := by
    by_contra hm
    have hp := (original_nonsolvable_noncommuting_parameter d h1332 hH hZ hs
      e q hq hk hr he hm).2
    exact hno (main_model_of_source523_omega_movement d h523 hH hZ (by omega))
  have hder := original_commuting_pair_noncyclic_cores d e hjoin hH
    (localActor_surjective_of_omega_movement d hH hZ) q hq hk he hVW
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  let P := H.pCoreIn 2
  let FQ := (frattini Q).map Q.subtype
  let FP := (frattini P).map P.subtype
  have hFQ : ¬ IsCyclic FQ := noncyclic_frattini_of_derived Q (isPGroup_pCoreIn 2 _) hder.2
  have hFP : ¬ IsCyclic FP := noncyclic_frattini_of_derived P (isPGroup_pCoreIn 2 _) hder.1
  have hFQne : FQ ≠ ⊥ := by
    intro hz
    apply hFQ
    rw [hz]
    infer_instance
  have hFPne : FP ≠ ⊥ := by
    intro hz
    apply hFP
    rw [hz]
    infer_instance
  have hQnorm : L ⊔ (T : Subgroup G) ≤ normalizer (FQ : Set G) :=
    ((L ⊔ (T : Subgroup G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _
        (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G)))).trans
      (normalizer_le_normalizer_characteristic_image Q (frattini Q))
  have hPnorm : H ≤ normalizer (FP : Set G) :=
    (H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H))).trans
      (normalizer_le_normalizer_characteristic_image P (frattini P))
  have hnotQ : ¬ H ≤ normalizer (FQ : Set G) := by
    intro hn
    have hN := normalizer_le_of_unique_maximalTwoLocal d.unique_maximal_overgroup
      ((isPGroup_pCoreIn 2 (L ⊔ (T : Subgroup G))).to_le (map_subtype_le (frattini Q)))
      hFQne hQnorm
    exact hH.1.2 (hn.trans hN)
  have hnotP : ¬ L ⊔ (T : Subgroup G) ≤ normalizer (FP : Set G) := by
    intro hn
    have hN := normalizer_le_of_unique_maximalTwoLocal d.unique_maximal_overgroup
      ((isPGroup_pCoreIn 2 H).to_le (map_subtype_le (frattini P))) hFPne hn
    exact hH.1.2 (hPnorm.trans hN)
  refine ⟨hFQ,hFP,hnotQ,hnotP,?_,?_,?_⟩
  · exact fun hb => relative_core_frattini_centralizes le_sup_left hb
  · exact fun hb => relative_core_frattini_centralizes (map_subtype_le _) hb
  · intro hbL hbK
    exact ⟨original_block_pair_core_intersection_elementary d e hjoin hH hbL hbK,
      original_block_pair_frattini_disjoint d e hjoin hH hbL hbK,
      original_block_pair_frattini_commute d e hjoin hH hbL hbK⟩

/-- The same literal intersection and Frattini geometry apply after every
guarded original Sylow/component rechoice. -/
theorem universal_original_nonsolvable_block_frattini
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
    let Q := (I ⊔ (S : Subgroup G)).pCoreIn 2
    let P := H.pCoreIn 2
    let FQ := (frattini Q).map Q.subtype
    let FP := (frattini P).map P.subtype
    ¬ IsCyclic FQ ∧ ¬ IsCyclic FP ∧
      ¬ H ≤ normalizer (FQ : Set G) ∧
      ¬ I ⊔ (S : Subgroup G) ≤ normalizer (FP : Set G) ∧
      (IsBlock (I.subgroupOf (I ⊔ (S : Subgroup G))) → FQ ≤ centralizer (I : Set G)) ∧
      (IsBlock (((pResidual 2 H).map H.subtype).subgroupOf H) →
        FP ≤ centralizer ((pResidual 2 H).map H.subtype : Set G)) ∧
      (IsBlock (I.subgroupOf (I ⊔ (S : Subgroup G))) →
        IsBlock (((pResidual 2 H).map H.subtype).subgroupOf H) →
        IsElementaryAbelian 2 (Q ⊓ P : Subgroup G) ∧ Disjoint FQ FP ∧ ⁅FQ,FP⁆ = ⊥) := by
  obtain ⟨V,V₁,V₂,V₃,⟨d⟩⟩ := hcontexts S I standing
  have hmanyS : 1 < (maximalTwoLocalOvergroups (S : Subgroup G)).ncard := by
    rwa [maximalTwoLocalOvergroups_ncard_sylow S T]
  exact original_nonsolvable_block_frattini d hc hno hmanyS h1332 hcontexts
    h523 hH hZ hs
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly
