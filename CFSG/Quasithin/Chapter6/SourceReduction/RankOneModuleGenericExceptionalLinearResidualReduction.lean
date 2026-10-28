module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearResidualGraph
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinear
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.SourceNormality
public import CFSG.Quasithin.Chapter3.Section02.SourceSelection

/-!
# Isolating the two source exclusions for the exceptional residual

The local-family residual has a unique normal containing C-component in
each actual local overgroup, by the proved 1.2.4 theorem. A proper enlargement
would therefore supply exactly the embedding forbidden in 5.1.12. Once this
exclusion is proved, maximality follows by applying C-component maximality
inside E T for every E in L(G,T) above the residual.

Faithfulness of that maximal residual constructs the original Fundamental
Setup by 3.2.3. Its T-orbit is the residual itself and its local join is H.
The second independent source obligation is that such an FSU cannot admit
the diagram actor already constructed in ResidualGraph. It is the specialized
3.2.5, 3.2.8 and 3.2.9 argument, retaining the actual multiple-overgroup guard.

The two exclusions below are explicit, unproved source inputs. The final
theorem is a conditional assembly, not a proof of unconditional 5.1.14(1).
Source: Aschbacher–Smith, 1.2.4, 3.2.3–9, 5.1.12 and 5.1.14(1),
printed pp.505,580–583,635,638 (refs/quasithin.pdf).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The proper-containing-component exclusion needed from 5.1.12.
Normality is relative to Y, and the embedded component is C.map Y.subtype. -/
@[expose] def LinearFourEmbeddingExclusion (G : Type u) [Group G] [Finite G] : Prop :=
  ∀ (T : Sylow 2 G) (K : Subgroup G), K ∈ Chapter1.L G (T : Subgroup G) →
    (T : Subgroup G) ≤ normalizer (K : Set G) →
    ∀ Y ∈ Chapter1.HOver G (T : Set G), ∀ C : Subgroup Y,
      C.IsCComponent → C.Normal → K ≤ C.map Y.subtype → K ≠ C.map Y.subtype →
        ¬ HasLinearFourGraphAction (T : Subgroup G) K

/-- The specialized FSU diagram exclusion in 3.2.5,8,9. This retains the
standing outside guard through the actual multiple-overgroup hypothesis. -/
@[expose] def LinearFourFSUDiagramExclusion (G : Type u) [Group G] [Finite G] : Prop :=
  ∀ (T : Sylow 2 G) (K : Subgroup G),
    1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
    Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T K →
    (T : Subgroup G) ≤ normalizer (K : Set G) →
      ¬ HasLinearFourGraphAction (T : Subgroup G) K

omit [Finite G] in
/-- The linear quotient marking is transported through the literal inclusion in G. -/
theorem linear_residual_quotient {H : Subgroup G}
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4) :
    ClassicalGroup.IsPSL ((residual H) ⧸ pCore 2 (residual H)) 3 4 := by
  let e := (pResidual 2 H).equivMapOfInjective H.subtype H.subtype_injective
  exact hlinear.of_mulEquiv (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).symm

omit [Finite G] in
/-- The FSU actor is the original residual: T already normalizes it. -/
theorem residual_localOrbit_eq {T : Sylow 2 G} {H : Subgroup G}
    (hTH : (T : Subgroup G) ≤ H) :
    Chapter3.Section02.localOrbit T (residual H) = residual H :=
  le_antisymm (iSup_conjugates_le_of_le_normalizer _ _ _ le_rfl
    (hTH.trans (le_normalizer_residual H))) (le_componentOrbit _ _)

/-- The FSU reduced subgroup is R₂(H), with H the original H* member. -/
theorem residual_localJoin_eq {T : Sylow 2 G} {H : Subgroup G}
    (hTH : (T : Subgroup G) ≤ H) :
    Chapter3.Section02.localJoin T (residual H) = H := by
  change Chapter3.Section02.localOrbit T (residual H) ⊔ (T : Subgroup G) = H
  rw [residual_localOrbit_eq hTH, residual_sup_sylow T H hTH]

/-- Assuming maximality and faithfulness constructs a genuine FSU; its seed
is selected from the actual reduced subgroup, not supplied by a callback. -/
theorem linear_residual_fundamentalSetup {T : Sylow 2 G} {H : Subgroup G}
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hmax : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hf : ChapterA.Section04.IsFaithfulSignalizerType (residual H)) :
    Nonempty (Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T
      (residual H)) := by
  obtain ⟨F, _, _, _, ⟨e⟩⟩ := linear_residual_quotient hlinear
  let : IsQuasisimple ((residual H) ⧸ pCore 2 (residual H)) :=
    IsQuasisimple.of_mulEquiv e.symm
  exact Chapter3.Section02.source_exists_fundamentalSetup hG T (residual H)
    hmax hf inferInstance

/-- Construct the actual normal containing component in every local overgroup
of H. No component classification or diagram exclusion is assumed. -/
theorem linear_residual_containing_component {T : Sylow 2 G} {H Y : Subgroup G}
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hH : H ∈ Chapter1.HOver G (T : Set G))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hY : Y ∈ Chapter1.HOver G (H : Set G)) :
    ∃ C : Subgroup Y, C.IsCComponent ∧ C.Normal ∧ residual H ≤ C.map Y.subtype := by
  have hTY : (T : Subgroup G) ≤ Y := hH.2.trans hY.2
  have hRY : residual H ≤ Y := (map_subtype_le _).trans hY.2
  let S := T.subtype hTY
  have hr : (residual H).subgroupOf Y ∈ Chapter1.L Y (S : Subgroup Y) := by
    change (residual H).subgroupOf Y ∈ Chapter1.L Y ((T : Subgroup G).subgroupOf Y)
    exact (Chapter1.mem_LIn_iff_subgroupOf hTY hRY).mp
      ⟨hRY, linear_residual_mem_localFamily hH hlinear⟩
  have hn : (S : Subgroup Y) ≤ normalizer (((residual H).subgroupOf Y : Subgroup Y) : Set Y) := by
    intro s hs
    apply mem_normalizer_iff.mpr
    intro x
    exact mem_normalizer_iff.mp ((hH.2.trans (le_normalizer_residual H)) hs) (x : G)
  obtain ⟨C, ⟨hC, hRC, hnC⟩, _⟩ :=
    Chapter1.Section02.lemma_1_2_4_containment_normality_source
      (Chapter1.Section02.uniqueness_local_quotient_sqtk hG hY.1) S hr hn
  refine ⟨C, hC, hnC, ?_⟩
  simpa only [map_subgroupOf_eq_of_le hRY] using map_mono (f := Y.subtype) hRC

/-- Apply the proper-embedding exclusion to the constructed component inside
E T, then use C-component maximality to obtain maximality in L(G,T). -/
theorem linear_residual_maximal_of_embedding_exclusion
    {T : Sylow 2 G} {M H : Subgroup G}
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hTM : (T : Subgroup G) ≤ M)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hemb : LinearFourEmbeddingExclusion G) :
    residual H ∈ Chapter1.LStar G (T : Subgroup G) := by
  have hr := linear_residual_mem_localFamily hH.1.1 hlinear
  have hg := linear_residual_graph_action T hTM hH hlinear
  refine ⟨hr, ?_⟩
  intro E hE hRE
  let Y := E ⊔ (T : Subgroup G)
  have hHY : H ≤ Y := by
    rw [← residual_sup_sylow T H hH.1.1.2]
    exact sup_le_sup_right hRE _
  have hY : Y ∈ Chapter1.HOver G (H : Set G) := ⟨hE.2.2, hHY⟩
  obtain ⟨C, hC, hnC, hRC⟩ := linear_residual_containing_component hG hH.1.1 hlinear hY
  have heq : residual H = C.map Y.subtype := by
    by_contra hne
    exact hemb T (residual H) hr (hH.1.1.2.trans (le_normalizer_residual H))
      Y ⟨hY.1, (show (T : Subgroup G) ≤ Y from le_sup_right)⟩ C hC hnC hRC hne hg
  have hCE : C ≤ E.subgroupOf Y := by
    intro c hc
    exact hRE (heq.symm ▸ mem_map_of_mem Y.subtype hc)
  have he := congrArg (map Y.subtype) (hC.eq_of_le hE.1 hCE)
  rw [map_subgroupOf_eq_of_le (show E ≤ Y from le_sup_left)] at he
  exact he.symm.trans heq.symm

/-- Conditional 5.1.14(1) assembly. Both earlier source exclusions still
require independent proofs before this gives the unconditional theorem. -/
theorem linear_residual_maximal_nonfaithful_of_exclusions
    {T : Sylow 2 G} {M H : Subgroup G}
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hTM : (T : Subgroup G) ≤ M)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hemb : LinearFourEmbeddingExclusion G) (hfsu : LinearFourFSUDiagramExclusion G) :
    residual H ∈ Chapter1.LStar G (T : Subgroup G) ∧
      ¬ ChapterA.Section04.IsFaithfulSignalizerType (residual H) := by
  have hm := linear_residual_maximal_of_embedding_exclusion hG hTM hH hlinear hemb
  refine ⟨hm, ?_⟩
  intro hf
  obtain ⟨D⟩ := linear_residual_fundamentalSetup hG hlinear hm hf
  exact hfsu T (residual H) hmany D (hH.1.1.2.trans (le_normalizer_residual H))
    (linear_residual_graph_action T hTM hH hlinear)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
