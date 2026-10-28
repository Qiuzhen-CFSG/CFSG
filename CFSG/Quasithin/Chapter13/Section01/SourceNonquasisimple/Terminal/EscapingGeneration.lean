module

public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Terminal.Source
public import CFSG.Quasithin.ChapterE.Section01.ValuesSporadic.JankoTwo.FiveQuotients
public import CFSG.Quasithin.ChapterE.Section01.ValuesSporadic.Rudvalis.LocalGeneration
public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.SpecificGroups.Alternating.FiveTwoCoreExtension

/-!
# The escaping E₂-overgroup

The multiple-overgroup hypothesis first gives a minimal member of the actual
`HStar` family outside `N_G(L)`.  The source 13.1.6 alternatives are recorded
by `A5EscapeSource`: the solvable alternative is discharged by rank-one
E-generation, while the surviving normal component has its literal two-core
quotient identified with `A₅`. The join quotient is A₅ or S₅, and its actual
E-generation lifts through the ambient two-core. The source two-rank bound
is retained explicitly.

The original conditional HStar adapter remains available. The extension
`EscapingGeneration.Source` constructs `A5EscapeSource` at the actual join YT
from the proved 13.1.6 alternatives and applies the terminal contradiction.

Source: Aschbacher--Smith 13.1.6--13.1.7, printed pp.868--869, 875--876.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Terminal
open Chapter1 Chapter1.Section02 Chapter12.Section02 Chapter3
open ChapterE
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The non-solvable source branch for a minimal overgroup outside `M`.

`model` is the literal quotient of the component represented inside `H`; the
ambient quotient and its rank bound are separate source data.  This keeps the
component quotient map visible when the branch is transported to `H/O₂(H)`.
-/
structure A5EscapeSource (T : Sylow 2 G) (M H Y : Subgroup G) : Prop where
  component : Y ∈ cComponentsIn H
  normal : (Y.subgroupOf H).Normal
  outside : ¬ Y ≤ M
  model : Nonempty ((Y.subgroupOf H) ⧸ pCore 2 (Y.subgroupOf H) ≃*
    alternatingGroup (Fin 5))
  rank : primeRank 2 (H ⧸ pCore 2 H) ≤ 2

/-- Generation for the actual source join, using its literal core quotient. -/
theorem A5EscapeSource.isEGenerated_of_sup
    {T : Sylow 2 G} {M H Y : Subgroup G}
    (s : A5EscapeSource T M H Y) (hjoin : Y ⊔ (T : Subgroup G) = H) :
    IsEGenerated 2 H := by
  have hYH : Y ≤ H := s.component.1
  have hTH : (T : Subgroup G) ≤ H := hjoin ▸ le_sup_right
  have hTY : (T : Subgroup G) ≤ normalizer (Y : Set G) :=
    hTH.trans ((normal_subgroupOf_iff_le_normalizer hYH).mp s.normal)
  let e : Y.subgroupOf H ≃* Y := subgroupOfEquivOfLe hYH
  let eQ := QuotientGroup.congr _ _ e (pCore_map_iso 2 e)
  obtain ⟨a⟩ := s.model
  have hm := Theory.SpecificGroups.Alternating.FiveExtensionAction.core_quotient_of_two_supplement
    Y (T : Subgroup G) hTY T.isPGroup' (eQ.symm.trans a)
  rw [hjoin] at hm
  apply IsEGenerated.of_normal_two_subgroup (pCore 2 H) pCore_isPGroup
  rcases hm with hb | hb
  · obtain ⟨b⟩ := hb
    exact JankoTwo.alternating_five_isEGenerated.map_equiv b.symm
  · obtain ⟨b⟩ := hb
    exact JankoTwo.symmetric_five_isEGenerated.map_equiv b.symm

private theorem generation_of_a5_source
    {T : Sylow 2 G} {M H Y : Subgroup G}
    (hH : H ∈ HStar (T : Subgroup G) M)
    (s : A5EscapeSource T M H Y) : ChapterE.IsEGenerated 2 H := by
  have hTH : (T : Subgroup G) ≤ H := hH.1.1.2
  have hYH : Y ≤ H := s.component.1
  apply s.isEGenerated_of_sup
  apply le_antisymm (sup_le hYH hTH)
  by_contra hne
  have hlt : Y ⊔ (T : Subgroup G) < H := lt_of_le_not_ge (sup_le hYH hTH) hne
  have hYM : Y ⊔ (T : Subgroup G) ≤ M :=
    HStar.proper_overgroup_le T hH le_sup_right hlt
  exact s.outside (le_sup_left.trans hYM)

/-- The actual terminal escape construction from the 13.1.6 source output.

The first branch of `source` is the solvable alternative.  It is impossible
outside `M`, since every solvable overgroup containing `T` is E-generated at
one and the supplied terminal containment puts it in `M`.  The second branch
is the small quasisimple alternative, whose literal A₅ quotient gives the
required E₂ generation of the same escaping `H`.
-/
theorem exists_escaping_two_generated
    {T : Sylow 2 G} (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L))
    (hcontain : ∀ H : Subgroup G, (T : Subgroup G) ≤ H →
      ChapterE.IsEGenerated 1 H → H ≤ normalizer (L : Set G))
    (source : ∀ H : Subgroup G, H ∈ HStar (T : Subgroup G)
      (normalizer (L : Set G)) →
      Group.IsSolvable H ∨ ∃ Y : Subgroup G, A5EscapeSource T
        (normalizer (L : Set G)) H Y) :
    ∃ H : Subgroup G, (T : Subgroup G) ≤ H ∧
      ¬ H ≤ normalizer (L : Set G) ∧ ChapterE.IsEGenerated 2 H := by
  have hTL : (T : Subgroup G) ≤ normalizer (L : Set G) :=
    radicalLocal_invariant_source hL.1.1
      (uniqueness_local_quotient_sqtk h.simpleQTKE hL.1.1.2.2) hn
  obtain ⟨K,hK,hLK,_,_,hM,_⟩ := h.maximal_counterexample_of_many hmany
    (show L ∈ nonquasisimpleFaithful T from
      ⟨(Adequate.mem_faithfulLocalComponents_iff T L).mpr ⟨hL.1.1,hL.2⟩,hn⟩)
  have he : K = L := hL.1.2 K hK.1 hLK
  subst K
  obtain ⟨H, hH⟩ := Chapter3.exists_HStar_of_hasMaximalOutside
    (Chapter3.hasMaximalOutside_of_many T hmany (normalizer (L : Set G)) hM hTL)
  have hTH : (T : Subgroup G) ≤ H := hH.1.1.2
  have hHM : ¬ H ≤ normalizer (L : Set G) := hH.1.2
  rcases source H hH with hs | ⟨Y, s⟩
  · have hgen1 : ChapterE.IsEGenerated 1 H :=
      ChapterE.isEGenerated_one_of_solvable
    exact (hHM (hcontain H hTH hgen1)).elim
  · exact ⟨H, hTH, hHM, generation_of_a5_source hH s⟩

end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Terminal
