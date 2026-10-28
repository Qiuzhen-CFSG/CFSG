module

public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.BaumannFixed.CampbellAutomorphisms.TheoremA.Noncontainment
public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.BaumannFixed.CampbellAutomorphisms.TheoremA.SourceActors

/-!
# The original actors for Campbell II.7.5

The original local-class and Baumann hypotheses construct the common
maximal subgroup, the moving maximum elementary subgroup, and an outside
involution of J(H). The noncontainment theorem applies to these exact
actors and the original automorphism. This is the source input to II.7.6;
no replacement or noncontainment property is assumed.
Source: Campbell, Pushing up in Finite Groups, II.7, printed pp.33–35.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.ChapterC.GlaubermanNiles
open CampbellTheoremA
variable {H : Type*} [Group H] [Finite H] (S : Subgroup H)

theorem InLocalClass.exists_theoremA_noncontained_actors
    (h : InLocalClass S.subtype) (hB : IsBaumannFixed S) (a : MulAut S)
    (hAll : ∀ b : MulAut S, automorphismImage S b (Campbell.V H) ≤ pCore 2 H)
    (hn : ¬ ⁅Campbell.J (⊤ : Subgroup H),imageF S a⁆ ≤ Campbell.F H) :
    ∃ (M A : Subgroup H) (g : H), S ≤ M ∧ M ⋖ ⊤ ∧
      normalizer (fixed S : Set H) ≤ M ∧
      A ∈ elementaryAbelianMaxSubgroups S ∧ ¬A ≤ pCore 2 H ∧
      g ∈ Campbell.J (⊤ : Subgroup H) ∧ g^2=1 ∧ g ∉ M ∧
      firstReplacement S a A ∈ elementaryAbelianMaxSubgroups S ∧
      firstReplacement S a A ≤ pCore 2 H ∧
      replacement S a A g ∈ elementaryAbelianMaxSubgroups S ∧
      replacement S a A g ≤ pCore 2 H ∧
      ¬ mixedActor S a g ≤ replacement S a A g := by
  obtain ⟨M,A,g,hSM,hMt,hNZ,hA,hAQ,hgK,hg2,hgM⟩ := h.exists_theoremA_actors S hB
  have hp := h.firstReplacement_geometry S hB a (hAll a) A hA
  have hb := h.replacement_geometry S hB a hAll A hA g
  exact ⟨M,A,g,hSM,hMt,hNZ,hA,hAQ,hgK,hg2,hgM,hp.1,hp.2.1,hb.1,hb.2.1,
    h.mixedActor_not_le_replacement S hB a hAll hn A hA hAQ M ⟨hSM,hMt⟩ hNZ g hgK hg2 hgM⟩
end CFSG.Quasithin.ChapterC.GlaubermanNiles
