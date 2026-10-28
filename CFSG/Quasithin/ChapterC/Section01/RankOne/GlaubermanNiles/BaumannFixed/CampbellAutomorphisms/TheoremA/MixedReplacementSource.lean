module

public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.BaumannFixed.CampbellAutomorphisms.TheoremA.MixedReplacementTransport
public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.BaumannFixed.CampbellAutomorphisms.TheoremA.NoncontainmentSource

/-!
# The original mixed replacement configuration

The same maximal subgroup, maximum elementary subgroup, and outside
involution from II.7.3–5 satisfy the transported replacement and
commutator dichotomy of II.7.6. All actors are constructed from the
original local class and the chosen failure of Theorem A.
Source: Campbell, Pushing up in Finite Groups, II.7, printed pp.33–35.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.ChapterC.GlaubermanNiles
open CampbellTheoremA
variable {H : Type*} [Group H] [Finite H] (S : Subgroup H)

theorem InLocalClass.exists_theoremA_mixed_replacement
    (h : InLocalClass S.subtype) (hB : IsBaumannFixed S) (a : MulAut S)
    (hAll : ∀ b : MulAut S, automorphismImage S b (Campbell.V H) ≤ pCore 2 H)
    (hn : ¬ ⁅Campbell.J (⊤ : Subgroup H),imageF S a⁆ ≤ Campbell.F H) :
    ∃ (M A : Subgroup H) (g : H), S ≤ M ∧ M ⋖ ⊤ ∧
      normalizer (fixed S : Set H) ≤ M ∧
      A ∈ elementaryAbelianMaxSubgroups S ∧ ¬A ≤ pCore 2 H ∧
      g ∈ Campbell.J (⊤ : Subgroup H) ∧ g^2=1 ∧ g ∉ M ∧
      replacement S a A g ∈ elementaryAbelianMaxSubgroups S ∧
      replacement S a A g ≤ pCore 2 H ∧
      ¬ mixedActor S a g ≤ replacement S a A g ∧
      (mixedActor S a g ⊔ (replacement S a A g ⊓ centralizer (mixedActor S a g : Set H))) ∈
        elementaryAbelianMaxSubgroups S ∧
      mixedActor S a g ⊔ (replacement S a A g ⊓ centralizer (mixedActor S a g : Set H)) ≤ pCore 2 H ∧
      (⁅replacement S a A g,mixedActor S a g⁆=⊥ ∨
        ⁅replacement S a A g,mixedActor S a g⁆=(fixed S).map (MulAut.conj g).toMonoidHom) := by
  obtain ⟨M,A,g,hSM,hMt,hNZ,hA,hAQ,hgK,hg2,hgM,_,_,hb,hbQ,hy⟩ :=
    h.exists_theoremA_noncontained_actors S hB a hAll hn
  let : (Campbell.F H).Normal := Campbell.F_normal
  have hF : ¬imageF S a ≤ Campbell.F H := fun hf =>
    hn ((commutator_mono le_rfl hf).trans (commutator_le_right _ _))
  have ht := h.mixed_replacement_maximum_and_commutator S hB a hAll hF A hA g hgK hg2
  exact ⟨M,A,g,hSM,hMt,hNZ,hA,hAQ,hgK,hg2,hgM,hb,hbQ,hy,ht⟩
end CFSG.Quasithin.ChapterC.GlaubermanNiles
