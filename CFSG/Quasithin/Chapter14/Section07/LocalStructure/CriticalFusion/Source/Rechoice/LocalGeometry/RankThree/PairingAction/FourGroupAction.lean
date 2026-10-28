module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.RankThree.PairingAction
public import CFSG.Quasithin.ChapterA.Section01.Elementary

/-!
# The full four-group action in the rank-three branch of 14.7.70

The two literal core commutators identify the hypotheses of A.1.14 on
E = V₁ Zα. Its proved action and normal-closure clauses supply the full
automorphism action of Y_E and its normality inside N_G(E). All point-core
identifications are transported from the actual vertex centralizers.

The earlier 14.5.21 commutator equality and the marked reciprocal actor
remain explicit, as in `PairingAction`. The restricted action on the larger
commutator space and the two-residual span remain separate source steps.

Source: Aschbacher–Smith, combined manuscript, 1 March 2004,
A.1.14 and 14.7.70, printed pp.23 and 1074.
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.RankThree
open Subgroup Representation Chapter12.Section08
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  {d : Data T L V F W} {c : CriticalPath (L := L) F}

namespace Preliminary
variable (h : Preliminary d c)
include h

/-- The source hypotheses of A.1.14 hold for the actual two vertex cores. -/
theorem E_source_core_pair (s : d.ActionDescent)
    (h21 : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1)
    (a : F.H) (ha : (a : G) ∈ conjugate F.U c.conjugator⁻¹)
    (t : SL2FourNatural.F) (ht : t ≠ 0)
    (hmark : d.qH a = alternatingActor d.naturalQuotient (SL2FourNatural.upper t)) :
    ∃ v₁ v₂ : G, FourGroupCorePair (E c) v₁ v₂ ∧
      FourGroupCorePair.core v₁ = F.H.pCoreIn 2 ∧
      FourGroupCorePair.core v₂ = c.Qα ∧
      FourGroupCorePair.generated v₁ v₂ = YE c := by
  obtain ⟨v₁, hv₁, v₂, hv₂, ho₁, ho₂, hne, hp₁, hp₂, hC₁, hC₂⟩ :=
    h.E_source_involutions
  have hc₁ : FourGroupCorePair.core v₁ = F.H.pCoreIn 2 :=
    congrArg (pCoreIn 2) hC₁
  have hc₂ : FourGroupCorePair.core v₂ = c.Qα := hC₂
  obtain ⟨hcomm₁, hcomm₂⟩ := h.E_core_commutators s h21 a ha t ht hmark
  refine ⟨v₁, v₂, ?_, hc₁, hc₂, ?_⟩
  · exact ⟨h.E_isKleinFour, hv₁, hv₂, ho₁, ho₂, hne,
      by rw [hc₁, hcomm₁, hp₁], by rw [hc₂, hcomm₂, hp₂]⟩
  · change FourGroupCorePair.core v₁ ⊔ FourGroupCorePair.core v₂ =
      F.H.pCoreIn 2 ⊔ c.Qα
    rw [hc₁, hc₂]

/-- A.1.14 discharges the full E-action and relative-normality steps of
14.7.70, using the consumer's existing normalizer inclusion literally. -/
theorem YE_full_action_and_normality (s : d.ActionDescent)
    (h21 : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1)
    (a : F.H) (ha : (a : G) ∈ conjugate F.U c.conjugator⁻¹)
    (t : SL2FourNatural.F) (ht : t ≠ 0)
    (hmark : d.qH a = alternatingActor d.naturalQuotient (SL2FourNatural.upper t)) :
    Function.Surjective ((E c).normalizerMonoidHom.comp
      (inclusion (h.YE_normalizes h21.le))) ∧
    ((YE c).subgroupOf (normalizer (E c : Set G))).Normal ∧
    normalizer (E c : Set G) = YE c ⊔ centralizer (E c : Set G) := by
  obtain ⟨v₁, v₂, hp, _, _, hgen⟩ := h.E_source_core_pair s h21 a ha t ht hmark
  refine ⟨?_, ?_, ?_⟩
  · intro f
    obtain ⟨y, hy⟩ := ChapterA.lemma_A_1_14_action hp f
    exact ⟨⟨y, hgen ▸ y.property⟩, hy⟩
  · simpa only [hgen] using (ChapterA.lemma_A_1_14_2 hp).2
  · simpa only [hgen] using ChapterA.lemma_A_1_14_normalizer hp

end Preliminary
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.RankThree
