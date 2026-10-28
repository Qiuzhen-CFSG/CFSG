module
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.OriginalSix.ParabolicApplication
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.ChiefCount.SymmetricSixSource.Count
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.OriginalSix.CubicParity

/-!
# The original symmetric-six terminal contradiction

The same actual cubic subgroup and complete L₁ chief series have even
noncentral two-count by the original pair argument and count three by the
marked symmetric-six module. Their incompatible counts exclude this
natural actor case with all original source hypotheses retained.
Source: Aschbacher–Smith13.5.24, printed p.925.
-/
public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section05.ComponentReduction.OriginalSix
open Section08.SourceCompletion Section08.Source Recognition Recognition.Configuration
open Recognition.MarkedModule Recognition.MarkedModule.AlternatingParabolics
variable {G : Type*} [Group G] [Finite G] {D : ChapterF.Section09.Setup G}
  {V₂ M : Subgroup G}
  (d : NaturalSetup D.T D.L D.V D.V₁ V₂ D.Vplus M D.Gz) (h : D.Hypothesis)
  [(D.V₁.subgroupOf D.UH).Normal] [IsElementaryAbelian 2 (Action.ModuleGroup D)]

include d h

theorem symmetric_six_source_false
    (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
    (hU : ¬IsMulCommutative D.UH)
    (h1221 : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple D.T D.L)
    (hc : centralizer (D.Vplus:Set G)≤M⊓normalizer (D.V:Set G))
    (K : Subgroup G) (s : Selected D K) (hLK : D.L₁≤K)
    (f : Catalogue.actor D K≃*Equiv.Perm (Fin 6))
    (fV : CentralQuotient.Space D h K≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 6))
    (hfV : ∀b:Catalogue.actor D K,∀u,
      centralProjection D h fV (Action.starRepresentation D h b.val u)=
        BinaryPermutation.naturalRepresentation (Fin 6) (f b)
          (centralProjection D h fV u)) :
    False := by
  obtain ⟨A,hAL,hA⟩ := CubicParity.exists_cubic d h e
  obtain ⟨t,h0,h1⟩ := NoncentralChiefRefinement.exists_chiefSeries
    (⊥ : NoncentralChiefRefinement.NormalNode D.L₁) ⊤ bot_le
  have htilde := (symmetric_six_source_conclusions d h e hU h1221 hc K s hLK f fV hfV).2.2.2
  obtain ⟨r,hr⟩ := CubicParity.count_even d h e htilde hU A hAL hA t h0 h1
  have hthree := ChiefCount.SymmetricSixSource.source_count_three D h d e hU h1221 hc
    K s hLK f fV hfV A hAL hA t h0 h1
  omega

end CFSG.Quasithin.Chapter13.Section05.ComponentReduction.OriginalSix
