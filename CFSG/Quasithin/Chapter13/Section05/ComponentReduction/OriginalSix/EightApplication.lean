module
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.OriginalSix.ParabolicApplication
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.MarkedModule.AlternatingParabolics.EightMarking

/-!
# The original A₈ application

The source involution and Sylow marking determine the actual pair
stabilizer. The natural central-quotient action then generates the whole
original tilde module by L₁, discharging the remaining hypothesis of13.5.14.
Source: Aschbacher–Smith13.5.21(6), printed p.924.
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

theorem alternating_eight_source_generation
    (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
    (hU : ¬IsMulCommutative D.UH)
    (h1221 : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple D.T D.L)
    (hc : centralizer (D.Vplus:Set G)≤M⊓normalizer (D.V:Set G))
    (K : Subgroup G) (s : Selected D K) (hLK : D.L₁≤K)
    (f : Catalogue.actor D K≃*alternatingGroup (Fin 8))
    (fV : CentralQuotient.Space D h K≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 8))
    (hfV : ∀b:Catalogue.actor D K,∀u,
      centralProjection D h fV (Action.starRepresentation D h b.val u)=
        BinaryPermutation.alternatingNaturalRepresentation (Fin 8) (f b)
          (centralProjection D h fV u)) :
    D.tilde D.UH=⁅D.tilde D.UH,D.tilde D.L₁⁆ := by
  have hSQ := (Chapter1.Section02.uniqueness_local_quotient_sqtk
    d.counterexample.qtke (selected_H_mem h)).stronglyQuasithin
  exact alternating_eight_tilde_generation D h s d.counterexample.qtke.properK hSQ hLK
    (source_local_component_commutator d h e h1221 hc K s)
    (NormalBranch.SourceOrthogonal.seed_index d) hU (seed_identity d h) f fV hfV

end CFSG.Quasithin.Chapter13.Section05.ComponentReduction.OriginalSix
