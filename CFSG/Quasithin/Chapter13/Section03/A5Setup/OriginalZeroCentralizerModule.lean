module
public import CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalMaximality
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.OrbitSetup
public import CFSG.Quasithin.Chapter10.SourceA5ZeroCentralizerModule

/-!
# Original module equality in the A₅ zero-centralizer branch

Under the literal Hypothesis 13.3.1, construct the original Fundamental
Setup and identify its local and full modules with the common two-core
when the Baumann normalizer escapes and C_Z(L₀)=1. The local module's
ambient normalizer is the original M=N_G(L₀). These are the actual module
identities needed for the next dihedral-factor normalizer argument.
Source: Aschbacher–Smith, 10.2.1 and13.3.2(2), pp.742–743,884–885.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalMaximality
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

theorem exists_original_zero_centralizer_module
    (h : Chapter14.Section03.FaithfulSource.Hypothesis1331 T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤
      normalizer (localOrbit T L : Set G))
    (hz : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G) = ⊥) :
    ∃ D : FundamentalSetup KnownSimple.IsKnownSimple T L,
      D.moduleSubgroup = (localJoin T L).pCoreIn 2 ∧
      D.fullModule = D.moduleSubgroup ∧
      D.moduleSubgroup = (normalizer (localOrbit T L : Set G)).pCoreIn 2 ∧
      normalizer (D.moduleSubgroup : Set G) = normalizer (localOrbit T L : Set G) := by
  obtain ⟨D⟩ := (hypothesis1221 h e).exists_original_fundamentalSetup
  have hV := Chapter10.source_a5_zero_centralizer_module_eq_core D e hn hout hz
  refine ⟨D,hV,Chapter10.source_a5_zero_centralizer_fullModule_eq D e hn hout hz,?_,
    Chapter10.source_a5_zero_centralizer_module_normalizer D e hn hout hz⟩
  exact hV.trans (Chapter10.source_a5_zero_centralizer_core_eq D e hn hout hz).2.symm
end CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalMaximality
