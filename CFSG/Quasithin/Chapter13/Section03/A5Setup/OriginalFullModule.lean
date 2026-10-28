module
public import CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalMaximality
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.OrbitSetup
public import CFSG.Quasithin.Chapter10.SourceA5FullModule

/-!
# The actual full module at the original A₅ normalization input

The literal Hypothesis13.3.1 constructs its Fundamental Setup. In the
nonnormal A₅ case, an escaping Baumann normalizer forces the local module
to equal its full M-orbit and gives its ambient normalizer exactly M.
This is the original-module input for both remaining branches of10.2.1.
Source: Aschbacher–Smith,10.2.1 and13.3.2(2),pp.742–743,884–885.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalMaximality
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

theorem exists_original_full_module
    (h : Chapter14.Section03.FaithfulSource.Hypothesis1331 T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤
      normalizer (localOrbit T L : Set G)) :
    ∃ D : FundamentalSetup KnownSimple.IsKnownSimple T L,
      D.fullModule = D.moduleSubgroup ∧
      normalizer (D.moduleSubgroup : Set G) = normalizer (localOrbit T L : Set G) := by
  obtain ⟨D⟩ := (hypothesis1221 h e).exists_original_fundamentalSetup
  exact ⟨D,Chapter10.source_a5_exception_fullModule_eq D e hn hout,
    Chapter10.source_a5_exception_module_normalizer D e hn hout⟩
end CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalMaximality
