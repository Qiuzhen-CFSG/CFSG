module
public import CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalMaximality
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.OrbitSetup
public import CFSG.Quasithin.Chapter10.SourceA5ZeroCentralizerCore

/-!
# The original A₅ zero-centralizer core under Hypothesis 13.3.1

Construct the original Fundamental Setup and apply the C.1.13(c) pair
splitting to the actual Sylow conjugates of L. If the Baumann normalizer
escapes M and C_Ω₁(Z(T))(L₀)=1, the local, orbit and maximal-local cores
coincide and are elementary abelian. No coordinates, chosen normalized
module or full/local-module equality is assumed.

This discharges the core calculation of the zero-centralizer branch in
10.2.1 at the original 13.3.2 input. The later dihedral-factor and normalizer
arguments remain separate.
Source: Aschbacher–Smith,10.2.1 and13.3.2(2),pp.742–743,884–885.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalMaximality
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The literal original A₅ hypotheses give the elementary common core
needed before the zero-centralizer dihedral geometry. -/
theorem zero_centralizer_core_structure
    (h : Chapter14.Section03.FaithfulSource.Hypothesis1331 T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤
      normalizer (localOrbit T L : Set G))
    (hz : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G) = ⊥) :
    (localJoin T L).pCoreIn 2 = (localOrbit T L).pCoreIn 2 ∧
      (normalizer (localOrbit T L : Set G)).pCoreIn 2 = (localJoin T L).pCoreIn 2 ∧
      IsElementaryAbelian 2 ((localJoin T L).pCoreIn 2) := by
  obtain ⟨D⟩ := (hypothesis1221 h e).exists_original_fundamentalSetup
  have he := Chapter10.source_a5_zero_centralizer_core_eq D e hn hout hz
  exact ⟨he.1,he.2,Chapter10.source_a5_zero_centralizer_core_elementary D e hn hout hz⟩

end CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalMaximality
