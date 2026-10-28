module
public import CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalMaximality
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.OrbitSetup
public import CFSG.Quasithin.Chapter10.SourceA5ZeroCentralizerPairSections

/-!
# Actual symmetric-five sections for the original zero-center pair

The original Hypothesis13.3.1 Fundamental Setup gives exact natural-kernel
splittings for both centralizers of the paired blocks. These are sections
of the literal quotient-image maps, retained under the original Sylow
conjugation, with no supplied extension or involution-lift premise.
Source: Aschbacher–Smith10.2.1 and13.3.2(2), pp.742–743 and884–885.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalMaximality
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

theorem zero_centralizer_pair_sections
    (h : Chapter14.Section03.FaithfulSource.Hypothesis1331 T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤
      normalizer (localOrbit T L : Set G))
    (hz : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G) = ⊥) :
    ∃ D : FundamentalSetup KnownSimple.IsKnownSimple T L,
      ∃ t : localJoin T L, (t : G) ∈ (T : Subgroup G) ∧
        L.subgroupOf (localJoin T L) ≠
          (L.subgroupOf (localJoin T L)).map (MulAut.conj t).toMonoidHom ∧
        Chapter10.SourceOriginalPairedOpposite D t ∧
        Chapter10.OriginalCentralizerImageSection D (L.subgroupOf (localJoin T L)) ∧
        Chapter10.OriginalCentralizerImageSection D
          ((L.subgroupOf (localJoin T L)).map (MulAut.conj t).toMonoidHom) := by
  obtain ⟨D⟩ := (hypothesis1221 h e).exists_original_fundamentalSetup
  exact ⟨D,Chapter10.source_a5_zero_centralizer_pair_sections D e hn hout hz⟩

end CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalMaximality
