module
public import CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalMaximality
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.OrbitSetup
public import CFSG.Quasithin.Chapter10.SourceA5ZeroBaumannProduct

/-!
# The original zero-center Baumann subgroup is a product of four dihedral groups

The original 13.3.1 hypotheses construct the fundamental setup. In the
zero-center branch with an escaping Baumann normalizer, the two original
centralizer factors commute, generate the Baumann subgroup and intersect
trivially. Their dihedral-square identifications give four D₈ factors for the
literal ambient Baumann subgroup. The subsequent normalizer argument must
still retain the action on those factors and the original module.

Source: Aschbacher–Smith, 10.2.1 and 13.3.2(2), printed pp.743,884–885.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalMaximality
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

theorem zero_original_baumann_dihedral_four_product
    (h : Chapter14.Section03.FaithfulSource.Hypothesis1331 T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤
      normalizer (localOrbit T L : Set G))
    (hz : omegaOneCenterAmbient (T : Subgroup G) ⊓
      centralizer (localOrbit T L : Set G) = ⊥) :
    Nonempty (ChapterB.baumann (T : Subgroup G) ≃*
      (DihedralGroup 4 × DihedralGroup 4) × (DihedralGroup 4 × DihedralGroup 4)) := by
  obtain ⟨D⟩ := (hypothesis1221 h e).exists_original_fundamentalSetup
  exact Chapter10.source_a5_zero_original_baumann_dihedral_four_product D e hn hout hz

end CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalMaximality
