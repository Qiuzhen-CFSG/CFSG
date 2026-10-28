module

public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisCentralizersTwoSourceOmegaSpan
public import CFSG.Quasithin.Chapter12.Section02.StructuralSource.At
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.LocalAnalysisCentralizersTwoSourceModels

/-!
# LocalAnalysisCentralizersTwoSourceOmegaSpan at the original ambient group and Sylow subgroup

These are the same source arguments as `LocalAnalysisCentralizersTwoSourceOmegaSpan`, with structural
12.2.2 and its module alternatives restricted to the original G,T. Every
chosen subgroup, central quotient, action and relative normality statement
is retained. Independent definitions and lemmas are imported unchanged.
The universal statements remain available from the original module.

Source: Aschbacher–Smith, 12.3.1–13, printed pp.807–812.
-/

@[expose] public noncomputable section

open Subgroup Theory.GroupTheory Representation

namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

open Section02 BinaryPermutation

universe u

variable {G : Type u} [Group G] [Finite G]

variable {T : Sylow 2 G} {L V : Subgroup G} {S : Setup T L V}

variable {E : S.NaturalCoordinates}

namespace SylowNormalizer.Points

variable (P : Points E)

theorem five_omega_commutator_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (escape : CentralizerEscape T) :
    ⁅omegaCenterIn (T : Subgroup G),P.five⁆ = ⁅V,P.five⁆ := by
  have hle := S.omega_commutator_le_chosen_moved_at structural
    (PointCentralizers.source_1237_at P structural escape).2.2.1 P.five
    ((pointResidual_le L (P.two : G)).trans inf_le_left)
  have hne : ⁅omegaCenterIn (T : Subgroup G),P.five⁆ ≠ ⊥ := by
    intro he
    apply P.five_moves_six_at structural escape
    have hc := le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp he)
    exact hc.trans (centralizer_le (Set.singleton_subset_iff.mpr P.six_mem_omega))
  let b : alternatingCoreRepresentation (Fin 5) ≃ₗ alternatingNaturalRepresentation (Fin 5) :=
    .mk (coreEquivNatural (Fin 5) (by decide)) (by
      intro g
      apply LinearMap.ext
      intro v
      exact coreEquivNatural_equivariant (Fin 5) (by decide) g.val v)
  let : (alternatingCoreRepresentation (Fin 5)).IsIrreducible :=
    b.irreducible_of_euqiv (alternatingNatural_isIrreducible (by decide))
  let f := P.fiveCoreEquiv.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 P.five))
  let : IsIrreducible ((alternatingCoreRepresentation (Fin 5)).comp f) :=
    (irreducible_comp_surjective_iff f
      (P.fiveCoreEquiv.surjective.comp (QuotientGroup.mk'_surjective _)) _).mpr inferInstance
  exact (P.five_moved_natural.eq_kernel_or_section _ bot_le hle
    (normalizer_commutator_ge_right _ _)).resolve_left hne

theorem five_moved_le_omegaSpan_commutator_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (escape : CentralizerEscape T) :
    ⁅V,P.five⁆ ≤ ⁅P.twoOmegaSpan,P.five⁆ := by
  rw [←P.five_omega_commutator_at structural escape]
  exact commutator_mono (le_conjugateSpanBy _ _) le_rfl

theorem two_omegaSpan_commutator_eq_of_le_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (escape : CentralizerEscape T)
    (hle : ⁅P.twoOmegaSpan,P.five⁆ ≤ ⁅V,P.five⁆) :
    ⁅P.twoOmegaSpan,P.five⁆ = ⁅V,P.five⁆ :=
  le_antisymm hle (P.five_moved_le_omegaSpan_commutator_at structural escape)

theorem five_moved_le_omegaSpan_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (escape : CentralizerEscape T) : ⁅V,P.five⁆ ≤ P.twoOmegaSpan := by
  apply (P.five_moved_le_omegaSpan_commutator_at structural escape).trans
  apply le_normalizer_iff_commutator_le_left.mp
  exact ((pointResidual_le L (P.two : G)).trans inf_le_right).trans
    (le_normalizer_conjugateSpanBy _ _)

end SylowNormalizer.Points

end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

open Section02

universe u

variable {G : Type u} [Group G] [Finite G]

variable {T : Sylow 2 G} {L V : Subgroup G} {S : Setup T L V}

variable {E : S.NaturalCoordinates}

namespace PointCentralizers

def localAnalysis_of_omegaSpan_commutator_le_at
    (P : SylowNormalizer.Points E)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (escape : CentralizerEscape T)
    (natural : ∀ (A U : Subgroup G) (SA : Setup T A U), Nonempty SA.NaturalCoordinates)
    (hm : ⁅P.twoOmegaSpan,P.five⁆ ≤ ⁅V,P.five⁆) : S.LocalAnalysis :=
  localAnalysis_of_omegaSpan_at P structural modules escape natural
    (P.two_omegaSpan_commutator_eq_of_le_at structural escape hm)

end PointCentralizers

end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

