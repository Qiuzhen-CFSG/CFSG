module
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisCentralizersTwoSourceModels

/-!
# The natural A₅ seed in the literal omega span

The central weight-six vector is moved by the point residual. Irreducibility
of its marked four-dimensional action and 12.3.7 identify [Ω₁Z(T),K] with
[V,K]. Consequently [V,K] embeds in U=⟨Ω₁Z(T)^{C_G(e)}⟩ and in [U,K].
B.2.14 supplies the elementary structure and original Sylow containment of U.

The actual LocalAnalysis application retains only [U,K]≤[V,K]. Its B.5
proof remains with qt-d-1236-1238-point-centralizers; the final source
assembly is qt-d-1231-local-analysis. Source: Aschbacher–Smith 12.3.7–8,
printed pp.809–810, with B.2.14 and B.5.1,6.
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

/-- The original Sylow omega center already generates the whole moved A₅ space. -/
theorem five_omega_commutator
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T) :
    ⁅omegaCenterIn (T : Subgroup G),P.five⁆ = ⁅V,P.five⁆ := by
  have hle := S.omega_commutator_le_chosen_moved structural
    (PointCentralizers.source_1237 P structural escape).2.2.1 P.five
    ((pointResidual_le L (P.two : G)).trans inf_le_left)
  have hne : ⁅omegaCenterIn (T : Subgroup G),P.five⁆ ≠ ⊥ := by
    intro he
    apply P.five_moves_six structural escape
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

/-- The easy direction of the source B.5 equality retains the literal omega span. -/
theorem five_moved_le_omegaSpan_commutator
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T) :
    ⁅V,P.five⁆ ≤ ⁅P.twoOmegaSpan,P.five⁆ := by
  rw [←P.five_omega_commutator structural escape]
  exact commutator_mono (le_conjugateSpanBy _ _) le_rfl

/-- The remaining source module identity needs only the reverse containment. -/
theorem two_omegaSpan_commutator_eq_of_le
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T)
    (hle : ⁅P.twoOmegaSpan,P.five⁆ ≤ ⁅V,P.five⁆) :
    ⁅P.twoOmegaSpan,P.five⁆ = ⁅V,P.five⁆ :=
  le_antisymm hle (P.five_moved_le_omegaSpan_commutator structural escape)

/-- The orbit span is formed inside the actual point centralizer. -/
theorem twoOmegaSpan_le_pointCentralizer :
    P.twoOmegaSpan ≤ centralizer ({(P.two : G)} : Set G) := by
  apply conjugateSpanBy_le_self
  intro z hz
  exact mem_centralizer_singleton_iff.mpr
    (P.two_central z ((mem_omegaCenterIn_iff _ _).mp hz).1)

/-- Reducedness supplies the elementary structure on the literal ambient span. -/
theorem twoOmegaSpan_elementary : IsElementaryAbelian 2 P.twoOmegaSpan := by
  have hr := P.twoOmegaSpan_reduced
  let := hr.elementary
  exact IsElementaryAbelian.of_surjective
    (subgroupOfEquivOfLe P.twoOmegaSpan_le_pointCentralizer).toMonoidHom
    (subgroupOfEquivOfLe P.twoOmegaSpan_le_pointCentralizer).surjective

/-- The actual omega span lies in the original Sylow subgroup. -/
theorem twoOmegaSpan_le_sylow : P.twoOmegaSpan ≤ (T : Subgroup G) := by
  let H := centralizer ({(P.two : G)} : Set G)
  have hTH : (T : Subgroup G) ≤ H := fun t ht =>
    mem_centralizer_singleton_iff.mpr (P.two_central t ht)
  let R := T.subtype hTH
  intro x hx
  have hxH := P.twoOmegaSpan_le_pointCentralizer hx
  have hc := P.twoOmegaSpan_reduced.le_pCore
    (show (⟨x,hxH⟩ : H) ∈ P.twoOmegaSpan.subgroupOf H from hx)
  exact pCore_isPGroup.le_sylow_of_normal R hc

/-- The original natural A₅ module embeds in the source omega span. -/
theorem five_moved_le_omegaSpan
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T) : ⁅V,P.five⁆ ≤ P.twoOmegaSpan := by
  apply (P.five_moved_le_omegaSpan_commutator structural escape).trans
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

/-- The only remaining local obligation is the upper B.5 moved-space bound,
with the original module, omega span and point residual unchanged. -/
def localAnalysis_of_omegaSpan_commutator_le
    (P : SylowNormalizer.Points E)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (modules : Theorem1222Modules KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T)
    (natural : ∀ (A U : Subgroup G) (SA : Setup T A U), Nonempty SA.NaturalCoordinates)
    (hm : ⁅P.twoOmegaSpan,P.five⁆ ≤ ⁅V,P.five⁆) : S.LocalAnalysis :=
  localAnalysis_of_omegaSpan P structural modules escape natural
    (P.two_omegaSpan_commutator_eq_of_le structural escape hm)

end PointCentralizers
end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
