module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.SourceGeometry
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.ExceptionalActors.Catalogue.Applications
public import Theory.GroupTheory.PCoreSurjective.OddExtension

/-!
# The full exceptional-A₇ source actor

The genuine short-block source line defines a two-dimensional subspace of
the actual four-dimensional exceptional module. The specified quotient map
carries the Sylow intersection and the residual Lᵥ into its stabilizer.
Its kernel on Lᵥ is a two-group, so quotienting both groups by their two-cores
preserves the original cubic residual quotient. In particular the actor can
be noncyclic, as required by the source's three permitted actors.

These data construct `PermittedActor`; the proved catalogue gives zero common
fixed space on the whole module. The checked short-block endgame then
centralizes the exact marked conjugate from the local configuration. No
seed-in-K condition, core-intersection equality, actor marking or B.2.14
splitting is assumed.

Source: Aschbacher–Smith, 13.6.22, printed pp.932–933. The underlying binary
four-space and actor catalogue use the actual alternating-seven carrier.
-/

public section
open Subgroup Representation
open CFSG.Quasithin.ChapterC
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.A5Module
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination
open SourceSmallModels SourceSmallModels.BinaryRankTwo
open SourceSmallModels.AlternatingBranches
open SourceSmallModels.AlternatingBranches.ExceptionalActors

namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels
variable {G : Type*} [Group G] [Finite G] {K L V T : Subgroup G}

/-- The original source line constructs a permitted full residual actor. Its
actual two-group kernel preserves the cubic quotient, allowing noncyclic actors. -/
theorem exceptionalSeven_centralizer_eq_of_sourceLine (s : Marking L V)
    (d : SourceLineData L K V T (markedV s)) (h : IsExceptionalA7Block K)
    (hcard : Nat.card (Lv L (markedV s) ⧸ pCore 2 (Lv L (markedV s))) = 3) :
    (blockU K).map K.subtype ⊓ centralizer (Lv L (markedV s) : Set G) =
      (blockU K).map K.subtype ⊓ centralizer (K : Set G) := by
  let := h.1.module_elementary
  let : CommGroup (BlockModule K) := IsMulCommutative.instCommGroup
  obtain ⟨e⟩ := h.2.1
  obtain ⟨ρ, hρ, hdim, m, hm⟩ := exceptionalSeven_quotientModel K h e
  have hlU : ⁅V, Lv L (markedV s)⁆ ≤ (blockU K).map K.subtype := by
    rw [← show sourceU K = (blockU K).map K.subtype from sourceU_eq K h.1]
    exact d.line_le
  have hf : Function.Surjective m.actor := by
    rw [hm]
    exact e.surjective.comp (QuotientGroup.mk'_surjective _)
  obtain ⟨P, hP⟩ := SourceActors.exists_source_sylow d.normalizes_K d.sylow d.sylow_eq
  let S : Sylow 2 A7 := P.mapSurjective hf
  have hS : (S : Subgroup A7) = (T.subgroupOf K).map m.actor :=
    SourceActors.sylow_image m.actor hf P hP
  let Q := quotientPlane s m hlU
  let D := actorImage s m d.lv_le
  have hD : D = ((Lv L (markedV s)).subgroupOf K).map m.actor :=
    actor_image_eq_map s m d.lv_le
  have hk : m.actor.ker = pCore 2 K := by
    rw [hm, ← MonoidHom.comap_ker,
      (MonoidHom.ker_eq_bot_iff e.toMonoidHom).mpr e.injective]
    ext k
    change QuotientGroup.mk' (pCore 2 K) k = 1 ↔ k ∈ pCore 2 K
    exact QuotientGroup.eq_one_iff k
  let f := m.actor.comp (inclusion d.lv_le)
  let q : Lv L (markedV s) →* D := f.rangeRestrict
  have hq : Function.Surjective q := f.rangeRestrict_surjective
  have hqker : IsPGroup 2 q.ker := by
    change IsPGroup 2 f.rangeRestrict.ker
    rw [MonoidHom.ker_rangeRestrict]
    change IsPGroup 2 (m.actor.comp (inclusion d.lv_le)).ker
    rw [← MonoidHom.comap_ker, hk]
    exact pCore_isPGroup.comap_of_injective (inclusion d.lv_le) (inclusion_injective d.lv_le)
  have hquot : Nat.card (D ⧸ pCore 2 D) = 3 :=
    (Nat.card_congr (q.quotientPCoreEquivOfSurjective hq hqker).toEquiv).symm.trans hcard
  have hp : PermittedActor ρ Q S D := by
    refine ⟨?_, ?_, ?_, actorImage_twoPerfect s m d.lv_le, hquot,
      quotientPlane_commutator s m hlU d.lv_le⟩
    · rw [hS]
      apply BinaryOffender.le_subspaceStabilizer
      rintro a ⟨k, hk, rfl⟩ w hw
      exact quotientPlane_invariant_of_normalizes s m hlU k
        (d.line_invariant ((show T ≤ Lv L (markedV s) ⊔ T from le_sup_right) hk)) hw
    · apply BinaryOffender.le_subspaceStabilizer
      rintro a ⟨l, rfl⟩ w hw
      exact quotientPlane_invariant s m hlU d.lv_le l hw
    · rw [hS, hD]
      exact SourceActors.image_normalizes m.actor d.normalizes_Lv
  exact centralizer_eq_of_permittedActor s ρ hρ hdim m d.lv_le hlU S hp

section LocalConfiguration
variable {S : Sylow 2 G} {M V₁ V₂ : Subgroup G}

/-- The exceptional-A₇ calculation centralizes the same earlier marked conjugate,
with all line, actor and supplement data constructed on the local configuration. -/
theorem exceptionalSeven_centralizes_markedA_of_localConfiguration
    (d : FlagSource S L V V₁ V₂) (c : LocalConfiguration M d.flag)
    (h : IsExceptionalA7Block K)
    (hK : K ∈ ComponentSelection.Yz L (S : Subgroup G)
      (markedZ d.flag.module) (markedV d.flag.module))
    (hn : Tv (S : Subgroup G) (markedV d.flag.module) ≤ normalizer (K : Set G))
    (hLK : Lv L (markedV d.flag.module) ≤ K)
    (hchar : Theory.GroupTheory.generalizedFitting (Gv (markedV d.flag.module)) =
      pCore 2 (Gv (markedV d.flag.module)))
    (hSL : (S : Subgroup G) ≤ normalizer (L : Set G)) :
    K ≤ Gv (markedA d.flag.module) := by
  obtain ⟨e⟩ := sourceLineData_of_localConfiguration d c h.1 hK hn hLK hchar hSL
  exact short_centralizes_markedA d c h.1 hK hn hLK hchar hSL
    (exceptionalSeven_centralizer_eq_of_sourceLine d.flag.module e h c.residual_card)

end LocalConfiguration

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels
