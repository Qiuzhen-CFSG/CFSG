module
public import CFSG.Quasithin.Chapter14.Section08.LieTypeBranch.OrdinarySixSeed
public import CFSG.Quasithin.Chapter13.Section07.OrdinarySource.F9Application
public import CFSG.Quasithin.Chapter13.Section07.L1ChiefCount
/-!
# The full-span branch at the actual maximal ordinary counterexample

The maximal choice supplies Hypothesis12.2.1. A nonabelian full V-span
places the point normalizer in the escaping family, and the original
plane noncentrality then constructs F.9, the abelian seed closure and
seed-core noncentrality. The actual paired conjugator gives the full
L₁ chief count on these unchanged groups and quotient maps.

The earlier13.3.14 plane noncentrality remains explicit; no equality
between the seed span and the full V-span is used.
Source: Aschbacher–Smith13.7.8 opening and13.7.10(8), printed pp.940–942.
-/
public section
open Subgroup Theory.GroupTheory NoncentralChiefRefinement
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section08.LieTypeBranch
open Chapter13.Section08.SourceCompletion
open Chapter13.Section07 ChapterF.Section09.Setup
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
include d
/-- The actual maximal ordinary counterexample supplies F.9 and the abelian
seed inputs. Only the earlier point-core/plane noncentrality is retained. -/
theorem original_six_full_span_inputs_of_plane_noncentral
    (hmax : Maximal (Counterexample T) L)
    (e : (L ⧸ pCore 2 L)≃*alternatingGroup (Fin 6))
    (hV : ¬IsMulCommutative (conjugateSpanBy V G₁))
    (hm : ⁅G₁.pCoreIn 2,V₂⁆≠⊥) :
    (ConjugateIntersections.sourceSetup T L V V₃ V₁ G₁).Hypothesis ∧
      IsMulCommutative (Chapter13.Section08.Source.UH G₁ V₃) ∧
      ⁅V₃,G₁.pCoreIn 2⁆≠⊥ := by
  let D := ConjugateIntersections.sourceSetup T L V V₃ V₁ G₁
  have heq : G₁=D.Gz := d.first_normalizer.trans
    (le_antisymm (normalizer_le_centralizer_of_card_two V₁ d.line_card)
      (Subgroup.centralizer_le_normalizer _))
  have d' : NaturalSetup D.T D.L D.V D.V₁ V₂ D.Vplus M D.Gz := heq ▸ d
  have h1221 := hypothesis1221_of_maximal_natural_six d' hmax e
  have hVGz : ¬IsMulCommutative (conjugateSpanBy D.V D.Gz) := heq ▸ hV
  have hH : D.H∈Chapter13.Section08.Source.Hz D.L₁ D.T D.Gz M := by
    rw [show D.H=D.Gz from heq]
    exact OrdinarySource.point_normalizer_mem_Hz_of_nonabelian_full d' h1221 hVGz
  have hm' : ⁅(normalizer (D.V₁:Set G)).pCoreIn 2,V₂⁆≠⊥ := by
    change ⁅(normalizer (V₁:Set G)).pCoreIn 2,V₂⁆≠⊥
    rwa [←d.first_normalizer]
  obtain ⟨h,hU,hne⟩ := OrdinarySource.inputs_of_plane_noncentral d' e h1221 hH hm'
  refine ⟨h,hU,?_⟩
  change ⁅V₃,D.Gz.pCoreIn 2⁆≠⊥ at hne
  exact heq.symm ▸ hne

/-- The full13.7.10(8) count on the original maximal counterexample,
with F.9 and the abelian seed closure supplied by their source proofs. -/
theorem original_six_full_span_chief_count
    (hmax : Maximal (Counterexample T) L)
    (e : (L ⧸ pCore 2 L)≃*alternatingGroup (Fin 6))
    (hV : ¬IsMulCommutative (conjugateSpanBy V G₁))
    (hm : ⁅G₁.pCoreIn 2,V₂⁆≠⊥) :
    ∃ g : L,
      (QuotientGroup.mk' (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G))
        (inclusion le_sup_left g))^2 = 1 ∧
      V ≤ V₃ ⊔ conjugate V₁ (g : G) ∧
      ¬ conjugate V₁ (g : G) ≤ Chapter13.Section08.Source.UH G₁ V₃ ∧
      ∀ s : ChiefSeries (ConjugateIntersections.sourceSetup T L V V₃ V₁ G₁).L₁,
        s.head = ⊥ → s.last = ⊤ →
        s.noncentralTwoCount = Nat.log 2 (Nat.card
          (((conjugate (Chapter13.Section08.Source.VH G₁ V) (g : G) ⊓
            (L ⊔ (T : Subgroup G) : Subgroup G).pCoreIn 2).subgroupOf G₁).map
              (QuotientGroup.mk' (pCore 2 G₁)))) + 2 := by
  obtain ⟨h,hU,_⟩ := original_six_full_span_inputs_of_plane_noncentral d hmax e hV hm
  exact exists_source_L1_chief_count d h hU hV
end CFSG.Quasithin.Chapter14.Section08.LieTypeBranch
