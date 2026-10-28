module
public import CFSG.Quasithin.Chapter10.SourceA5ComponentNormalizer.ConditionalInput
public import CFSG.Quasithin.Chapter10.SourceNonnormalPairAction
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.NonquasisimpleFitting
public import Theory.GroupTheory.CComponent.FittingNormalizerQuotient
/-!
# The quasisimple quotient in the original component normalizer

The original maximal local group permutes the two conjugate factors. Its
intersection with the normalizer of the first therefore normalizes the
opposite factor as well. For a normal C-component containing that opposite
factor and satisfying F* = O₂, a nonquasisimple quotient would force its
Fitting preimage into this intersection by C.2.6. The Fitting-normalizer
quotient theorem then gives a contradiction. This supplies the quasisimple
field of the actual C.2.7 input, preserving the original normalizer and
R = O₂(L₀T).

Source: Aschbacher–Smith, Lemma 10.2.6, printed pp.748–749; C.2.6–7,
printed pp.145–146.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter1
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
include D

/-- The stabilizer of the first member of the original pair fixes the second. -/
theorem source_nonnormal_component_normalizer_fixes_opposite
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G)) :
    normalizer (L : Set G) ⊓ D.maximalLocal ≤
      normalizer (L.map (MulAut.conj t).toMonoidHom : Set G) := by
  intro m hm
  apply mem_normalizer_iff_map_conj_eq.mpr
  have htM : t ∈ D.maximalLocal := le_normalizer_componentOrbit L T ht
  have hmL := mem_normalizer_iff_map_conj_eq.mp hm.1
  have hcomp : (MulAut.conj (m * t)).toMonoidHom =
      (MulAut.conj m).toMonoidHom.comp (MulAut.conj t).toMonoidHom := by
    ext x
    change (m * t) * x * (m * t)⁻¹ = m * (t * x * t⁻¹) * m⁻¹
    group
  have hp := source_nonnormal_maximal_pair D hn ht htn (m * t)
    (D.maximalLocal.mul_mem hm.2 htM)
  rw [hcomp, ← map_map] at hp
  rcases hp with hp | hp
  · exact (htn (mem_normalizer_iff_map_conj_eq.mpr
      ((map_injective (MulAut.conj m).injective) (hp.trans hmL.symm)))).elim
  · exact hp

/-- The characteristic-two branch of the original normalizer enlargement has
quasisimple quotient modulo its two-core. -/
theorem source_nonnormal_normalizer_component_quotient_quasisimple
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    {I : Subgroup G} (hI : I ∈ cComponentsIn (normalizer (L : Set G)))
    (hIN : (I.subgroupOf (normalizer (L : Set G))).Normal)
    (hf : generalizedFitting I = pCore 2 I)
    (hBI : L.map (MulAut.conj t).toMonoidHom ≤ I) :
    IsQuasisimple (I ⧸ pCore 2 I) := by
  classical
  by_contra hnq
  have hF := ChapterC.Section02Source.fittingCore_le_of_nonquasisimple_component_setup
    (source_nonnormal_component_normalizer_pushing_setup D hn) hI hf
    ((normal_subgroupOf_iff_le_normalizer hI.1).mp hIN) hnq
  let B := L.map (MulAut.conj t).toMonoidHom
  let B₀ := B.subgroupOf I
  let e : L ≃* B₀ := ((MulAut.conj t).subgroupMap L).trans
    (subgroupOfEquivOfLe hBI).symm
  have htop : (⊤ : Subgroup I).IsCComponent := by
    simpa only [subgroupOf_self] using hI.2.subgroupOf_of_le le_rfl hI.1
  have hB : IsQuasisimple (B₀ ⧸ pCore 2 B₀) := by
    let := D.quasisimple
    exact IsQuasisimple.of_mulEquiv
      (QuotientGroup.congr (pCore 2 L) (pCore 2 B₀) e (pCore_map_iso 2 e))
  have hFn : twoFittingCore I ≤ normalizer (B₀ : Set I) := by
    rw [← subgroupOf_normalizer_eq hBI]
    intro x hx
    exact source_nonnormal_component_normalizer_fixes_opposite D hn ht htn
      (hF (mem_map_of_mem I.subtype hx))
  exact hnq (quasisimple_quotient_of_fitting_normalizes htop B₀ hB hFn)

/-- The original strict enlargement supplies the full C.2.7 input in its
characteristic-two branch; no separate quotient assumption is needed. -/
theorem source_nonnormal_constrained_component_c27_input
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    {K : Subgroup G} (hK : K ∈ cComponentsIn (normalizer (L : Set G)))
    (hKN : (K.subgroupOf (normalizer (L : Set G))).Normal)
    (hBK : L.map (MulAut.conj t).toMonoidHom < K)
    (hF : generalizedFitting K = pCore 2 K) :
    Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.Input
      KnownSimple.IsKnownSimple (normalizer (L : Set G))
      ((localJoin T L).pCoreIn 2) (normalizer (L : Set G) ⊓ D.maximalLocal) K :=
  source_nonnormal_component_c27_input D hn ht hK hKN hBK
    (source_nonnormal_normalizer_component_quotient_quasisimple D hn ht htn hK hKN hF hBK.le) hF
end CFSG.Quasithin.Chapter10
