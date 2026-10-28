module
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne.OriginalComparison
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.Terminal
public import Theory.GroupTheory.ConjugateSpanNormalizer

/-!
# Mutual quadratic action in the full-denominator branch

The opposite module centralizes U_H and normalizes L, hence normalizes
the entire L-span. Once the span is abelian, it centralizes the endpoint
line A₁ and therefore lies in the endpoint group normalizing Uγ. Both
iterated commutators vanish because their first commutator lies in the
intersection of these two abelian groups.

The source application obtains abelianness from the original local planes
using OriginalComparison, which constructs all parabolic markings. No
normalization or quadratic premise is added. The remaining local-plane
construction, small-displacement estimate, permutation comparison and
13.4.1 application remain with qt-d-138-a6-endgame-source; the earlier
ordinary setup remains with qt-d-138-six-g2-source.
Source: Aschbacher--Smith, proof of 13.8.33, printed p.967.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne
open TransvectionRecognition.Component.ModelExtension A6Endgame.IntersectionBalance
open TransvectionQuotients TransvectionQuotients.FourLocalFactors
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H L₂ : Subgroup G}
  [IsElementaryAbelian 2 (Source.UH H V₃)]

/-- The actual abelian L-span and opposite module normalize each other
and have both iterated commutators trivial. -/
theorem full_denominators_span_quadratic
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (h : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (c : CriticalGeometry.CriticalPair L (T : Subgroup G) H V) (hH : H = G₁)
    (hDH : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) = Source.UH H V₃)
    (hDg : Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ = c.Ugamma V₃)
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (hab : IsMulCommutative (Source.UL L H V₃)) :
    Source.UL L H V₃ ≤ normalizer (c.Ugamma V₃ : Set G) ∧
      c.Ugamma V₃ ≤ normalizer (Source.UL L H V₃ : Set G) ∧
      ⁅Source.UL L H V₃, c.Ugamma V₃⁆ ≤ Source.UL L H V₃ ⊓ c.Ugamma V₃ ∧
      ⁅⁅Source.UL L H V₃, c.Ugamma V₃⁆, c.Ugamma V₃⁆ = ⊥ ∧
      ⁅⁅Source.UL L H V₃, c.Ugamma V₃⁆, Source.UL L H V₃⁆ = ⊥ := by
  let := hab
  let : IsElementaryAbelian 2 (c.Ugamma V₃) := IsElementaryAbelian.map _
  have hc := (ComponentSieve.SixAndG2.Overgroup.full_denominators_commutator d h c hDH hDg).1
  have hUgC : c.Ugamma V₃ ≤ centralizer (Source.UH H V₃ : Set G) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    rwa [commutator_comm]
  have hUgM : c.Ugamma V₃ ≤ M :=
    ((hUgC.trans (centralizer_le (le_conjugateSpanBy V₃ H))).trans hcentral).trans inf_le_left
  have hUgN : c.Ugamma V₃ ≤ normalizer (Source.UL L H V₃ : Set G) := by
    apply normalizes_conjugateSpanBy (Source.UH H V₃) L (c.Ugamma V₃)
      (hUgC.trans (Subgroup.centralizer_le_normalizer _))
    rwa [← d.local_normalizer]
  have hA : c.Aone V₁ ≤ Source.UL L H V₃ :=
    (endpoint_commutator d h c hDH hDg hcentral).2.trans (le_conjugateSpanBy _ _)
  have hULC : Source.UL L H V₃ ≤ centralizer (c.Aone V₁ : Set G) :=
    (le_centralizer _).trans (centralizer_le hA)
  have hULN : Source.UL L H V₃ ≤ normalizer (c.Ugamma V₃ : Set G) := by
    apply le_trans (hULC.trans (Subgroup.centralizer_le_normalizer _))
    rw [← Terminal.endpoint_eq_line_normalizer d c hH]
    exact c.normalizes_Ugamma V₃
  have hb : ⁅Source.UL L H V₃, c.Ugamma V₃⁆ ≤ Source.UL L H V₃ ⊓ c.Ugamma V₃ :=
    le_inf (le_normalizer_iff_commutator_le_left.mp hUgN)
      (le_normalizer_iff_commutator_le_right.mp hULN)
  exact ⟨hULN,hUgN,hb,
    commutator_eq_bot_iff_le_centralizer.mpr ((hb.trans inf_le_right).trans (le_centralizer _)),
    commutator_eq_bot_iff_le_centralizer.mpr ((hb.trans inf_le_left).trans (le_centralizer _))⟩

/-- The original local planes supply both abelianness and mutual quadratic
action on the unchanged source groups. -/
theorem span_quadratic_of_original_planes
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (h : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (c : CriticalGeometry.CriticalPair L (T : Subgroup G) H V) (hH : H = G₁)
    (hDH : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) = Source.UH H V₃)
    (hDg : Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ = c.Ugamma V₃)
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (a : SolvableExclusion.Five.StarAction H (Source.UH H V₃) V₁)
    (e : Source.Hstar H ≃* Equiv.Perm (Fin 6))
    (model : CompatibleModel H V₃ V₁ a e)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (s : SectionStructure.Data L H (T : Subgroup G) (sourceOne L T V₁) L₂ V V₂ V₃)
    (e₁ : (((((sourceOne L T V₁) ⊔ (T : Subgroup G)).subgroupOf (L ⊔ (T : Subgroup G))).map
      (barMap (L ⊔ (T : Subgroup G)) V s.normalizes_V).rangeRestrict) ⧸
      pCore 2 ((((sourceOne L T V₁) ⊔ (T : Subgroup G)).subgroupOf (L ⊔ (T : Subgroup G))).map
      (barMap (L ⊔ (T : Subgroup G)) V s.normalizes_V).rangeRestrict)) ≃* Equiv.Perm (Fin 3))
    (e₂ : ((((L₂ ⊔ (T : Subgroup G)).subgroupOf (L ⊔ (T : Subgroup G))).map
      (barMap (L ⊔ (T : Subgroup G)) V s.normalizes_V).rangeRestrict) ⧸
      pCore 2 (((L₂ ⊔ (T : Subgroup G)).subgroupOf (L ⊔ (T : Subgroup G))).map
      (barMap (L ⊔ (T : Subgroup G)) V s.normalizes_V).rangeRestrict)) ≃* Equiv.Perm (Fin 3))

    (hp : SourceLocalPlanes s e₁ e₂)
    (hL₂ : L₂ = BarQuotients.sourceResidual L (T : Subgroup G) V₂) :
    IsMulCommutative (Source.UL L H V₃) ∧
      Source.UL L H V₃ ≤ normalizer (c.Ugamma V₃ : Set G) ∧
      c.Ugamma V₃ ≤ normalizer (Source.UL L H V₃ : Set G) ∧
      ⁅Source.UL L H V₃, c.Ugamma V₃⁆ ≤ Source.UL L H V₃ ⊓ c.Ugamma V₃ ∧
      ⁅⁅Source.UL L H V₃, c.Ugamma V₃⁆, c.Ugamma V₃⁆ = ⊥ ∧
      ⁅⁅Source.UL L H V₃, c.Ugamma V₃⁆, Source.UL L H V₃⁆ = ⊥ := by
  have hab := span_abelian_of_original_planes d h c hH hDH hDg hcentral a e model
    eL s e₁ e₂ hp hL₂
  exact ⟨hab,full_denominators_span_quadratic d h c hH hDH hDg hcentral hab⟩

end CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne
