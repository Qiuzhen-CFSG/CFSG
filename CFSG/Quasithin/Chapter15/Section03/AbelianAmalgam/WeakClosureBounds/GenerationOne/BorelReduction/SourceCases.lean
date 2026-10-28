module

public import CFSG.Quasithin.Defs
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.BorelReduction.SourceCases.Models
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.BorelReduction.SourceCases.Overlap
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.BorelReduction.Residual

/-!
# Reduction of the full E.2.2 alternatives when n(H) > 1

The input enumerates all six cases of E.2.2, including the odd-characteristic
model, congruence, centralizer and automizer clauses. Its common conclusions
retain the relative C-component, the quasisimple quotient K/O₂(K), component
generation, and the SQTK property of H/J. This is a conclusion interface for
the E.2.2 owner, not a proof of E.2.2 from the SQTK hypothesis.

The reduction excludes cases (1b), (2c), and (2d) by their exact value n(H)=1.
It retains (1a), (2a), and (2b), with field exponent f=n(H)>1. Minimality in
the actual outside family identifies the earlier unique maximal subgroup with
M ∩ H. The existing component-orbit argument then gives O²(H)=⟨K^T⟩ and
H=O²(H)T. Borel pairs, diagram actions, and the central kernel equality all
survive unchanged. Oddness and central-cover refinements belong to later work.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.2.2,
printed pp.215–216 (PDF pp.226–227), and 15.3.65, p.1152 (PDF p.1169).
-/

@[expose] public section
noncomputable section
universe u
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.BorelReduction.SourceCases
open Subgroup ChapterE
open scoped Pointwise
variable {G : Type u} [Group G]

/-- The common clauses of E.2.2(1). The source uses right conjugates K^t,
so `conjBy t⁻¹` is used. M means the local maximal subgroup M ∩ H. -/
structure ExchangedClauses (H M K T : Subgroup G) : Prop where
  kernel_eq : sourceKernel H M = pCore 2 H
  exchanged_product : ∃ t ∈ T, K ≠ K.conjBy t⁻¹ ∧
    ((M ⊓ H : Subgroup G) : Set G) =
      ((M ⊓ K : Subgroup G) : Set G) * (((M ⊓ K).conjBy t⁻¹ : Subgroup G) : Set G) *
        (T : Set G)

/-- The common clauses of E.2.2(2). The equality lives in H/O₂(H), and
retains the possibly nontrivial central kernel of H/O₂(H) → H/J. -/
structure SingleClauses (H M K T : Subgroup G) : Prop where
  product : (H : Set G) = (K : Set G) * (T : Set G)
  kernel_center : (sourceKernel H M).map (QuotientGroup.mk' (pCore 2 H)) =
    (center (actorImage H K)).map (actorImage H K).subtype

variable [Finite G]

/-- All six alternatives and the exact generation values of E.2.2.
The characteristic-odd cases are retained in full before the reduction. -/
inductive FullAlternatives (H M K T : Subgroup G) : Prop
  | oneA (f : ℕ) : ExchangedClauses H M K T → ExchangedModel H M K f →
      generationParameter H = f → FullAlternatives H M K T
  | oneB : ExchangedClauses H M K T → ExchangedOddModel H M K T →
      generationParameter H = 1 → FullAlternatives H M K T
  | twoA (f : ℕ) : SingleClauses H M K T → BenderModel H M K f →
      generationParameter H = f → FullAlternatives H M K T
  | twoB (f : ℕ) : SingleClauses H M K T → DiagramModel H M K T f →
      generationParameter H = f → FullAlternatives H M K T
  | twoC : SingleClauses H M K T → SingleOddLinearModel H M K T →
      generationParameter H = 1 → FullAlternatives H M K T
  | twoD : SingleClauses H M K T → SingleOddRankThreeModel H M K T →
      generationParameter H = 1 → FullAlternatives H M K T

/-- The complete E.2.2 conclusion for the actual local overlap. This is an
input contract for the E.2.2 owner, not a proof of that classification. All
components and quotient cores are internal to their indicated groups. -/
def FullE22Conclusion (𝒦 : GroupClass.{u}) (H M T : Subgroup G) : Prop :=
  ∃ K : Subgroup G, K ≤ H ∧ (K.subgroupOf H).IsCComponent ∧
    Theory.GroupTheory.IsQuasisimple (K ⧸ pCore 2 K) ∧
    H = K ⊔ T ∧ IsSQTK 𝒦 (H ⧸ sourceKernel H M) ∧ FullAlternatives H M K T

/-- Exactly the three alternatives surviving n(H) > 1. The central quotient
and diagram conditions are unchanged from the full source alternatives. -/
inductive ReducedCases (H M K T : Subgroup G) (f : ℕ) : Prop
  | exchanged : ExchangedClauses H M K T → ExchangedModel H M K f → ReducedCases H M K T f
  | bender : SingleClauses H M K T → BenderModel H M K f → ReducedCases H M K T f
  | diagram : SingleClauses H M K T → DiagramModel H M K T f → ReducedCases H M K T f

/-- E.2.2's numerical clause excludes precisely (1b), (2c), and (2d). -/
theorem FullAlternatives.reduce {H M K T : Subgroup G}
    (h : FullAlternatives H M K T) (hn : 1 < generationParameter H) :
    ∃ f : ℕ, 1 < f ∧ generationParameter H = f ∧ ReducedCases H M K T f := by
  cases h with
  | oneA f hc hm he => exact ⟨f, he ▸ hn, he, .exchanged hc hm⟩
  | oneB _ _ he => omega
  | twoA f hc hm he => exact ⟨f, he ▸ hn, he, .bender hc hm⟩
  | twoB f hc hm he => exact ⟨f, he ▸ hn, he, .diagram hc hm⟩
  | twoC _ _ he => omega
  | twoD _ _ he => omega

/-- The usable conditional output on p.1152. The residual is computed from
component generation; neither a central-cover collapse nor oddness is assumed. -/
structure Reduction (𝒦 : GroupClass.{u}) (H M K T : Subgroup G) (f : ℕ) : Prop where
  component_le : K ≤ H
  component : (K.subgroupOf H).IsCComponent
  quasisimple : Theory.GroupTheory.IsQuasisimple (K ⧸ pCore 2 K)
  generated : H = K ⊔ T
  core_le : pCore 2 H ≤ sourceKernel H M
  quotient_sqtk : IsSQTK 𝒦 (H ⧸ sourceKernel H M)
  exponent_gt_one : 1 < f
  generation_eq : generationParameter H = f
  residual_eq : residual H = conjugateSpanBy K T
  residual_product : (H : Set G) = (residual H : Set G) * (T : Set G)
  cases : ReducedCases H M K T f

/-- Conditional reduction of the full genuine E.2.2 output under the actual
minimal-outside-family hypothesis. The preceding minimal-parabolic result and
E.2.2 output are explicit inputs for source-theorem assembly to discharge. -/
theorem reduce_of_full_e22 {𝒦 : GroupClass.{u}} {T : Sylow 2 G} {H M : Subgroup G}
    (hH : H ∈ minimalSylowOutsideFamily T M)
    (hP : ChapterB.IsMinimalParabolicOver (T.subtype hH.prop.1.2) ⊤)
    (hn : 1 < generationParameter H)
    (hsource : FullE22Conclusion 𝒦 H M (T : Subgroup G)) :
    ∃ (K : Subgroup G) (f : ℕ), Reduction 𝒦 H M K (T : Subgroup G) f := by
  obtain ⟨K, hKH, hK, hqs, hgen, hsqtk, hcases⟩ := hsource
  obtain ⟨f, hf, he, hc⟩ := hcases.reduce hn
  refine ⟨K, f, hKH, hK, hqs, hgen, twoCore_le_sourceKernel hH hP, hsqtk, hf, he, ?_, ?_, hc⟩
  · exact residual_eq_conjugateSpanBy_of_component hgen T.2 hK
  · exact residual_mul_of_component hgen T.2 hK

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.BorelReduction.SourceCases
