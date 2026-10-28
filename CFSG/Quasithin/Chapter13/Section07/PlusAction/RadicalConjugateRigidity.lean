module

public import CFSG.Quasithin.Chapter13.Section01.RadicalConjugateRigidity.Source
public import CFSG.Quasithin.Chapter13.Section07.PlusAction.PrimitiveSource
public import CFSG.Quasithin.Chapter1.Section02.Adequate.Families

/-!
# Canonical radical rigidity at a source plus-kernel component

A C-component in the literal plus-action kernel is faithful by the proved
opening calculation of 13.7.4. The original flag line makes O₂(H) nontrivial,
so the component belongs to L_f(G,T) and has an actual maximal local overgroup.
Every nonquasisimple such overgroup now has the canonical-radical rigidity
proved in 13.1.11. This connects that earlier source branch to the actual
kernel reduction. It does not assume or assert the still missing 13.1.7
exclusion or the complete five-model catalogue of 13.3.2.

Source: Aschbacher--Smith 13.1.11, p.872; 13.3.2, p.884; 13.7.4(1), p.937.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section07.PlusAction
open Section08.SourceCompletion Chapter1 Chapter1.Section02.Adequate
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
include d

/-- The component branch of primitive kernel selection belongs to the
actual faithful local family, without assuming T-normality of the component. -/
theorem source_kernel_component_local
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    {K : Subgroup G}
    (hKC : K ≤ kernel (ConjugateIntersections.sourceSetup T L V V₃ V₁ H))
    (hcomp : (K.subgroupOf H).IsCComponent) (hp : IsPPerfect 2 K) :
    K ∈ MainForward.faithfulLocalComponents T := by
  have hKH : K ≤ H := hKC.trans kernel_le_H
  have hne : K ≠ ⊥ := by
    intro hz
    apply hcomp.ne_bot
    rw [hz]
    ext x
    change (x : G) = 1 ↔ x = 1
    exact ⟨fun he => Subtype.ext he, fun he => congrArg Subtype.val he⟩
  have hpoint : V₁ ≤ H.pCoreIn 2 :=
    h.point_lt.le.trans ((le_conjugateSpanBy V₃ H).trans h.UH_le_QH)
  have hH : H ∈ Chapter1.H G := by
    intro hz
    apply h.g2_hypothesis.point_ne_bot
    exact bot_unique (hz ▸ hpoint)
  have hl : K ∈ Chapter1.L G (T : Subgroup G) := mem_L_of_cComponent hH
    ⟨T.subtype h.T_le_H, map_subgroupOf_eq_of_le h.T_le_H⟩ hKH hcomp
  exact (mem_faithfulLocalComponents_iff T K).mpr
    ⟨hl, source_plus_kernel_faithful_signalizer d h hU hKC hcomp.subnormal hp hne⟩

/-- Select a genuine maximal local overgroup of the literal kernel component.
Its nonquasisimple branch satisfies the full canonical 13.1.11 conclusion. -/
theorem source_kernel_component_maximal_radical_rigidity
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    {K : Subgroup G}
    (hKC : K ≤ kernel (ConjugateIntersections.sourceSetup T L V V₃ V₁ H))
    (hcomp : (K.subgroupOf H).IsCComponent) (hp : IsPPerfect 2 K) :
    K ∈ MainForward.faithfulLocalComponents T ∧
    ∃ I ∈ LStar G (T : Subgroup G), K ≤ I ∧
      ∀ (_hn : ¬ IsQuasisimple (XiQuotient I)) (p : ℕ) (_hp : p.Prime)
        (_ho : Odd p) (_hd : p ∣ Nat.card (fittingSubgroup (XiQuotient I)))
        (X₁ : Subgroup G) (_hXX₁ : XiP p I ≤ X₁)
        (hX₁M : X₁ ≤ normalizer (I : Set G)),
        (∀ A : Subgroup (XiFrattiniQuotient (XiP p I)),
          (∀ s : X₁, ∀ a ∈ A,
            xiFrattiniAction X₁ (XiP p I) (XiP_invariant p hX₁M) s a ∈ A) →
              A = ⊥ ∨ A = ⊤) →
        ∀ g : G, X₁ ≤ (normalizer (I : Set G)).conjBy g →
          g ∈ normalizer (I : Set G) ∧
            (normalizer (I : Set G)).conjBy g = normalizer (I : Set G) := by
  have hlocal := source_kernel_component_local d h hU hKC hcomp hp
  obtain ⟨I,hI,hKI⟩ := exists_mem_LStar_ge ((mem_faithfulLocalComponents_iff T K).mp hlocal).1
  refine ⟨hlocal,I,hI,hKI,?_⟩
  intro hn p hprime ho hd X₁ hXX₁ hX₁M hirr g hg
  let : Fact p.Prime := ⟨hprime⟩
  exact Section01.RadicalConjugateRigidity.maximal_radical_unique_conjugate
    d.counterexample.qtke T hI hn ho hd X₁ hXX₁ hX₁M hirr g hg

end CFSG.Quasithin.Chapter13.Section07.PlusAction
