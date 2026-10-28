module
public import CFSG.Quasithin.Chapter13.Section07.SourceDuality
public import Theory.GroupTheory.NoncentralChiefRefinement.CubicComparison.SmallQuotients
public import Theory.Representation.BinaryConjugationSection.CubicLength
public import CFSG.Quasithin.Chapter13.Section07.PlusAction.Kernel
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Component.ModelExtension.SourceSetup

/-!
# The four-factor core contribution under the original central duality

A cubic with two noncentral factors on U_H and trivial action on U₀ has the
same two-factor contribution on the dual section Q_H/C_H(U_H). Therefore
its cubic length on Q_H is at least four. Once the actual point-residual
star image is A₄, the normal Klein-four quotient adds the fifth factor.
The model marking and the A₄ residual identification are kept explicit here;
the source consumer constructs them from the selected natural SL₂(4) section.
Source: Aschbacher–Smith, 13.7.13, printed p.943, using 13.7.4(2).
-/
public section
open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section07
open Section08.SourceCompletion
open Section08.TransvectionRecognition.Component.ModelExtension
open Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}

/-- Source central duality counts four factors in the actual two-core. -/
theorem source_core_cubic_length_four
    (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (A : Subgroup G) (hAH : A ≤ H) (hA : Nat.card A = 3)
    (hcentral : A ≤ centralizer (PlusAction.fixedLayer
      (ConjugateIntersections.sourceSetup T L V V₃ V₁ H) : Set G))
    (hUlen : conjugationCubicLength A (Section08.Source.UH H V₃) = 2) :
    4 ≤ conjugationCubicLength A (H.pCoreIn 2) := by
  obtain ⟨hE,τ,sU,sQ,hpair,hcoord⟩ := source_central_duality d h hU
  have hpA : IsPGroup 3 A := IsPGroup.of_card (n := 1) (by simpa using hA)
  have hpQ : IsPGroup 2 (H.pCoreIn 2) := isPGroup_pCoreIn 2 H
  have hpU : IsPGroup 2 (Section08.Source.UH H V₃) :=
    hpQ.of_injective (inclusion h.UH_le_QH) (inclusion_injective _)
  have hd := sU.dual_sectionCubicLength sQ A hAH hA hpU hpQ
  have hfix : conjugationCubicLength A
      (PlusAction.fixedLayer (ConjugateIntersections.sourceSetup T L V V₃ V₁ H)) = 0 := by
    unfold conjugationCubicLength
    rw [relIndex_eq_one.mpr (le_centralizer_iff.mp hcentral)]
    decide
  change conjugationCubicLength A
      ((Section08.Source.UH H V₃) ⊓ centralizer (H.pCoreIn 2 : Set G)) = 0 at hfix
  have hUV : Section08.Source.UH H V₃ ≤ Section08.Source.VH H V :=
    conjugateSpanBy_mono d.seed_le le_rfl
  have hVC : Section08.Source.VH H V ≤ Section08.Source.HC H V₃ :=
    VH_centralizes_UH d h hU
  have hmono := conjugationCubicLength_mono A (hUV.trans hVC)
  unfold sectionCubicLength at hd
  rw [hfix,hUlen] at hd
  omega


/-- The literal A₄ quotient adds the fifth factor to the four-factor core. -/
theorem source_sl2Four_chief_count_ge_five_of_residual
    (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hJH : sourceOne L T V₁ ≤ H)
    (f : sourceOne L T V₁ →* alternatingGroup (Fin 4))
    (hf : Function.Surjective f)
    (hker : f.ker = (H.pCoreIn 2).subgroupOf (sourceOne L T V₁))
    (A : Subgroup G) (hAJ : A ≤ sourceOne L T V₁) (hA : Nat.card A = 3)
    (hcentral : A ≤ centralizer (PlusAction.fixedLayer
      (ConjugateIntersections.sourceSetup T L V V₃ V₁ H) : Set G))
    (hUlen : conjugationCubicLength A (Section08.Source.UH H V₃) = 2)
    (s : NoncentralChiefRefinement.ChiefSeries (sourceOne L T V₁))
    (h0 : s.head = ⊥) (h1 : s.last = ⊤) : 5 ≤ s.noncentralTwoCount := by
  let J := sourceOne L T V₁
  let Q := H.pCoreIn 2
  have hp : IsPGroup 2 f.ker := by
    rw [hker]
    exact (isPGroup_pCoreIn 2 H).comap_subtype
  have hfour := source_core_cubic_length_four d h hU A (hAJ.trans hJH) hA hcentral hUlen
  have hQL : Q ≤ normalizer (J : Set G) := h.QH_le_T.trans
    (T_normalizes_one L T V₁ d.line_stable)
  have hLQ : J ≤ normalizer (Q : Set G) := hJH.trans
    (ChapterF.Section09.Setup.Hypothesis.H_normalizes_QH
      (D := ConjugateIntersections.sourceSetup T L V V₃ V₁ H))
  have hlength := NoncentralChiefRefinement.CubicComparison.intersection_length_eq A Q J
    (IsPGroup.of_card (n := 1) (by simpa using hA)) (isPGroup_pCoreIn 2 H) hAJ hQL hLQ
  have hfi : conjugationCubicLength (A.subgroupOf J) f.ker =
      conjugationCubicLength A Q := by
    rw [hker]
    have he := NoncentralChiefRefinement.CubicComparison.length_subgroupOf A (J ⊓ Q) J hAJ inf_le_left
    rw [inf_subgroupOf_left] at he
    have he' : conjugationCubicLength (A.subgroupOf J) (Q.subgroupOf J) =
        conjugationCubicLength A (Q ⊓ J) := by simpa only [inf_comm] using he
    exact he'.trans hlength
  have hAc : Nat.card (A.subgroupOf J) = 3 :=
    (Nat.card_congr (subgroupOfEquivOfLe hAJ).toEquiv).trans hA
  have heq := NoncentralChiefRefinement.CubicComparison.alternatingFour_count f hf hp
    (A.subgroupOf J) hAc s h0 h1
  rw [hfi] at heq
  dsimp [Q] at heq
  omega

end CFSG.Quasithin.Chapter13.Section07
