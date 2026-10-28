module
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne.OriginalMaps
public import CFSG.Quasithin.Chapter13.Section08.A6Endgame.ActionAnalysis33.ChiefFiltrations
public import CFSG.Quasithin.Chapter13.Section08.A6Endgame.PointNormalizer.CoreFixed
public import Theory.Representation.BinaryConjugationSection.CubicLength

/-!
# The literal H-side dual section in the original filtration

The image of C_{U_H}(Q_H) in U_H/V₁ is a proper invariant subspace of the
natural module or its augmentation cover. The original noncentral seed
makes it proper. Both models fix every such subspace pointwise, so coprime
fixed-point lifting gives cubic length zero on the full denominator.
The original central pairing then identifies the cubic length of Q_H/H_C
with that of U_H, retaining the actual denominator and the constant line.

OriginalRightFiltration applies this to the same actor as the L-side
filtration. The seed-core noncentrality is the earlier source 13.5.4(5)
premise already used by the terminal consumers; it is not a numerical bound.
Source: Aschbacher--Smith, 13.7.4(2) and 13.8.33, printed pp.936,968.
-/

public section
open Subgroup Representation
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne
open TransvectionRecognition.Component.ModelExtension A6Endgame.IntersectionBalance
open A6Endgame.ActionAnalysis33
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}
  [IsElementaryAbelian 2 (Source.UH H V₃)]

/-- The literal central-duality denominator contributes zero to every cubic
subgroup of H. The full constant line and central kernel are retained. -/
theorem original_dual_denominator_length_zero
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (h : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (a : SolvableExclusion.Five.StarAction H (Source.UH H V₃) V₁)
    (e : Source.Hstar H ≃* Equiv.Perm (Fin 6))
    (model : CompatibleModel H V₃ V₁ a e)
    (hmove : ⁅V₃, Source.QH H⁆ ≠ ⊥)
    (A : Subgroup G) (hAH : A ≤ H) (hA : IsPGroup 3 A) :
    conjugationCubicLength A (dualDenominator H V₃) = 0 := by
  let U := Source.UH H V₃
  let D := dualDenominator H V₃
  have hZ : V₁ ≤ D := le_inf (d.line_le_uh H)
    (le_centralizer_iff.mp ((pCoreIn_le 2 H).trans h.H_centralizes))
  have hDn : H ≤ normalizer (D : Set G) :=
    (le_inf (le_normalizer_conjugateSpanBy V₃ H)
      ((ChapterF.Section09.Setup.Hypothesis.H_normalizes_QH
        (D := Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H)).trans
        (normalizer_le_normalizer_centralizer _))).trans inf_normalizer_le_normalizer_inf
  have hZn : H ≤ normalizer (V₁ : Set G) :=
    h.H_centralizes.trans (Subgroup.centralizer_le_normalizer _)
  let : (V₁.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
    ((show D ≤ H from inf_le_left.trans h.UH_le_H).trans hZn)
  have hproper : ¬ U ≤ centralizer (Source.QH H : Set G) := by
    intro hc
    exact hmove (commutator_eq_bot_iff_le_centralizer.mpr ((le_conjugateSpanBy V₃ H).trans hc))
  have hc : ⁅D,A⁆ ≤ V₁ := by
    rw [commutator_comm,commutator_le]
    intro b hb u hu
    let z : U := ⟨u,hu.1⟩
    have hf := A6Endgame.PointNormalizer.core_fixed_image_fixed a (d.line_le_uh H)
      h.H_centralizes hproper (Or.inr ⟨e,model.action_cases H V₃ V₁ a e⟩) z hu.2
      (QuotientGroup.mk' (pCore 2 H) ⟨b,hAH hb⟩)
    rw [a.conjugation] at hf
    have hm := QuotientGroup.eq_iff_div_mem.mp hf
    change b * u * b⁻¹ / u ∈ V₁ at hm
    simpa only [commutatorElement_def,div_eq_mul_inv] using hm
  have he := NoncentralChiefRefinement.CubicComparison.length_eq_of_commutator_le
    A D V₁ hA ((isPGroup_pCoreIn 2 H).to_le (inf_le_left.trans h.UH_le_QH))
    hZ (hAH.trans hDn) (hAH.trans hZn) hc
  rw [← he,conjugationCubicLength,
    show (centralizer (A : Set G)).relIndex V₁ = 1 from
      relIndex_eq_one.mpr (le_centralizer_iff.mp (hAH.trans h.H_centralizes))]
  rfl

/-- Original 13.7.4(2), applied to the same cubic actor as the two filtrations.
Its actual denominator is fixed by that actor, so QH/HC and UH have equal length. -/
theorem original_dual_section_length
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (h : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (a : SolvableExclusion.Five.StarAction H (Source.UH H V₃) V₁)
    (e : Source.Hstar H ≃* Equiv.Perm (Fin 6))
    (model : CompatibleModel H V₃ V₁ a e)
    (hmove : ⁅V₃, Source.QH H⁆ ≠ ⊥)
    (A : Subgroup G) (hAH : A ≤ H) (hA : Nat.card A = 3) :
    sectionCubicLength A (Source.HC H V₃) (Source.QH H) =
      conjugationCubicLength A (Source.UH H V₃) := by
  obtain ⟨hE,ρ,sU,sQ,_,_⟩ := Section07.source_central_duality (localNaturalSetup d) h
    (show IsMulCommutative (Source.UH H V₃) from inferInstance)
  have he := sU.dual_sectionCubicLength sQ A hAH hA
    ((isPGroup_pCoreIn 2 H).to_le h.UH_le_QH) (isPGroup_pCoreIn 2 H)
  have hz := original_dual_denominator_length_zero d h a e model hmove A hAH
    (IsPGroup.of_card (n := 1) (by simpa using hA))
  change sectionCubicLength A (Source.HC H V₃) (Source.QH H) =
    conjugationCubicLength A (Source.UH H V₃) - conjugationCubicLength A (dualDenominator H V₃) at he
  simpa only [hz,Nat.sub_zero] using he
end CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne
