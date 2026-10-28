module

public import CFSG.Quasithin.ChapterK.Section01To04.SporadicCatalogue.RudvalisExclusion.NormalizerExclusion.Displacement
public import CFSG.Quasithin.ChapterK.Section01To04.SporadicCatalogue.RudvalisExclusion.NormalizerExclusion.Automorphisms
public import Theory.Representation.BinaryOffender.MaximalCentralizerSaturation
public import Theory.Representation.BinaryOffender.InnerNormalizerActors

/-!
# The centralizer argument in the Rudvalis normalizer

The certified displacement bounds force a possible actor to saturate the
rank-six bound. Maximal low-displacement involution centralizers would then
all be the stabilizer of the same proper nonzero fixed space. Their double
centralizer is too small to contain the actor.

The final theorem below is conditional on the finite local group calculation
and innerness of involutory automorphisms. The normalizer descent retains the
literal operators through `normalizerEmbedding`; no ambient outer action is
silently removed. These remaining group inputs must be discharged before
asserting `sourceNormalizerExclusion`.

Source: Guralnick--Malle, Classification of 2F-modules I, Proposition 5.1,
Ru paragraph, manuscript p.17; Aschbacher--Smith K.4, printed p.457.
-/

public section
namespace CFSG.Quasithin.ChapterK.SporadicCatalogue.RudvalisExclusion
open Subgroup Representation.BinaryOffender NormalizerExclusion Theory.GroupTheory
open scoped ENNReal

/-- The fixed-space argument on the actual matrix group. -/
theorem not_small_standard_actor (hmodel : StandardComparison)
    (hi : standardRepresentation.IsIrreducible) (hlocal : LocalStructure)
    (A : Subgroup standardGroup) (hA : IsElementaryTwo A) :
    ¬ fixedCodim standardRepresentation A ≤ 2 * rank A := by
  let : IsElementaryAbelian 2 A := hA.2
  apply not_small_actor_of_maximal_centralizers standardRepresentation hi hA
    (n := 2) (r := 6) (by decide) (by decide)
    (rank_le_of_primeRank_le hA hlocal.1) (by rw [finrank_space]; decide)
  · intro t ht ht1
    exact (involution_displacement hmodel t ht1
      (elemPow_eq_one_of_isElementaryAbelian t ht)).1
  · intro t ht ht1 hd
    exact hlocal.2 t ((involution_displacement hmodel t ht1
      (elemPow_eq_one_of_isElementaryAbelian t ht)).2 hd)

/-- Exclusion in the full normalizer, conditional on the exact remaining
finite group inputs. Only elementary actors are descended to the matrix group. -/
theorem standardNormalizerExclusion_of_localCalculations (hmodel : StandardComparison)
    (hi : standardRepresentation.IsIrreducible) (hlocal : LocalStructure)
    (hinner : ∀ α : MulAut standardGroup, α ^ 2 = 1 →
      ∃ x : standardGroup, x ^ 2 = 1 ∧ α = MulAut.conj x) :
    StandardNormalizerExclusion := by
  apply lt_of_not_ge
  intro hq
  obtain ⟨A, hA, _, hd⟩ :=
    (cubicRatio_le_nat_iff (normalizerRepresentation standardRepresentation) 2).mp hq
  obtain ⟨B, hB, hBA⟩ := elementary_normalizer_is_image standardRepresentation
    standardRepresentation_injective hi hinner A hA
  apply not_small_standard_actor hmodel hi hlocal B hB
  have hc := fixedCodim_map_equivariant standardRepresentation
    (normalizerRepresentation standardRepresentation)
    (normalizerEmbedding standardRepresentation) (LinearEquiv.refl _ _)
    (fun _ _ => rfl) B
  rw [hBA] at hc
  have hr := rank_map_injective (normalizerEmbedding standardRepresentation)
    (normalizerEmbedding_injective standardRepresentation standardRepresentation_injective) B
  rw [hBA] at hr
  rw [hc, ← hr]
  exact hd

/-- Source assembly retains the quasisimplicity and irreducibility hypotheses
that its caller supplies. The two additional calculations remain obligations. -/
theorem sourceNormalizerExclusion_of_localCalculations (hmodel : StandardComparison)
    (hlocal : IsQuasisimple standardGroup → LocalStructure)
    (hinner : IsQuasisimple standardGroup → standardRepresentation.IsIrreducible →
      ∀ α : MulAut standardGroup, α ^ 2 = 1 →
        ∃ x : standardGroup, x ^ 2 = 1 ∧ α = MulAut.conj x) :
    SourceNormalizerExclusion := by
  intro hq hi
  exact standardNormalizerExclusion_of_localCalculations hmodel hi (hlocal hq) (hinner hq hi)

/-- The complete source reduction to the three independent model calculations.
Simplicity and perfectness required by the rank and automorphism producers
are derived here from the original source hypotheses. -/
theorem sourceNormalizerExclusion_of_modelFacts (hmodel : StandardComparison)
    (hcentral : IsQuasisimple standardGroup → standardRepresentation.IsIrreducible →
      LowInvolutionCentralizers)
    (hrank : IsSimpleGroup Rudvalis.Model → Group.IsPerfect Rudvalis.Model →
      primeRank 2 Rudvalis.Model ≤ 6)
    (hstable : IsSimpleGroup Rudvalis.Model → Group.IsPerfect Rudvalis.Model →
      ∀ f : MulAut Rudvalis.Model, ∃ y : Fin 4060,
        (MulAction.stabilizer Rudvalis.Model (0 : Fin 4060)).map f.toMonoidHom =
          MulAction.stabilizer Rudvalis.Model y) : SourceNormalizerExclusion := by
  intro hq hi
  have hC := hcentral hq hi
  have hs := model_isSimple_of_lowCentralizers hmodel hq hi hC
  have hp := model_isPerfect hmodel hq
  exact standardNormalizerExclusion_of_localCalculations hmodel hi
    ⟨standard_rank_le_of_model_rank hmodel (hrank hs hp), hC⟩
    (standard_involutory_inner_of_pointStabilizers hmodel hi hC (hstable hs hp))

end CFSG.Quasithin.ChapterK.SporadicCatalogue.RudvalisExclusion
