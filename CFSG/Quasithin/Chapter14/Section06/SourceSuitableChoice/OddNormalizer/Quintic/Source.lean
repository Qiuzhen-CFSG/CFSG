module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Quintic.ModuleGeometry.ExchangedQuotientExclusion
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddCriticalPair.Alternatives.Source
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Closure.Primitive

/-!
# Original 14.6.15: the maximal odd prime is three

The earlier exchanged factors give p = 3 or p = 5. At p = 5, original
14.6.13 supplies a rank-eight critical endpoint, with its strict kernel
and both point containments. The residual closure case is excluded by
the second-normalizer component comparisons. The remaining full
Aut(PSL₂(16)) wreath case is excluded by its quotient of order 32 and
the actual actor order 200. Thus p = 3 for the original chosen H and Mc.

The first theorem keeps the authorized earlier critical-pair premise.
The second discharges it using the checked 14.6.13 producer. Both retain
the full rank-two prefix, primitive residual and maximal-prime choice.
The earlier 14.6.12 setup (including its factor-join index) remains with
qt-e-14612-singleton; the 14.6.14 alternatives remain with
qt-e-14614-maximal-closure. The 14.6.13 source belongs to
qt-e-suitable-orthogonal-marking. Final suitable-choice and 14.6.25
assembly discharge the remaining earlier inputs. No module-geometry,
component-comparison or contradiction premise is added.

Source: Aschbacher--Smith 14.6.12--15, printed pp.1031--1035.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06.OddNormalizer
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open Quintic
variable {G : Type*} [Group G] [Finite G]
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)]
    (a : LocalQuotientAction H (conjugateSpanBy (localModule T M) H) (centralInvolutions T))
local instance : IsElementaryAbelian 2
    (ChapterF.Section09.Setup.UH
      ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,H⟩) :=
  inferInstanceAs (IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H))

include hG hempty hM hunique hmany hcard e hab hH

/-- Original 14.6.15 with the authorized earlier-source premises exposed.
The critical pair is supplied by 14.6.13, not by a module-geometry callback. -/
theorem source_lemma_14_6_15_of_critical
    (p : ℕ) (H0 H1 H2 : Subgroup G)
    (hp : PrimitiveResidual H p) (hmax : MaximalOddPrime (T : Subgroup G) M p)
    (d : ExchangedFactorSetup a (T : Subgroup G) p H0 H1 H2)
    (hc : SourceClosureAlternatives (T : Subgroup G) Mc H p)
    (hcritical : p = 5 → Nonempty (CriticalPair
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH)
      a Mc H1)) : p = 3 := by
  rcases d.prime with h3 | h5
  · exact h3
  · subst p
    obtain ⟨c⟩ := hcritical rfl
    have hprim : Quintic.PrimitiveResidual H 5 := by
      refine ⟨hp.elementary,?_,hp.minimal⟩
      intro hz
      have hh := d.residual_card
      rw [hz,card_bot] at hh
      norm_num at hh
    exact (ModuleGeometry.source_quintic_exclusion
      (⟨hG,hempty,hM,hunique,hmany,hcard,e,hab,hH,hprim,hmax,d,hc,c⟩ :
        ComponentExclusion.Context T M Mc H H0 H1 H2 a)).elim

/-- Original 14.6.15. The checked 14.6.13 theorem supplies the literal
critical pair, retaining its conjugator and both point containments. -/
theorem source_lemma_14_6_15
    (p : ℕ) (H0 H1 H2 : Subgroup G)
    (hp : PrimitiveResidual H p) (hmax : MaximalOddPrime (T : Subgroup G) M p)
    (d : ExchangedFactorSetup a (T : Subgroup G) p H0 H1 H2)
    (hc : SourceClosureAlternatives (T : Subgroup G) Mc H p) : p = 3 := by
  apply source_lemma_14_6_15_of_critical hG T hempty hM hunique hmany hcard e hab
    H hH a p H0 H1 H2 hp hmax d hc
  intro h5
  subst p
  rcases OddCriticalPair.source_critical_geometry_alternatives hG T hempty hM hunique
      hmany hcard e hab H hH a 5 H0 H1 H2 d with ⟨h3,_⟩ | ⟨_,⟨c⟩⟩
  · norm_num at h3
  · let D : ChapterF.Section09.Setup G :=
      ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,H⟩
    let h : D.Hypothesis :=
      source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH
    obtain ⟨hb,_,_⟩ := source_rankTwo_critical_track_bounds hG T hempty hM hunique
      hmany hcard e hab H hH
    have hγ : c.endpoint.conjugate D.UH ≤ D.H :=
      (map_mono (conjugateSpanBy_mono h.plus_le le_rfl)).trans (c.endpoint.large_le hb)
    have hd := c.strict
    rw [OddCriticalPair.critical_denominator_eq h _ hγ,
      ←h.kernel_UH_eq_QH] at hd
    exact ⟨⟨c.endpoint,c.outside,hd,c.first_actor,c.point,c.reverse_point,c.dimension⟩⟩

end CFSG.Quasithin.Chapter14.Section06.OddNormalizer
