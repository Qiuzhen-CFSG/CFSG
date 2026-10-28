module

public import CFSG.Quasithin.ChapterK.Section01To04.SporadicCatalogue.RudvalisExclusion.Transport
public import CFSG.Quasithin.ChapterK.Section01To04.SporadicCatalogue.RudvalisExclusion.DirectSource
public import CFSG.Quasithin.ChapterK.Section01To04.SporadicCatalogue.Sieve
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Pariahs.DegreeBounds
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Theory.SpecificGroups.Rudvalis.Multiplier.OddPrimary
public import Theory.SpecificGroups.Rudvalis.Model.TwoRankSix
public import Theory.SpecificGroups.Rudvalis.Model.OuterStabilizer

/-!
# Exclusion of Rudvalis under the full Chapter K source hypotheses

The odd-primary covering theorem, intrinsic two-rank bound and invariance of
the actual point-stabilizer class discharge the three group inputs of the
direct displacement argument. That argument transports the original ambient
cubic actor and excludes every faithful finite-dimensional binary source
action, without an upper degree bound. Both the full source exclusion and
the existing degree-36 contract are exported, and the catalogue sieve consumes
the full exclusion.

The earlier conditional recognition and normalizer reductions are preserved.
Source: Aschbacher--Smith K.4, printed p.457, citing Guralnick--Malle,
Classification of 2F-modules I, Proposition 5.1 and Theorem 6.6.
-/

public section
namespace CFSG.Quasithin.ChapterK.SporadicCatalogue
open Theory.GroupTheory Subgroup
open RudvalisExclusion
universe u v

/-- K.4 excludes the actual Rudvalis central quotient under the original
source hypotheses. All three group premises of the direct proof are discharged. -/
theorem sourceExclusion_ru : SourceExclusion.{u,v} .ru :=
  RudvalisDirect.sourceExclusion_ru_of_groupFacts
    (fun he => Rudvalis.Multiplier.source_center_isPGroup he)
    (fun _ _ => Rudvalis.primeRank_le_six)
    (fun hs _ => @Rudvalis.outer_stabilizer_map_eq hs)

/-- The degree-36 contract required by the existing sporadic catalogue.
The direct proof applies in every finite dimension. -/
theorem boundedSourceExclusion_ru : BoundedSourceExclusion.{u,v} .ru 36 := by
  intro G V _ _ _ _ _ ρ h he _
  exact sourceExclusion_ru ρ h he

/-- Apply the Ru exclusion to the literal Theorem C catalogue sieve.
The other five sporadic exclusions remain with their independent source owners. -/
theorem survivingCentralQuotient_of_source_exclusions_except_ru
    {G : Type u} {V : Type v} [Group G] [Finite G]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (h : SourceHypotheses ρ)
    (hmodel : ChapterA.Section02.IsTheoremCSporadicModel
      (generalizedFitting G ⧸ center (generalizedFitting G)))
    (hm11 : SourceExclusion.{u,v} .m11) (hj1 : SourceExclusion.{u,v} .j1)
    (hj4 : SourceExclusion.{u,v} .j4) (hhs : SourceExclusion.{u,v} .hs)
    (hhe : SourceExclusion.{u,v} .he) :
    IsSurvivingCentralQuotient (generalizedFitting G) :=
  survivingCentralQuotient_of_source_exclusions ρ h hmodel
    hm11 hj1 hj4 hhs hhe sourceExclusion_ru

/-- The remaining source dimensions start at 28, even for arbitrary covers. -/
theorem ru_source_degree_ge_twentyEight
    {G : Type u} {V : Type v} [Group G] [Finite G]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (h : SourceHypotheses ρ)
    (e : generalizedFitting G ⧸ center (generalizedFitting G) ≃*
      KnownSimple.SporadicName.ru.Carrier) : 28 ≤ Module.finrank (ZMod 2) V :=
  ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Pariahs.ru_degree
    (ρ.comp (generalizedFitting G).subtype)
    (h.faithful.comp (generalizedFitting G).subtype_injective) e

/-- The actual source application of the independent recognition and finite
normalizer calculations. Neither remaining input is a source catalogue tag. -/
theorem boundedSourceExclusion_ru_of_standardModule
    (hrec : SmallModuleRecognition.{u,v})
    (hcalc : StandardNormalizerExclusion) : BoundedSourceExclusion.{u,v} .ru 36 := by
  intro G V _ _ _ _ _ ρ h he hd
  let := h.quasisimple
  obtain ⟨e, E, hE⟩ := hrec (ρ.comp (generalizedFitting G).subtype)
    (h.faithful.comp (generalizedFitting G).subtype_injective) h.irreducible he hd
  exact (not_le_of_gt hcalc) (cubic_le_two_standardNormalizer ρ (generalizedFitting G)
    h.faithful e E hE h.cubic_le_two)

/-- The source already supplies quasisimplicity and irreducibility. Transport
them to the marked action before applying the finite normalizer calculation. -/
theorem boundedSourceExclusion_ru_of_sourceCalculations
    (hrec : SmallModuleRecognition.{u,v})
    (hcalc : SourceNormalizerExclusion) : BoundedSourceExclusion.{u,v} .ru 36 := by
  intro G V _ _ _ _ _ ρ h he hd
  let := h.quasisimple
  obtain ⟨e, E, hE⟩ := hrec (ρ.comp (generalizedFitting G).subtype)
    (h.faithful.comp (generalizedFitting G).subtype_injective) h.irreducible he hd
  have hsimple : IsQuasisimple standardGroup := IsQuasisimple.of_mulEquiv e
  have hi := standardRepresentation_irreducible_of_marking
    (ρ.comp (generalizedFitting G).subtype) e E hE h.irreducible
  exact (not_le_of_gt (hcalc hsimple hi))
    (cubic_le_two_standardNormalizer ρ (generalizedFitting G)
      h.faithful e E hE h.cubic_le_two)

end CFSG.Quasithin.ChapterK.SporadicCatalogue
