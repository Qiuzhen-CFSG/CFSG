module

public import CFSG.Quasithin.Chapter2.Section05.OvercomponentsSource.NormalityTerminal
public import CFSG.Quasithin.Chapter2.Section05.OvercomponentsSource.NormalityTight

/-!
# The original 2.5.20 terminal consumer

The actual two-component orbit and its paired involution residual force tight
embedding, exclude every third returning Sylow conjugate and make the ambient
Sylow normalize K₀. The original unique-maximal-two-local source tuple forbids
that normalization. Thus the nonnormal branch is impossible once its earlier
literal residual calculation is supplied.

This is the final source implication of 2.5.20, printed p.564, used to obtain
K=K₀ at the start of 2.5.21. The paired residual calculation and preceding
2.5.19 component persistence remain genuine source obligations, not conclusions
of this module.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.Section05.OvercomponentsSource
open ComponentRefinement ComponentSelection
variable {G : Type*} [Group G] [Finite G]
  {H K M : Subgroup G} {S : Sylow 2 H} {z : G}

/-- The original nonnormal source branch contradicts its paired residual.
Tightness and the ambient-normalizer conclusion are both derived here. -/
theorem source_nonnormal_pair_residual_false
    (c : MathieuSourceSetup H K M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    (hn : ¬ (K.subgroupOf H).Normal)
    (u : G) (hu : u ∈ (S : Subgroup H).map H.subtype)
    (hc : K ≤ centralizer (K.conjBy u : Set G))
    (horbit : ∀ a ∈ (S : Subgroup H).map H.subtype,
      K.conjBy a = K ∨ K.conjBy a = K.conjBy u)
    (hres : ∀ i ∈ ((S : Subgroup H).map H.subtype ⊓ K : Subgroup G),
      orderOf i = 2 →
      (primeToResidual 3 (centralizer ({i} : Set G))).map
        (centralizer ({i} : Set G)).subtype = K.conjBy u) : False := by
  have htight := tightlyEmbedded_of_involution_residual_source c hG hempty hgen hb
    u hu hc horbit hres
  exact MathieuSourceSetup.ambient_sylow_not_normalize_component_orbit c hgen
    (Normality.ambient_sylow_normalizes_orbit c hG hempty hgen hb hn
      u hu hc horbit htight hres)

end CFSG.Quasithin.Chapter2.Section05.OvercomponentsSource
