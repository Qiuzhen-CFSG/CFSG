module

public import CFSG.Quasithin.Chapter13.Section07.ModelExclusions.NaturalModels
public import CFSG.Quasithin.Chapter13.Section07.ModelExclusions.SeedGeneration
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.Containment.Reduction.NormalizerRank
public import Theory.GroupTheory.PrimeRankFixedJoin
public import Theory.Quasithin.CoprimeRank

/-!
# The rank-one conclusion of 13.7.5(5)

In the covered case the actual point residual has elementary quotient of
order nine by its two-core, hence three-rank at least two. Containment
of L₁ in K and normalization of V₃ contradict rank one for N_K(V₃).
Thus the quotient of L is ordinary A₆. The section-normalizer version
retains the literal map H→H/V₁ used by the exceptional-field consumer.

Source: Aschbacher–Smith, 13.7.5(5), printed p.938.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section07.ModelExclusions
open Section08.SourceCompletion
open Section08.TransvectionRecognition.Component.ModelExtension
open Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
open Section08.ComponentSieve.FieldComponents.ExceptionalFields.Containment.Reduction
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
include d

/-- The two original point-residual quotients, with no additional cardinality input. -/
theorem point_residual_quotient_card :
    Nat.card (sourceOne L T V₁ ⧸ pCore 2 (sourceOne L T V₁)) = 3 ∨
      Nat.card (sourceOne L T V₁ ⧸ pCore 2 (sourceOne L T V₁)) = 9 := by
  rcases NaturalModels.quotient_alternatives d with ⟨e, he⟩ | ⟨e, he⟩
  · obtain ⟨a⟩ := NaturalModels.ordinary_natural d e he
    exact Or.inl (Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics.OrdinarySource.source_residual_quotient_card a _ rfl)
  · obtain ⟨a⟩ := NaturalModels.covered_natural d e he
    exact Or.inr (a.one_quotient_card (CoverFactorization.source_factorization a))

/-- Original 13.7.5(5), needing no additional component-model premise. -/
theorem ordinary_of_rank_one {K : Subgroup G}
    (hL₁K : sourceOne L T V₁ ≤ K)
    (hrank : primeRank 3 (K ⊓ normalizer (V₃ : Set G) : Subgroup G) = 1) :
    Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) := by
  rcases NaturalModels.quotient_alternatives d with ⟨e, _⟩ | ⟨e, he⟩
  · exact ⟨e⟩
  · obtain ⟨a⟩ := NaturalModels.covered_natural d e he
    have hf := CoverFactorization.source_factorization a
    let Q := sourceOne L T V₁ ⧸ pCore 2 (sourceOne L T V₁)
    let : IsMulCommutative Q := a.one_quotient_commutative hf
    let : IsElementaryAbelian 3 (⊤ : Subgroup Q) := {
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
        (fun x => Subtype.ext (a.one_quotient_cube hf x.val)) }
    have hl : 2 ≤ primeRank 3 Q := IsElementaryAbelian.primeRank_ge_of_card
      (⊤ : Subgroup Q) (by rw [card_top]; exact a.one_quotient_card hf)
    rw [primeRank_quotient_eq_of_isTwoGroup 3 (by decide)
      (pCore 2 (sourceOne L T V₁)) pCore_isPGroup] at hl
    have hu := primeRank_mono 3 (le_inf hL₁K (point_residual_normalizes_seed d))
    omega

/-- The exact quotient-normalizer convention in the existing 13.8.20 application. -/
theorem ordinary_of_section_normalizer_rank_one {H K : Subgroup G}
    [(V₁.subgroupOf H).Normal]
    (hKH : K ≤ H) (hV₃H : V₃ ≤ H) (hL₁K : sourceOne L T V₁ ≤ K)
    (hrank : primeRank 3 (seedSectionNormalizer H K V₃ V₁) = 1) :
    Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) := by
  apply ordinary_of_rank_one d hL₁K
  rwa [seedSectionNormalizer_eq H K V₃ V₁ hKH hV₃H
    (d.line_le_plane.trans d.plane_le_seed)] at hrank

/-- The actual contained PSL₂(4) consumer with its universal 13.7.5(5) premise discharged. -/
theorem ordinary_of_contained_linear_two_four
    {F : Type*} [Field F] [Finite F] (hF : Nat.card F = 4)
    {H K : Subgroup G} (hKH : K ≤ H)
    (e : Section08.Source.starImage H K ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)
    (hL₁K : sourceOne L T V₁ ≤ K) :
    Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) :=
  ordinary_of_rank_one d hL₁K
    (linear_two_four_normalizer_rank hF H K (sourceOne L T V₁) V₃ hKH e hL₁K
      (point_residual_normalizes_seed d) (point_residual_quotient_card d))

end CFSG.Quasithin.Chapter13.Section07.ModelExclusions
