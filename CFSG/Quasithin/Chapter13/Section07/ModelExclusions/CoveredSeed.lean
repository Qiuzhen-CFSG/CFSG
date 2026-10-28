module

public import CFSG.Quasithin.Chapter13.Section07.ModelExclusions.NaturalModels
public import CFSG.Quasithin.Chapter13.Section07.ModelExclusions.SeedGeneration
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement.LocalAction.NaturalSeed

/-!
# The covered seed in 13.7.5

The original covered factorization L₁=L₁,+L₀ and the central action of
L₀ remove that factor from the seed commutator. Full seed generation
therefore holds for the literal L₁,+, as well as for L₁. The same conjugate
span argument supplies 13.7.5(2) in the covered contained-seed branch.

Source: Aschbacher–Smith, 13.2.2(3), p.877, and 13.7.5(2), p.938.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section07.ModelExclusions
open Section08.SourceCompletion NaturalAction
open Section08.TransvectionRecognition.Component.ModelExtension
open Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
include d

/-- The covered factorization is recovered before the abelian-span theorem. -/
theorem covered_factorization
    (hcover : Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms)) :
    one L T V₁ = plus L T V₁ ⊔ zero L := by
  rcases NaturalModels.quotient_alternatives d with ⟨e, he⟩ | ⟨e, he⟩
  · obtain ⟨ec⟩ := hcover
    have hc := Nat.card_congr (centerCongr (e.symm.trans ec)).toEquiv
    rw [alternatingGroup.center_eq_bot (by simp), card_bot,
      Representation.Hexacode.even_center_card] at hc
    omega
  · obtain ⟨a⟩ := NaturalModels.covered_natural d e he
    exact CoverFactorization.source_factorization a

/-- In the covered case the actual L₁,+ generates all of V₃ by commutators. -/
theorem seed_commutator_plus
    (hcover : Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms)) :
    ⁅V₃, plus L T V₁⁆ = V₃ := by
  have hz : zero L ≤ centralizer (V₃ : Set G) :=
    (residual_le (centralPreimage L)).trans
      ((NaturalModels.centralPreimage_centralizes d).trans (centralizer_le d.seed_le))
  have hp : plus L T V₁ ≤ normalizer (V₃ : Set G) :=
    (plus_le_one L T V₁ d.line_stable).trans (point_residual_normalizes_seed d)
  have h := commutator_eq_of_centralizing_sup
    (show zero L ⊔ plus L T V₁ = one L T V₁ by
      rw [sup_comm]; exact (covered_factorization d hcover).symm) hz hp
  exact h.trans (seed_commutator_point_residual d)

/-- The literal U_H conclusion in the covered X=L₁,+ branch. -/
theorem span_commutator_of_containing_covered_seed {H K : Subgroup G}
    (hcover : Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms))
    (hKH : K ≤ H) (hKn : H ≤ normalizer (K : Set G))
    (hplusK : plus L T V₁ ≤ K) :
    ⁅Section08.Source.UH H V₃, K⁆ = Section08.Source.UH H V₃ := by
  have hUH : H ≤ normalizer (Section08.Source.UH H V₃ : Set G) :=
    le_normalizer_conjugateSpanBy V₃ H
  apply le_antisymm (le_normalizer_iff_commutator_le_left.mp (hKH.trans hUH))
  apply conjugateSpanBy_le
  · exact (seed_commutator_plus d hcover).symm.le.trans
      (commutator_mono (le_conjugateSpanBy V₃ H) hplusK)
  · intro x hx
    rw [mem_normalizer_iff_map_conj_eq, map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (hUH hx),
      mem_normalizer_iff_map_conj_eq.mp (hKn hx)]

end CFSG.Quasithin.Chapter13.Section07.ModelExclusions
