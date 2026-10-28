module
public import CFSG.Quasithin.Chapter13.Section07.ModelExclusions.PlaneMotion
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Parabolic.Marking.CompatibleFlags.Transport
/-!
# The original plane orbit generates the seed

The L₁-orbit of V₂ lies in V₃. Its order is four or eight, and order four
would make L₁ normalize V₂, contradicting the original natural flag action.
In the covered case the central factor L₀ acts trivially, so the same
argument applies to L₁,+. The final theorem transports the actual group
identity through the original U_H/V₁ quotient to the exact sectionImage
orbit span used by the alternating-module marking argument.

Source: Aschbacher–Smith, proof of13.7.6, printed p.939, before(i–iii).
-/

@[expose] public section
open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section07.ModelExclusions
open Section08.SourceCompletion NaturalAction
open Section08.TransvectionRecognition Component
open Section08.TransvectionRecognition.Component.ModelExtension
open Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
include d

private theorem plane_span_of_moves {X : Subgroup G}
    (hX : X ≤ normalizer (V₃ : Set G)) (hmoves : ¬ X ≤ normalizer (V₂ : Set G)) :
    conjugateSpanBy V₂ X = V₃ := by
  let W := conjugateSpanBy V₂ X
  have hW : W ≤ V₃ := conjugateSpanBy_le d.plane_le_seed hX
  have hEW : V₂ ≤ W := le_conjugateSpanBy V₂ X
  apply eq_of_le_of_card_ge hW
  have hlo : 4 ≤ Nat.card W := d.plane_card ▸ card_le_of_le hEW
  have hd : Nat.card W ∣ 8 := d.seed_card ▸ card_dvd_of_le hW
  have hm := Nat.mem_divisors.mpr ⟨hd, by decide⟩
  rw [show (8 : ℕ).divisors = {1,2,4,8} by decide] at hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  have hne : Nat.card W ≠ 4 := by
    intro he
    have hEq : V₂ = W := eq_of_le_of_card_ge hEW (by rw [he, d.plane_card])
    exact hmoves (hEq.symm ▸ le_normalizer_conjugateSpanBy V₂ X)
  rw [d.seed_card]
  omega

/-- The original plane orbit under the actual point residual generates the original seed. -/
theorem plane_orbit_point_residual : conjugateSpanBy V₂ (sourceOne L T V₁) = V₃ :=
  plane_span_of_moves d (point_residual_normalizes_seed d) (point_residual_not_normalizes_plane d)

/-- The covered plus factor also generates the original seed from the plane. -/
theorem plane_orbit_plus
    (hcover : Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms)) :
    conjugateSpanBy V₂ (plus L T V₁) = V₃ := by
  apply plane_span_of_moves d
    ((plus_le_one L T V₁ d.line_stable).trans (point_residual_normalizes_seed d))
  intro hp
  apply point_residual_not_normalizes_plane d
  change one L T V₁ ≤ _
  rw [covered_factorization d hcover]
  apply sup_le hp
  exact (residual_le (centralPreimage L)).trans
    (((NaturalModels.centralPreimage_centralizes d).trans
      (centralizer_le (d.plane_le_seed.trans d.seed_le))).trans
        (Subgroup.centralizer_le_normalizer _))

variable {H : Subgroup G}
  [(V₁.subgroupOf (Section08.Source.UH H V₃)).Normal]
  [IsElementaryAbelian 2 (Section08.Source.Utilde H V₃ V₁)]
open Section08.TransvectionParabolic.Marking Section08.TransvectionParabolic.Marking.CompatibleFlags

/-- The exact sectionImage orbit identity consumed by the original alternating marking. -/
theorem seed_section_plane_orbit
    (hL₁H : sourceOne L T V₁ ≤ H)
    (ρ : Representation (ZMod 2) (Section08.Source.Hstar H)
      (Additive (Section08.Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ) :
    sectionImage H V₃ V₁ V₃ = Submodule.span (ZMod 2)
      {v | ∃ a ∈ Section08.Source.starImage H (sourceOne L T V₁),
        ∃ x ∈ sectionImage H V₃ V₁ V₂, ρ a x = v} := by
  rw [← sectionImage_conjugateSpan ρ hρ V₂ (sourceOne L T V₁)
    (d.plane_le_seed.trans (le_conjugateSpanBy V₃ H)) hL₁H,
    plane_orbit_point_residual d]

end CFSG.Quasithin.Chapter13.Section07.ModelExclusions
