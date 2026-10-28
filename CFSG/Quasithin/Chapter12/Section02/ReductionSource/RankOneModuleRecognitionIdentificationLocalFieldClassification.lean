module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationLocalFieldClassification
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionIdentificationLocalFieldReduced

/-!
# The field-plane quotient classification on the original Chapter 12 layer

The chosen module supplies E.6.1 and the central-line normalizer
factorization. The actual conjugate image is quadratic, with its moved
space identified with the image of the original commutator plane.
The complete adequate B.5 alternatives hold on the normal best-offender
subgroup, and a minimal seed inside the original four-group controls
its moved components. All section coordinates are retained.

Source: Aschbacher--Smith, 6.2.7, pp.682--683, in the rank-one branch of
12.2.2(3d), p.795. The remaining source exclusions belong to local assembly.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
open CFSG.Quasithin.Chapter6.Source CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open CFSG.Quasithin.ChapterB.QuasisimpleSource CFSG.Quasithin.ChapterB.SourceInduction
namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}

/-- The actual quotient action has the complete adequate offender classification,
with the original commutator plane, minimal seed and section coordinates. -/
theorem source_local_one_sided_classified_action
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Conclusion6127 (T : Subgroup G) L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (g : G)
    (hBA : commutatorLayer T L ≤ normalizer
      ((commutatorLayer T L).map (MulAut.conj g).toMonoidHom : Set G))
    (hnon : ¬ (commutatorLayer T L).map (MulAut.conj g).toMonoidHom ≤
      centralizer (commutatorLayer T L : Set G)) :
    let B := commutatorLayer T L
    let A := B.map (MulAut.conj g).toMonoidHom
    let U := B ⊓ centralizer (A : Set G)
    letI := (source_local_one_sided_reduced_action D h h611 hnatural g hBA hnon).1.elementary
    let H := LocalFieldQuotientAction.Centralizer U
    let J := conjugateSpanBy B H
    let π := (LocalFieldQuotientAction.action B U).rangeRestrict
    let I := (A.subgroupOf H).map π
    ∃ (ρ : Representation (ZMod 2) (LocalFieldQuotientAction.action B U).range
        (Additive (LocalFieldQuotientAction.space B U)))
      (c : Representation.BinaryConjugationSection H J U (ρ.comp π)),
      Function.Injective ρ ∧ IsOffender ρ I ∧ IsQuadratic ρ I ∧ Nat.card I = 4 ∧
      moved ρ I = c.imageSpace ⁅A,B⁆ ∧ Module.finrank (ZMod 2) (moved ρ I) ≤ 2 ∧
      Nat.card (U ⊓ ⁅A,B⁆ : Subgroup G) * 2 ^ Module.finrank (ZMod 2) (moved ρ I) = 4 ∧
      ((U ⊓ ⁅A,B⁆ = ⊥ ∧ Module.finrank (ZMod 2) (moved ρ I) = 2) ∨
        (Nat.card (U ⊓ ⁅A,B⁆ : Subgroup G) = 2 ∧
          Module.finrank (ZMod 2) (moved ρ I) = 1)) ∧
      (U ⊓ ⁅A,B⁆ = ⊥ → fixedCodim ρ I = 2 ∧
        I ∈ CFSG.Quasithin.ChapterE.fixedSpaceFamily ρ 2 ∧ IsMinimalBestOffender ρ I ∧
        ∀ K, IsComponent (LocalFieldQuotientAction.action B U).range K → ⁅K,I⁆ = K →
          IsIrrPlus ρ K (moved ρ K) ∧ SmallMoved.ActorList K) ∧
      NontrivialAdequateAlternative (ρ.comp (offenderSubgroup ρ).subtype) ∧
      (∃ Q ≤ I, IsMinimalBestOffender ρ Q ∧ IsQuadratic ρ Q ∧
        ∀ K, IsComponent (LocalFieldQuotientAction.action B U).range K → ⁅K,Q⁆ = K →
          IsIrrPlus ρ K (moved ρ K) ∧ SmallMoved.ActorList K) ∧
      ∀ j : J, ∃ hj : (j : G) ∈ H, LocalFieldQuotientAction.projection U ⟨j, hj⟩ =
        ((c.coordinates j).toAdd.toMul : LocalFieldQuotientAction.Ambient U) := by
  have hnat : IsNaturalModule L (commutatorLayer T L) n := hnatural.1 ▸ hnatural.2.1
  exact LocalFieldQuotientAction.exists_classified_offender_action h611 hnatural
    (source_natural_layer_hypothesisE61 D h.toHypothesis1221 h611 hnat)
    (source_central_line_normalizer_factorization D h.toHypothesis1221 h611 hnatural.2.2.2.1)
    g hBA hnon

end CFSG.Quasithin.Chapter12.Section02.RankOneModule
