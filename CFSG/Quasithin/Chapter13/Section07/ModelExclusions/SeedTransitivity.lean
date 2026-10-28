module
public import CFSG.Quasithin.Chapter13.Section07.ModelExclusions.PlaneOrbit
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Parabolic.Marking.Standing
public import Theory.GroupAction.FourPerfectOrbit
/-!
# The three original nonzero seed vectors form one point-residual orbit

The actual section V₃/V₁ has dimension two. Its L₁ action is nontrivial:
triviality would put [V₃,L₁]=V₃ inside V₁. Since L₁ is two-perfect, the
four-element action is transitive on the three nonzero vectors. This retains
the original conjugation quotient rather than choosing a new plane action.

Source: Aschbacher–Smith, proof of 13.7.6(3), printed p.939.
-/
@[expose] public section
open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section07.ModelExclusions
open Section08.SourceCompletion
open Section08.TransvectionRecognition
open Section08.TransvectionRecognition.Component.ModelExtension
open Section08.TransvectionParabolic.Marking
open Section08.TransvectionParabolic.Marking.CompatibleFlags
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
  [(V₁.subgroupOf (Section08.Source.UH H V₃)).Normal]
  [IsElementaryAbelian 2 (Section08.Source.Utilde H V₃ V₁)]
include d
/-- Every nonzero original seed-section vector is in the orbit of every other. -/
theorem seed_section_nonzero_orbit
    (hL₁H : sourceOne L T V₁ ≤ H)
    (ρ : Representation (ZMod 2) (Section08.Source.Hstar H)
      (Additive (Section08.Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (v : Additive (Section08.Source.Utilde H V₃ V₁))
    (hv : v ∈ sectionImage H V₃ V₁ V₃) (hv0 : v ≠ 0) :
    ∀ w ∈ sectionImage H V₃ V₁ V₃, w ≠ 0 →
      ∃ l : sourceOne L T V₁,
        ρ (QuotientGroup.mk' (pCore 2 H) (inclusion hL₁H l)) v = w := by
  let P := sectionImage H V₃ V₁ V₃
  let f := (QuotientGroup.mk' (pCore 2 H)).comp (inclusion hL₁H)
  let τ := ρ.comp f
  have hs (l : sourceOne L T V₁) : ∀ w ∈ P, τ l w ∈ P :=
    sectionImage_invariant ρ hρ V₃ (inclusion hL₁H l)
      (point_residual_normalizes_seed d l.property)
  let σ := Representation.subrepresentation τ P hs
  have hd : Module.finrank (ZMod 2) P = 2 :=
    sectionImage_seed_finrank (d.line_le_plane.trans d.plane_le_seed) d.line_card d.seed_card
  have hnontriv : ∃ l, σ l ≠ 1 := by
    by_contra ht
    push Not at ht
    have hc : ⁅V₃, sourceOne L T V₁⁆ ≤ V₁ := by
      apply commutator_le.mpr
      intro x hx l hl
      let u : Section08.Source.UH H V₃ := ⟨x, le_conjugateSpanBy V₃ H hx⟩
      have hu : vector H V₃ V₁ u ∈ P := ⟨u, hx, rfl⟩
      have hf := congrArg Subtype.val (LinearMap.congr_fun (ht ⟨l,hl⟩) ⟨_,hu⟩)
      change ρ (QuotientGroup.mk' (pCore 2 H) ⟨l, hL₁H hl⟩)
        (vector H V₃ V₁ u) = vector H V₃ V₁ u at hf
      have he := vector_commutator ρ hρ u ⟨l, hL₁H hl⟩
      rw [hf, sub_self] at he
      exact (QuotientGroup.eq_one_iff (N := V₁.subgroupOf (Section08.Source.UH H V₃)) _).mp he
    rw [seed_commutator_point_residual d] at hc
    have hcard := card_le_of_le hc
    rw [d.line_card, d.seed_card] at hcard
    omega
  have hp : IsPPerfect 2 (sourceOne L T V₁) :=
    isPPerfect_embedded_pResidual 2 ((L ⊔ (T : Subgroup G)) ⊓ normalizer (V₁ : Set G))
  intro w hw hw0
  obtain ⟨l, hl⟩ := Representation.nonzero_orbit_of_twoPerfect_plane hp hd σ hnontriv
    (⟨v,hv⟩ : P) (fun h => hv0 (congrArg Subtype.val h))
    (⟨w,hw⟩ : P) (fun h => hw0 (congrArg Subtype.val h))
  exact ⟨l, congrArg Subtype.val hl⟩
end CFSG.Quasithin.Chapter13.Section07.ModelExclusions
