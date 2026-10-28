module
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.ComponentSylowFour
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.ModuleAbsorption
public import Theory.SpecificGroups.PSL3Even.CubicFourNormalizer.Equiv
public import Theory.AtlasPort.ExceptionalIsomorphisms.Elementary
/-!
# The paired-cubic even linear component screen

The actual first four-group is absorbed into the centerless component. Its
intrinsic Sylow intersection lies in the source Thompson subgroup, so it
normalizes that four-group. The source conjugate makes it noncentral, and
the upper-unitriangular normal-four calculation forces the coefficient field
to have two elements. Field transport then identifies the original component.

Source: Aschbacher–Smith, 2.4.32, printed p.547. The original marked action
and common Sylow are retained throughout; no model normalizer premise remains.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter2.DoubleA3
open ChapterC ChapterC.Section05.BlockAnalysis ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}
variable {d : MinimalBlockSetup M} {T : Sylow 2 G} {c : SourcePairCoordinates d T}

theorem SourceCentralizerGeometry.psl3_even_binary
    (g : SourceCentralizerGeometry c) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (h : Chapter1.Lemma115Hypotheses (involutionCentralizer g.z₂) g.P₂ M (g.z₁*g.z₂))
    (K : Subgroup (involutionCentralizer g.z₂))
    (hK : IsComponent (involutionCentralizer g.z₂) K)
    (α : MulAut K)
    (hα : ∀ k : K, ((α k : involutionCentralizer g.z₂) : G) =
      (g.z₁*g.z₂)*(k:G)*(g.z₁*g.z₂)⁻¹)
    (hinner : α ∈ (MulAut.conj : K →* MulAut K).range)
    (hmodel : ∃ f : ℕ, 0 < f ∧ ClassicalGroup.IsPSL K 3 (2^f)) :
    Nonempty (K ≃* Matrix.PSL3Two.PSL) := by
  obtain ⟨n,hn,F,_,_,hF,⟨e⟩⟩ := hmodel
  have hzF : center PSL(3,F) = ⊥ := by
    let : Group.IsPerfect SL(3,F) := Atlas.sl_perfect 3 (by decide)
    exact Group.IsPerfect.center_quotient_center_eq_bot SL(3,F)
  have hzK : center K = ⊥ := by
    apply (center K).eq_bot_iff_card.mpr
    rw [Nat.card_congr (centerCongr e).toEquiv,hzF,card_bot]
  have hU := g.first_module_le_component hG h K hK α hα hinner hzK
  let : K.Normal := g.component_normal_of_first_module h K hK hU
  obtain ⟨P,hP,hUE,hcard,hUP,hPN,hcent⟩ := g.component_sylow_normal_four K hzK hU
  exact Matrix.PSL3Even.CubicFourNormalizer.binary_model_of_equiv_sylow_normal_four
    F hn hF e P _ hcard hUP hPN hcent
end CFSG.Quasithin.Chapter2.DoubleA3
