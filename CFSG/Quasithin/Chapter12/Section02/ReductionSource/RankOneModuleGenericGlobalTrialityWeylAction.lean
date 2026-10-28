module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalTrialityWeylAction
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGeneric

/-!
# Triality Weyl actions in the literal Chapter 12 setup

The original Sylow actor normalizing the marked Hall torus sends each of the
two genuine local Weyl involutions into its torus coset. Both equations use
the original compatible parabolic maps and their whole-overlap marking.
The model proof uses uniqueness of the Bruhat form and the nonbinary torus
weights; its exponent restriction follows from the original left field.

These are local Weyl constraints for constructing the torus--coefficient
root action. That construction, ambient centralizer Sylow placement, and
triality completion recognition remain obligations of the generic assembly.

Source: Aschbacher--Smith F.4.29, F.4.37--38, pp.289,293--294, and
5.3.3, p.659 (`refs/quasithin.pdf`); GLS3 2.3.4--8 and §2.4.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Triality.Standard Triality.Standard.Parabolics Triality.Standard.ConcreteBruhat
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- Both marked Weyl involutions retain their torus cosets under the original
actor, with the two source parabolic maps and the whole overlap unchanged. -/
theorem rankOne_global_triality_torus_normalizer_weyl_action
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B E : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H))
    (m : ℕ) (hm : 0<m)
    (e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (ChapterF.GreenBook.LieModels.Triality.amalgam (binaryParameters m hm)).reverse)
    (hE : E ≤ ChapterF.Source.commonBorel ![L,residual H] (Global.sourceS L H))
    (hmark : ∀ b : (ChapterF.Source.parabolic ![L,residual H] (Global.sourceS L H) 0 ⊓
        ChapterF.Source.parabolic ![L,residual H] (Global.sourceS L H) 1 : Subgroup G),
        b.val ∈ E ↔ (e.middle b).val ∈ torus (binaryParameters m hm))
    (t : T) (htE : t.val ∈ normalizer (E : Set G)) :
    ∃ w₀ : ChapterF.Source.parabolic ![L,residual H] (Global.sourceS L H) 0,
    ∃ w₁ : ChapterF.Source.parabolic ![L,residual H] (Global.sourceS L H) 1,
    (e.left w₀).val = simpleRepresentative (binaryParameters m hm) rfl .central ∧
    (e.right w₁).val = simpleRepresentative (binaryParameters m hm) rfl .arms ∧
    (∃ u ∈ E, t.val*w₀.val*t.val⁻¹ = u*w₀.val) ∧
    (∃ u ∈ E, t.val*w₁.val*t.val⁻¹ = u*w₁.val) :=
  d.triality_torus_normalizer_weyl_action
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH.1.1.2 hp m hm e
    hE hmark t htE

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
