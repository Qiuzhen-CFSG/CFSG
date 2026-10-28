module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitarySource.InnerSylow
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFullNormalizer.FourCompletion

/-!
# Unconditional prepared U₄ source input

The actual prepared comparison first rules out the degree-two amalgam. The
ordinary quotient identifies every Sylow involution fixing the right-residual
center with an inner automorphism on the local SL₂ quotient. The long-root
centralization theorem supplies that fixed-center condition, and the resulting
Sylow equality makes the full extension's outer index odd. Thompson's
two-involution-class formula then gives the ambient order equality on that
same full extension. The existing completion and recognition theorems consume
this source input without changing either parabolic or the marked overlap.

This closes the ambient U₄ transfer and order steps of Aschbacher–Smith
5.3.2–4 and F.4.35–43, printed pp.658–659 and292–296 of `refs/quasithin.pdf`.
The U₅ source row is separate.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.LieModels.UnitaryFour
open ChapterF.SourceCompletion.UnitaryNonbinary UnitaryCompletion
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W H A C : Subgroup G} {n : ℕ}
variable (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 1 ≤ m)
    (hc : FourLocalComparison L (residual H) (sourceS L H) m hm)
include d h hH hp hc

/-- The genuine full-normalizer extension has its original marked maps and
ambient order bound, with no extension, fusion, or order premise left over. -/
theorem Preparation.unitaryFour_source :
    ∃ E : FourExtension m hm, Compatible L (residual H) E ∧
      Nat.card G ≤ Nat.card E.carrier := by
  let r := d.unitaryFourNormalizerMarking h hH hp m hm hc
  have hs := d.unitaryFour_sylow_eq_inner h hH hp m hm hc
  have horder := d.unitaryFour_order_of_inner_sylow h hH hp m hm hc hs r
  exact ⟨r.extension,r.full_comparison,horder.le⟩

/-- The same constructed extension supplies the literal completion input,
including the whole normalizer overlap and both native coset bounds. -/
theorem Preparation.unitaryFour_completion :
    let E := (d.unitaryFourNormalizerMarking h hH hp m hm hc).extension
    1 < m ∧ n = 2*m ∧
      ∃ c : RankTwoAmalgam.FaithfulCompletion E.amalgam
          (G := NormalizerJoin L (residual H)),
        c.left.range ⊓ c.right.range = c.middle.range ∧
        Nat.card (NormalizerJoin L (residual H)) ≤ Nat.card E.carrier ∧
        ∀ i : Bool, Nat.card (NormalizerJoin L (residual H) ⧸ c.cosetFamily i) ≤
          Nat.card (ProjectiveGroup m hm ⧸ SourceExtension.nativeFamily
            (P₀ := pointParabolic m hm) (P₁ := planeParabolic m hm) i) := by
  let r := d.unitaryFourNormalizerMarking h hH hp m hm hc
  have hs := d.unitaryFour_sylow_eq_inner h hH hp m hm hc
  have horder := d.unitaryFour_order_of_inner_sylow h hH hp m hm hc hs r
  exact d.unitaryFour_constructed_completion h hH hp m hm hc horder.le

/-- The prepared unitary-four branch is recognized unconditionally at its
original exponent, for either comparison orientation and q = 4. -/
theorem Preparation.unitaryFour_recognition :
    1 < m ∧ n = 2*m ∧ Nat.card G = Nat.card
      (d.unitaryFourNormalizerMarking h hH hp m hm hc).extension.carrier ∧
      ClassicalGroup.IsPSU G 4 (2^m) := by
  let r := d.unitaryFourNormalizerMarking h hH hp m hm hc
  have hs := d.unitaryFour_sylow_eq_inner h hH hp m hm hc
  have horder := d.unitaryFour_order_of_inner_sylow h hH hp m hm hc hs r
  exact d.unitaryFour_constructed_recognition h hH hp m hm hc horder.le

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
