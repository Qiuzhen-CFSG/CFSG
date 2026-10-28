module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalReeCompletion.InvolutionReduction
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalReeCompletion.Fusion

/-!
# Reduced Ree involution words in the original Chapter12 pair

The chosen-module hypotheses supply the original prepared input. On the
same full common-normalizer marking, every involution has a positive native
image with vanishing first Suzuki main coordinate. Thus every ambient
involution has an original-T representative whose native image is the
central first-root curve times the literal Suzuki radical factor.

The reduction keeps the actual quotient, both comparison orientations and
the original equation 2m+1=n. It is not native two-class exhaustion, converse
fusion, ambient recognition, or GlobalExit: those remain source obligations.
Source: Aschbacher–Smith 5.3.1–3, F.4.27,35 and 12.2.2,
printed pp.658–659,288,291–292,795 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.GreenBook.LieModels
open ReeF4.NormalizedRootCentralizers.CenterExponent
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- The literal whole-overlap map has reduced native coordinates on each involution. -/
theorem rankOne_global_ree_middle_involution_normal_form
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H)) (m : ℕ)
    (R : Global.ReeNormalizerMarking L (residual H) (Global.sourceS L H) m)
    (y : (normalizer (L : Set G) ⊓ normalizer (residual H : Set G) : Subgroup G))
    (hy : orderOf y.val = 2) :
    ∃ (t : ReeF4.Model m) (p : PositiveParameters m)
      (r : ReeF4.Parabolics.radical m .suzuki),
      orderOf t = 2 ∧ t ∈ ReeF4.Parabolics.unipotent m ∧
      R.middleToCarrier y = R.extension.baseHom t ∧
      p.main 0 = 0 ∧ ReeF4.toSplitGroup m t = positiveWord m p ∧
      t = ReeF4.ElementaryTwoBound.centralElement m 0 (p.central 0) * r.val :=
  d.ree_middle_involution_normal_form
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hp m R y hy

/-- Both source orientations yield the original-T representatives with their
reduced native word, preserving the same full marking and original degree. -/
theorem rankOne_global_ree_full_extension_involution_normal_forms
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H)) (m : ℕ)
    (he : Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H)) (ReeFour.amalgam m)) ∨
      Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H)) (ReeFour.amalgam m).reverse)) :
    2*m+1 = n ∧ 0 < m ∧
    ∃ R : Global.ReeNormalizerMarking L (residual H) (Global.sourceS L H) m,
      ∀ x : G, orderOf x = 2 →
        ∃ (y : (normalizer (L : Set G) ⊓ normalizer (residual H : Set G) : Subgroup G))
          (t : ReeF4.Model m) (p : PositiveParameters m)
          (r : ReeF4.Parabolics.radical m .suzuki),
          y.val ∈ (T : Subgroup G) ∧ IsConj x y.val ∧
          orderOf t = 2 ∧ t ∈ ReeF4.Parabolics.unipotent m ∧
          R.middleToCarrier y = R.extension.baseHom t ∧
          p.main 0 = 0 ∧ ReeF4.toSplitGroup m t = positiveWord m p ∧
          t = ReeF4.ElementaryTwoBound.centralElement m 0 (p.central 0) * r.val :=
  d.ree_full_extension_involution_normal_forms
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hp m hH he

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
