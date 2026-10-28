module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalTrialityCompletionFusion
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalTrialityCoreKernel

/-!
# Triality involution classes in the literal Chapter 12 setup

The two actual parabolic maps transport every involution of the original
S = O₂(N_G(L) ∩ H) to a highest-long-root or marked-short-root class inside
L ∨ O²(H). The existing marked nonfusion separates these classes in G, and
cyclic quotient transfer puts every ambient involution into S. Thus the same
marked representatives cover exactly two ambient classes; the original factor
join already realizes ambient fusion between involutions of S.

This supplies the involution comparison used in the triality centralizer and
Thompson-order argument. Original uniqueness, exhaustive amalgam comparison,
S = T, and ambient model recognition remain assembly obligations.

Source: Aschbacher–Smith F.4.35, F.4.38 and F.4.43, printed pp.292,294,296,
and 5.3.3–4, p.659 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric Chapter6.Source.RankOneGeneric.Global
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- The two exact root markings give all ambient involution classes, at every original exponent n > 1. -/
theorem rankOne_global_triality_ambient_involution_classes
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    {A B : Subgroup G} (d : Preparation T L H A B (residual H))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 0<m)
    (he : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.Triality.amalgam (_root_.Triality.Standard.binaryParameters m hm))) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.Triality.amalgam (_root_.Triality.Standard.binaryParameters m hm)).reverse)) :
    ∃ e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.Triality.amalgam (_root_.Triality.Standard.binaryParameters m hm)).reverse,
      ∃ z v : (L ⊔ residual H : Subgroup G),
        z.val = (e.right.symm (TrialityCompletionFusion.longElement (_root_.Triality.Standard.binaryParameters m hm) rfl)).val ∧
        v.val = (e.right.symm (TrialityCompletionFusion.shortElement (_root_.Triality.Standard.binaryParameters m hm) rfl)).val ∧
        z.val ∈ (center (residual H)).map (residual H).subtype ∧
        orderOf z=2 ∧ orderOf v=2 ∧ ¬ IsConj z.val v.val ∧
        (∀ x : (L ⊔ residual H : Subgroup G), x.val∈sourceS L H → orderOf x=2 →
          IsConj z x ∨ IsConj v x) ∧
        (∀ x : G, orderOf x=2 → IsConj z.val x ∨ IsConj v.val x) :=
  d.triality_ambient_involution_classes
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp m hm he

/-- The original factor join realizes all ambient involution fusion within S. -/
theorem rankOne_global_triality_completion_controls_involution_fusion
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    {A B : Subgroup G} (d : Preparation T L H A B (residual H))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (m : ℕ) (hm : 0<m)
    (he : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.Triality.amalgam (_root_.Triality.Standard.binaryParameters m hm))) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.Triality.amalgam (_root_.Triality.Standard.binaryParameters m hm)).reverse))
    (x y : G) (hx : x∈sourceS L H) (hy : y∈sourceS L H)
    (hx2 : orderOf x=2) (hy2 : orderOf y=2) :
    IsConj x y ↔ ∃ g∈L⊔residual H, g*x*g⁻¹=y :=
  d.triality_completion_controls_involution_fusion
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp m hm he x y hx hy hx2 hy2

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
