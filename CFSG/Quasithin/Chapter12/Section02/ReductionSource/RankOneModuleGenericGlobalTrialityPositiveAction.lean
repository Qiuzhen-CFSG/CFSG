module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalTrialityPositiveAction
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGeneric


/-!
# The whole triality positive action for the literal Chapter 12 pair

The original compatible parabolic maps give one common field coefficient
on both signed simple-root pairs. The six positive root factors then give
an actual torus--coefficient action on the whole original S. This proves
|C_S(t)| ≤ q^6 and |C_T(t)| < q^7 for an outer marked-torus involution,
including q=4, with no additional local-action or full-carrier-extension
premise. Both original overlap squares and the source definition of S remain.

Ambient centralizer Sylow placement is still needed for S=T. Preparation,
original uniqueness, exhaustive comparison and final GlobalExit retain their
assembly obligations. Source: Aschbacher--Smith F.4.37--38, printed
pp.293--294, and 5.3.3, p.659 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Triality.Standard Triality.Standard.Parabolics Triality.Standard.ConcreteBruhat
open Triality.Standard.OuterOdd Triality.Standard.OuterOdd.Coverage
open Triality.Standard.OuterOdd.Coverage.ParameterRigidity
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric Global.TrialityLocalParameters
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- Both original signed-root pairs use the same cubic coefficient. -/
theorem rankOne_global_triality_outer_common_signed_root_action
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1<n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H∈Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B E : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H))
    (m : ℕ) (hm : 0<m)
    (e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (ChapterF.GreenBook.LieModels.Triality.amalgam (binaryParameters m hm)).reverse)
    (hE : E ≤ ChapterF.Source.commonBorel ![L,residual H] (Global.sourceS L H))
    (hmark : ∀ b : (ChapterF.Source.parabolic ![L,residual H] (Global.sourceS L H) 0 ⊓
        ChapterF.Source.parabolic ![L,residual H] (Global.sourceS L H) 1 : Subgroup G),
        b.val∈E ↔ (e.middle b).val∈torus (binaryParameters m hm))
    (t : T) (ht2 : orderOf t=2) (htS : t.val∉Global.sourceS L H)
    (htE : t.val∈normalizer (E : Set G)) :
    ∃ (c : (fixedField (binaryParameters m hm))ˣ)
      (v : (ExtensionField (binaryParameters m hm))ˣ)
      (σ : CoefficientAut (binaryParameters m hm)),
      orderOf σ=2 ∧ v.val*σ v.val=1 ∧
      (∀ s r, t.val*(e.left.symm (rootInParabolic (binaryParameters m hm) rfl s .central r)).val*t.val⁻¹=
        (e.left.symm (rootInParabolic (binaryParameters m hm) rfl s .central
          (signedScalar s c.val*coefficientFixedField (binaryParameters m hm) σ r))).val) ∧
      (∀ s r, t.val*(e.right.symm (rootInParabolic (binaryParameters m hm) rfl s .arms r)).val*t.val⁻¹=
        (e.right.symm (rootInParabolic (binaryParameters m hm) rfl s .arms
          (signedScalar s v.val*σ r))).val) :=
  d.triality_outer_common_signed_root_action
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH.1.1.2 hp m hm e hE hmark t ht2 htS htE

/-- The original right-parabolic map identifies the entire positive action. -/
theorem rankOne_global_triality_outer_torus_coefficient_action
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1<n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H∈Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B E : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H))
    (m : ℕ) (hm : 0<m)
    (e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (ChapterF.GreenBook.LieModels.Triality.amalgam (binaryParameters m hm)).reverse)
    (hE : E ≤ ChapterF.Source.commonBorel ![L,residual H] (Global.sourceS L H))
    (hmark : ∀ b : (ChapterF.Source.parabolic ![L,residual H] (Global.sourceS L H) 0 ⊓
        ChapterF.Source.parabolic ![L,residual H] (Global.sourceS L H) 1 : Subgroup G),
        b.val∈E ↔ (e.middle b).val∈torus (binaryParameters m hm))
    (t : T) (ht2 : orderOf t=2) (htS : t.val∉Global.sourceS L H)
    (htE : t.val∈normalizer (E : Set G)) :
    ∃ (g : torus (binaryParameters m hm)) (σ : CoefficientAut (binaryParameters m hm)),
      orderOf σ=2 ∧
      let gP : parabolic (binaryParameters m hm) .arms := inclusion
        ((torus_le_borel _).trans (borel_le_parabolic _ .arms)) g
      ∀ x : parabolic (binaryParameters m hm) .arms,
        x.val∈unipotent (binaryParameters m hm) →
          t.val*(e.right.symm x).val*t.val⁻¹=
            (e.right.symm (gP*coefficientParabolic (binaryParameters m hm) σ .arms x*gP⁻¹)).val :=
  d.triality_outer_torus_coefficient_action
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH.1.1.2 hp m hm e hE hmark t ht2 htS htE

/-- The literal outer involution satisfies the bounds with no extra action premise. -/
theorem rankOne_global_triality_outer_involution_centralizer_lt
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1<n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H∈Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B E : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H))
    (m : ℕ) (hm : 0<m)
    (e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (ChapterF.GreenBook.LieModels.Triality.amalgam (binaryParameters m hm)).reverse)
    (hE : E ≤ ChapterF.Source.commonBorel ![L,residual H] (Global.sourceS L H))
    (hmark : ∀ b : (ChapterF.Source.parabolic ![L,residual H] (Global.sourceS L H) 0 ⊓
        ChapterF.Source.parabolic ![L,residual H] (Global.sourceS L H) 1 : Subgroup G),
        b.val∈E ↔ (e.middle b).val∈torus (binaryParameters m hm))
    (t : T) (ht2 : orderOf t=2) (htS : t.val∉Global.sourceS L H)
    (htE : t.val∈normalizer (E : Set G)) :
    Nat.card (Global.sourceS L H ⊓ centralizer ({t.val} : Set G) : Subgroup G) ≤ (binaryParameters m hm).q^6 ∧
      Nat.card ((T : Subgroup G) ⊓ centralizer ({t.val} : Set G) : Subgroup G) < (binaryParameters m hm).q^7 :=
  d.triality_outer_involution_centralizer_lt
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH.1.1.2 hp m hm e hE hmark t ht2 htS htE

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
