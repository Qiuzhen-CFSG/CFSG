module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalTrialityOuterFixed
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalTrialityCentralizerBounds

/-!
# The triality fixed-root estimate in the literal Chapter 12 setup

The actual torus--coefficient action on the three cubic-field and three
base-field root parameters has at most q^6 fixed points. Transport through
the original right parabolic map and the already proved [T:S] < q bound
give |C_T(t)| < q^7, without identifying S with T.

The local action identity remains explicit. Producing it from the compatible
parabolic automorphisms, proving ambient Sylow placement, and completing
triality recognition remain obligations of the generic-global assembly.

Source: Aschbacher--Smith F.4.37--38, pp.293--294, and 5.3.3, p.659
(`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Triality.Standard Triality.Standard.Parabolics Triality.Standard.OuterOdd
open Triality.Standard.ConcreteBruhat
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- The actual local action supplies the q^6 fixed-root estimate and the strict
q^7 bound in the original Sylow subgroup. No ambient Sylow placement is assumed. -/
theorem rankOne_global_triality_outer_centralizer_lt_of_torus_coefficient_action
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B E : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 0<m)
    (e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (ChapterF.GreenBook.LieModels.Triality.amalgam (binaryParameters m hm)).reverse)
    (hE : E ≤ ChapterF.Source.commonBorel ![L,residual H] (Global.sourceS L H))
    (hmark : ∀ b : (ChapterF.Source.parabolic ![L,residual H] (Global.sourceS L H) 0 ⊓
        ChapterF.Source.parabolic ![L,residual H] (Global.sourceS L H) 1 : Subgroup G),
        b.val ∈ E ↔ (e.middle b).val ∈ torus (binaryParameters m hm))
    (t : T) (htE : t.val ∈ normalizer (E : Set G))
    (g : torus (binaryParameters m hm))
    (σ : CoefficientAut (binaryParameters m hm)) (hσ : orderOf σ=2)
    (hact : let P := binaryParameters m hm
      let gP : parabolic P .arms := inclusion ((torus_le_borel P).trans (borel_le_parabolic P .arms)) g
      ∀ x : parabolic P .arms, x.val ∈ unipotent P →
        t.val * (e.right.symm x).val * t.val⁻¹ =
          (e.right.symm (gP * coefficientParabolic P σ .arms x * gP⁻¹)).val) :
    Nat.card (Global.sourceS L H ⊓ centralizer ({t.val} : Set G) : Subgroup G) ≤ (binaryParameters m hm).q^6 ∧
      Nat.card ((T : Subgroup G) ⊓ centralizer ({t.val} : Set G) : Subgroup G) < (binaryParameters m hm).q^7 :=
  d.triality_outer_centralizer_lt_of_torus_coefficient_action
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH.1.1.2 hp m hm e
    hE hmark t htE g σ hσ hact

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
