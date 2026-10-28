module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalTrialityLocalSylow
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGeneric

/-!
# Triality local Sylow placement for the literal Chapter 12 pair

The marked torus involution fixes an element of the original S outside
O₂(O²(H)), constructed on the genuine cubic-field root. The PSL₂(q³)
quotient then determines S uniquely among local Sylow two-subgroups.
Together with the original cyclic torus complement, this proves that
C_T(t) is Sylow in N_G(O²(H)) intersect C_G(t).

This is local Sylow placement, not yet Sylow placement in the full ambient
centralizer. The F.4.37 fixed-subgroup geometry, the full torus--coefficient
action identity, S=T, and triality recognition remain assembly obligations.
Original uniqueness and exhaustive compatible comparison are also retained.

Source: Aschbacher--Smith F.4.37--38, pp.293--294, and 5.3.3, p.659
(`refs/quasithin.pdf`). All maps are the original whole-overlap comparison.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Triality.Standard Triality.Standard.Parabolics Triality.Standard.ConcreteBruhat
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- The literal chosen-module hypotheses give local Sylow placement for the
original marked torus involution, at every exponent n>1. -/
theorem rankOne_global_triality_outer_centralizer_local_sylow
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
    (t : T) (ht2 : orderOf t=2) (htE : t.val∈normalizer (E : Set G)) :
    let C := normalizer (residual H : Set G) ⊓ centralizer ({t.val} : Set G)
    ∃ P : Sylow 2 C, (P : Subgroup C).map C.subtype=
      (T : Subgroup G) ⊓ centralizer ({t.val} : Set G) :=
  d.triality_outer_centralizer_local_sylow
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH.1.1.2 hp m hm e hE hmark t ht2 htE

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
