module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalTrialityCentralizerBounds
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalTrialityOuterInvolution

/-!
# Triality involution centralizer bounds in the literal Chapter 12 setup

The actual arms trace character gives a subgroup of order q^8 centralizing
the marked short root. The long root centralizes the whole original S,
of order q^12. The two compatible parabolic maps and ambient involution
fusion therefore give a q^8 lower bound for every Sylow two-subgroup of
every involution centralizer, without S=T or a parity assumption.

This supplies the lower bound in the F.4.38 outer-involution contradiction.
The fixed-root upper bound and ambient Sylow placement in F.4.37 remain
with the generic-global assembly, as do the final comparison and recognition.

Source: Aschbacher–Smith F.4.35, F.4.37–38, pp.292–294, and
5.3.3, p.659 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Triality.Standard Triality.Standard.Parabolics
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- The same right-parabolic marking gives q^12 for the long-root
centralizer in S and a q^8 lower bound for the short-root centralizer. -/
theorem rankOne_global_triality_marked_source_centralizer_bounds
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (m : ℕ) (hm : 0<m)
    (e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (ChapterF.GreenBook.LieModels.Triality.amalgam (binaryParameters m hm)).reverse) :
    let P := binaryParameters m hm
    let z : G := (e.right.symm (Global.TrialityCompletionFusion.longElement P rfl)).val
    let v : G := (e.right.symm (Global.TrialityCompletionFusion.shortElement P rfl)).val
    Nat.card (Global.sourceS L H ⊓ centralizer ({z} : Set G) : Subgroup G)=P.q^12 ∧
      P.q^8 ≤ Nat.card (Global.sourceS L H ⊓ centralizer ({v} : Set G) : Subgroup G) :=
  d.triality_marked_source_centralizer_bounds (D.rankOne_generic_input_of_many h hmany hn hpsl)
    hH.1.1.2 m hm e

/-- Every ambient involution centralizer has Sylow two-subgroups of order
at least q^8, retaining both compatible orientations and all degrees. -/
theorem rankOne_global_triality_involution_centralizer_sylow_lower_bound
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 0<m)
    (he : Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
        (ChapterF.GreenBook.LieModels.Triality.amalgam (binaryParameters m hm))) ∨
      Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
        (ChapterF.GreenBook.LieModels.Triality.amalgam (binaryParameters m hm)).reverse))
    (x : G) (hx : orderOf x=2) (R : Sylow 2 (centralizer ({x} : Set G))) :
    (binaryParameters m hm).q^8 ≤ Nat.card R :=
  d.triality_involution_centralizer_sylow_lower_bound (D.rankOne_generic_input_of_many h hmany hn hpsl)
    hH hp m hm he x hx R

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
