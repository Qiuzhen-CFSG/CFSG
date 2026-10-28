module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalTrialityAmbientSylow
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGeneric

/-!
# Triality ambient Sylow placement for the literal Chapter 12 pair

The actual whole-overlap comparison and original Hall torus give ambient
Sylow placement for C_T(t), and hence the original S=O₂(N_G(L) ∩ H) equals T.
The fixed-root geometry, characteristic central-derived subgroup and
normalizer argument are discharged by the source companion. These statements
include q=4 and retain both original parabolic maps and covering kernels.

Source: Aschbacher--Smith F.4.37--38, printed pp.293--294, and 5.3.3,
p.659 (`refs/quasithin.pdf`). Full normalizer realization and order,
exhaustive concrete comparison and final GlobalExit remain assembly duties.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Triality.Standard Triality.Standard.Parabolics Triality.Standard.ConcreteBruhat
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- The original outer involution centralizer is Sylow in its full ambient centralizer. -/
theorem rankOne_global_triality_outer_centralizer_ambient_sylow
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
    let E := (T : Subgroup G) ⊓ centralizer ({t.val} : Set G)
    ∃ R : Sylow 2 (centralizer ({t.val} : Set G)),
      (R : Subgroup (centralizer ({t.val} : Set G))).map (centralizer ({t.val} : Set G)).subtype = E :=
  d.triality_outer_centralizer_ambient_sylow
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp m hm e hE hmark t ht2 htS htE

/-- F.4.38 for the actual Chapter 12 triality comparison, including q=4.
The original source core is all of the original ambient Sylow subgroup. -/
theorem rankOne_global_triality_sourceS_eq_sylow
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1<n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H∈Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 0<m)
    (he : Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
        (ChapterF.GreenBook.LieModels.Triality.amalgam (binaryParameters m hm))) ∨
      Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
        (ChapterF.GreenBook.LieModels.Triality.amalgam (binaryParameters m hm)).reverse)) :
    Global.sourceS L H = (T : Subgroup G) :=
  d.triality_sourceS_eq_sylow (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp m hm he

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
