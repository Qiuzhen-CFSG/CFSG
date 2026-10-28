module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalTrialityLocalParameters
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGeneric

/-!
# The cubic-root field involution for the literal Chapter 12 pair

The original right-parabolic map gives scalar-semilinear formulas on both
signed cubic roots, with the same coefficient and reciprocal scalars. The
source quotient action proves the coefficient has order two whenever the
marked torus involution lies outside the original S. This includes field four
and does not assume a full-carrier automorphism extension.

The action on the other roots and the ambient F.4.37 Sylow placement are
still needed for S=T and triality recognition. Original preparation,
uniqueness, exhaustive comparison and final GlobalExit remain assembly duties.
Source: Aschbacher--Smith F.4.37--38, printed pp.293--294, and 5.3.3,
p.659 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Triality.Standard Triality.Standard.Parabolics Triality.Standard.ConcreteBruhat
open Triality.Standard.OuterOdd.Coverage.ParameterRigidity
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric Global.TrialityLocalParameters
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- Both cubic-root signs carry the same nontrivial field involution through
the original comparison map, with reciprocal root scalars. -/
theorem rankOne_global_triality_outer_signed_root_action
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
    ∃ (c : (ExtensionField (binaryParameters m hm))ˣ)
      (σ : ExtensionField (binaryParameters m hm) ≃+* ExtensionField (binaryParameters m hm)),
      orderOf σ=2 ∧ c.val*σ c.val=1 ∧
      ∀ s r, t.val*(e.right.symm (rootInParabolic (binaryParameters m hm) rfl s .arms r)).val*t.val⁻¹=
        (e.right.symm (rootInParabolic (binaryParameters m hm) rfl s .arms (signedScalar s c.val*σ r))).val :=
  d.triality_outer_signed_root_action
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH.1.1.2 hp m hm e hE hmark t ht2 htS htE

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
