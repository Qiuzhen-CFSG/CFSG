module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalTrialityShortCentralizer.Faithful
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGeneric

/-!
# The faithful triality plane action in Chapter 12

The original comparison identifies the characteristic plane in O₂(L)
with the native long-root plane. The central PSL₂(q) acts faithfully,
with its exact ambient conjugation equation. The chosen-module hypotheses
supply m=n>1, so the smallest prepared case q=4 is included.

Source: Aschbacher--Smith F.4.42, printed p.295, applied in 5.3.3,
printed p.659 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Triality.Standard Triality.Standard.Parabolics
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric Chapter6.Source.RankOneGeneric.Global
open _root_.Triality.Standard.ShortRootCentralizer
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- Faithful conjugation on the characteristic plane for the literal row. -/
theorem rankOne_global_triality_short_plane_faithful_psl2
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 0 < m)
    (e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (ChapterF.GreenBook.LieModels.Triality.amalgam (binaryParameters m hm)).reverse) :
    let P := binaryParameters m hm
    let f := (ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0).subtype.comp
      e.left.symm.toMonoidHom
    TrialityShortAction.plane f = (center (L.pCoreIn 2)).map (L.pCoreIn 2).subtype ∧
    ∃ k : plane P ≃* TrialityShortAction.plane f,
      ∃ ρ : PSL(2,GaloisField P.prime P.exponent) →* MulAut (TrialityShortAction.plane f),
        Function.Injective ρ ∧
        (∀ v, (k v).val = f ⟨v.val,
          radical_le_parabolic P .central (plane_le_radical P v.property)⟩) ∧
        (∀ a : levi P .central, ∀ v : plane P,
          (ρ (leviCentralEquivPSL2 P rfl a) (k v)).val =
            f ⟨a.val,levi_le_parabolic P .central a.property⟩ * (k v).val *
              (f ⟨a.val,levi_le_parabolic P .central a.property⟩)⁻¹) :=
  d.triality_short_plane_faithful_psl2
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp m hm e

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
