module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalReeCompletion.FullNormalizer
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalReeCompletion.NativeAction

/-!
# The original Chapter12 Ree full-normalizer diagram

The prepared whole-residual comparison constructs the actual native extension
and a compatible isomorphism on both full normalizers and their literal
intersection. Both endpoint markings and the entire pure Borel are retained.
No extension or realization premise is added to the original Chapter12 inputs.
The ambient order comparison for this same carrier, and hence GlobalExit,
remain further source obligations.

Source: Aschbacher–Smith 5.3.1–2, F.4.3 and 12.2.2,
printed pp.658–659,274,795 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.GreenBook.LieModels
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- The original chosen Ree pair supplies the simultaneous full-normalizer
extension and all three pure markings at every positive native parameter. -/
theorem rankOne_global_ree_full_normalizer_marking
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
      Nonempty (Global.ReeNormalizerMarking L (residual H) (Global.sourceS L H) m) := by
  exact d.ree_full_normalizer_marking
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp m he

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
