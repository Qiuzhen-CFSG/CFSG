module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalReeCompletion.Recognition
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalReeCompletion.ShortAmbient

/-!
# The prepared Chapter12 general Ree branch

The original whole-residual comparison constructs one compatible full-normalizer
extension. Proved involution exhaustion and full endpoint fusion discharge the
short-centralizer family's earlier-source premises. Thompson's formula then
compares the entire ambient group with that same extension; its actual marked
Weyl relation and original simplicity identify G with ReeF4.Model m.

The native general Ree output uses the SAME original degree n=2m+1 and retains
all m>0, including q=8, both input orientations and the whole overlap. No extra
centralizer, generation, order or recognition hypothesis remains. Exhaustive
comparison selection and construction of the original preparation remain with
the generic-global assembly.
Source: Aschbacher--Smith F.4.42--44, printed pp.295--296, 5.3.1--4,
printed pp.658--659, and the Chapter12 application on p.795 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.GreenBook.LieModels
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- Original chosen-module inputs identify the actual ambient group with the
native general Ree carrier at the original field degree. -/
theorem rankOne_global_ree_ambient_recognition
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
    2*m+1 = n ∧ 0 < m ∧ Nonempty (G ≃* ReeF4.Model m) := by
  exact d.ree_ambient_recognition
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp m he

/-- The actual prepared general Ree comparison gives the strict rank-two
GlobalExit, with no additional local or recognition premise. -/
theorem rankOne_globalExit_of_ree_comparison
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
    RankOneModule.GlobalExit G := by
  obtain ⟨hmn,hm,hiso⟩ := D.rankOne_global_ree_ambient_recognition h hmany hn hpsl hH d hp m he
  exact Or.inl ⟨n,hn,ClassificationModels.IsRankTwoModel.ree_f4 m (by omega) hmn.symm hiso⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
