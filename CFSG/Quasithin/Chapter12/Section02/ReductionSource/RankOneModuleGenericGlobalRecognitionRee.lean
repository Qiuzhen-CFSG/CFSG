module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalRecognitionRee
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalRecognitionUnitaryFive

/-!
# The actual Ree comparison in the Chapter12 generic pair

The selected diagram factor has binary PSL₂ quotient, excluding both Ree
amalgam orientations. The whole-residual branch remains: its surviving
orientation identifies the original L and R with the linear and Suzuki
root factors at n = 2m+1, with m positive and core orders q^11 and q^10.
The full overlap, including the odd Cartans, is retained throughout.

This discharges the Ree comparison in 5.2.6, not exhaustive classification
or ambient completion. Those steps and the F.1.12 core bound remain with
qt-d-1222-rankone-generic-global. Original uniqueness retains its independent
producer, and final source discharge stays with qt-d-1222-rankone-generic
and qt-d-1361-source.

Source: Aschbacher–Smith 5.2.6(5), pp.650–651, F.1.12(I)(5), pp.262–264,
and the original Chapter12 application on p.795 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.GreenBook.LieModels
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- The same prepared pair retains the whole residual or excludes both Ree
orientations at every parameter, including the binary field. -/
theorem rankOne_global_residual_or_ree_exclusions_of_core_bound
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hpar : 1 < ChapterE.generationParameter H)
    (hthree : ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hN : localBorel T L ≤ normalizer (residual H : Set G))
    (hunique : ∀ X : Subgroup G, IsMaximalTwoLocal X → L ≤ X →
      X = normalizer (L : Set G))
    (hcore : ∀ A B R : Subgroup G, Global.Preparation T L H A B R →
      Group.IsPerfect R →
      (R.pCoreIn 2).relIndex ((R ⊔ Global.sourceS L H).pCoreIn 2) ≤ 2) :
    ∃ A B R : Subgroup G, Global.Preparation T L H A B R ∧ Group.IsPerfect R ∧
      (R = residual H ∨
        (∃ f : ℕ, 1 < f ∧ ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 (2^f)) ∧
        ¬ ChapterC.IsShort R ∧ ∀ m : ℕ,
          let α := Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)
          ¬ Nonempty (RankTwoAmalgam.Iso α (ReeFour.amalgam m)) ∧
            ¬ Nonempty (RankTwoAmalgam.Iso α (ReeFour.amalgam m).reverse)) := by
  obtain ⟨A,B,R,d,hp,hr⟩ := D.rankOne_global_residual_or_diagram_obstructions_of_core_bound
    h hmany hn hpsl hH hpar hthree hN hunique hcore
  refine ⟨A,B,R,d,hp,?_⟩
  rcases hr with he | ⟨⟨f,hf,hlin⟩,hnot,_⟩
  · exact Or.inl he
  · refine Or.inr ⟨⟨f,hf,hlin⟩,hnot,?_⟩
    intro m
    exact d.not_ree_amalgams (D.rankOne_generic_input_of_many h hmany hn hpsl)
      hH.1.1.2 hp hlin m

/-- The surviving actual Ree comparison fixes the original field and both
local factors and transports the intrinsic quotient and core-order clauses. -/
theorem rankOne_global_ree_local_structure
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B R : Subgroup G} (d : Global.Preparation T L H A B R) (hp : Group.IsPerfect R)
    (m : ℕ) (e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H))
      (ReeFour.amalgam m).reverse) :
    2*m+1 = n ∧ 0 < m ∧
      Nonempty (L ≃* ReeF4.Parabolics.localFactor m .linear) ∧
      Nonempty (R ≃* ReeF4.Parabolics.localFactor m .suzuki) ∧
      Nonempty ((R ⧸ pCore 2 R) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) ∧
      Nat.card (pCore 2 L) = (2^n)^11 ∧ Nat.card (pCore 2 R) = (2^n)^10 :=
  d.ree_local_structure (D.rankOne_generic_input_of_many h hmany hn hpsl)
    hH.1.1.2 hp m e

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
