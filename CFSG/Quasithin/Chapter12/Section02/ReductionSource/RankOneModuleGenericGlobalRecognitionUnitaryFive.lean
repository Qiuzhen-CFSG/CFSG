module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalRecognitionUnitaryFive
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalRecognitionBlocks

/-!
# The special U₅(4) row in the original Chapter12 pair

The actual line parabolic has special SU₃(4) residual quotient, so it
cannot be either binary PSL₂ endpoint of a diagram-selected pair. Both
compatible amalgam orientations are therefore excluded in that branch.
For the whole-residual branch the surviving orientation is retained:
it forces the original n = 4 and identifies the literal L and R with
the plane and line residuals, with all canonical core and special-center
clauses. No ambient U₅(4) isomorphism is inferred from local comparison.

Original uniqueness and the F.1.12 bound retain their independent discharge;
exhaustive recognition and ambient completion stay with
qt-d-1222-rankone-generic-global. The final consumers are
qt-d-1222-rankone-generic and qt-d-1361-source.
Source: Aschbacher–Smith 5.2.6(7), pp.650–651, F.1.12(I)(7), p.263,
and the Chapter12 application on p.795 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.GreenBook.UnitaryFive
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- The source selector retains the whole-residual branch, including U₅(4),
while excluding both actual U₅(4) amalgams for the diagram factor. -/
theorem rankOne_global_residual_or_unitaryFive_exclusions_of_core_bound
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
        ¬ ChapterC.IsShort R ∧ ∀ M : Model 4,
          let α := Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)
          ¬ Nonempty (RankTwoAmalgam.Iso α M.amalgam) ∧
            ¬ Nonempty (RankTwoAmalgam.Iso α M.amalgam.reverse)) := by
  obtain ⟨A,B,R,d,hp,hr⟩ := D.rankOne_global_residual_or_diagram_obstructions_of_core_bound
    h hmany hn hpsl hH hpar hthree hN hunique hcore
  refine ⟨A,B,R,d,hp,?_⟩
  rcases hr with he | ⟨⟨f,hf,hlin⟩,hnot,_⟩
  · exact Or.inl he
  · refine Or.inr ⟨⟨f,hf,hlin⟩,hnot,?_⟩
    intro M
    exact d.not_unitaryFive_amalgams (D.rankOne_generic_input_of_many h hmany hn hpsl)
      hH.1.1.2 hp hlin M

/-- An actual surviving U₅(4) comparison on the original prepared pair
forces n = 4 and the source's complete local core structure. -/
theorem rankOne_global_unitaryFive_local_structure
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B R : Subgroup G} (d : Global.Preparation T L H A B R) (hp : Group.IsPerfect R)
    (M : Model 4) (e : RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) M.amalgam.reverse) :
    n = 4 ∧ Nonempty (L ≃* M.rightLocalImage) ∧ Nonempty (R ≃* M.leftLocalImage) ∧
      ChapterF.Source.IsSU (R ⧸ pCore 2 R) 3 4 ∧
      Nat.card (pCore 2 L) = 2^16 ∧ Nat.card (pCore 2 R) = 4^7 ∧
      Nat.card (center (pCore 2 R)) = 4 ∧
      center (pCore 2 R) = commutator (pCore 2 R) ∧
      center (pCore 2 R) = frattini (pCore 2 R) :=
  d.unitaryFive_local_structure (D.rankOne_generic_input_of_many h hmany hn hpsl)
    hH.1.1.2 hp M e

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
