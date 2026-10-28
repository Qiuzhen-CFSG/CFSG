module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalRecognitionExchanged
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalLocal

/-!
# Removing the exchanged right factor in the original Chapter 12 application

The source core-extension bound from 5.2.6 rules out the exchanged E.2.2
component: its second commuting component forces an extension of order at
least four. Thus the actual Bender right factor is the whole residual.
The marked diagram row remains separate and retains its scalar cover.

The bound is required only on the perfect prepared pairs to which F.1.12
applies. This task, qt-d-1222-rankone-generic-global, still owns its proof,
the diagram chief-factor exclusion and completion recognition. Original
uniqueness over L remains the input of qt-d-1222-rankone-global-uniqueness;
no uniqueness or recognition conclusion is inferred from this reduction.

Source: Aschbacher–Smith, 5.2.6, printed pp.650–651; the Chapter 12
application is on p.795 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- The original pair has right factor O²(H), unless the marked diagram
row occurs. Uniqueness and the F.1.12 core bound remain exact source premises. -/
theorem rankOne_global_residual_or_diagram_of_core_bound
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hpar : 1 < ChapterE.generationParameter H)
    (hN : localBorel T L ≤ normalizer (residual H : Set G))
    (hunique : ∀ X : Subgroup G, IsMaximalTwoLocal X → L ≤ X →
      X = normalizer (L : Set G))
    (hcore : ∀ A B R : Subgroup G, Global.Preparation T L H A B R →
      Group.IsPerfect R →
      (R.pCoreIn 2).relIndex ((R ⊔ Global.sourceS L H).pCoreIn 2) ≤ 2) :
    (∃ A B : Subgroup G, Global.Preparation T L H A B (residual H) ∧
      Group.IsPerfect (residual H)) ∨ Global.RightDiagramSource T L H := by
  have hi := D.rankOne_generic_input_of_many h hmany hn hpsl
  obtain ⟨A,B,c⟩ := D.rankOne_exists_cartanPair h hn hpsl hH hpar
  obtain ⟨hleft,hSylow⟩ := D.rankOne_sourceS_intersection_left h hpsl hH
  have hprepare (R : Subgroup G) (r : Global.RightFactor T L H A B R) :
      Global.Preparation T L H A B R := by
    refine ⟨c,r.le_residual,r.outside,hunique,hleft,?_,r.quotient,
      r.S_normalizes,r.cartan_normalizes,r.borel,r.characteristic_two hi hH c hleft hN⟩
    intro i
    fin_cases i
    · exact hSylow
    · exact r.sylow
  rcases Global.residual_rightFactor_or_diagram_of_core_bound hi hH hpar c hN
    (fun R r hp => hcore A B R (hprepare R r) hp) with ⟨r,hp⟩ | hd
  · exact Or.inl ⟨A,B,hprepare _ r,hp⟩
  · exact Or.inr hd

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
