module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalRecognitionDiagram
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalRecognitionExchanged

/-!
# The nonshort diagram factor in the original Chapter 12 setup

The marked linear and symplectic diagram rows now construct a perfect
prepared right factor and prove it nonshort. Combining this with the
exchanged-component exclusion leaves either the whole residual O²(H)
or a nonshort factor, on the original overlap core and Cartan pair.
Thus the remaining diagram branch cannot give either natural-block row
of 5.2.6.

Original uniqueness is still supplied by qt-d-1222-rankone-global-uniqueness.
The F.1.12 core bound, the other diagram exclusions, the strict field bound
and ambient completion recognition remain with this task,
qt-d-1222-rankone-generic-global. The final consumers remain
qt-d-1222-rankone-generic and qt-d-1361-source.

Source: Aschbacher–Smith 5.2.6, pp.650–651, and its original Chapter 12
application, p.795 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- The actual marked diagram branch gives a perfect, nonshort prepared
right factor. Thus the linear-three and symplectic-four block amalgams
cannot recognize this pair. Original uniqueness remains explicit. -/
theorem rankOne_global_preparation_not_short_of_diagram
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hpar : 1 < ChapterE.generationParameter H)
    (hthree : ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hN : localBorel T L ≤ normalizer (residual H : Set G))
    (hunique : ∀ X : Subgroup G, IsMaximalTwoLocal X → L ≤ X →
      X = normalizer (L : Set G))
    (hd : Global.RightDiagramSource T L H) :
    ∃ A B R : Subgroup G, Global.Preparation T L H A B R ∧
      Group.IsPerfect R ∧ ¬ ChapterC.IsShort R := by
  have hi := D.rankOne_generic_input_of_many h hmany hn hpsl
  obtain ⟨A,B,c⟩ := D.rankOne_exists_cartanPair h hn hpsl hH hpar
  obtain ⟨R,r,hp,hnot⟩ := Global.diagram_source_rightFactor_not_short
    hi hH hpar hthree c hN hd
  obtain ⟨hleft,hSylow⟩ := D.rankOne_sourceS_intersection_left h hpsl hH
  refine ⟨A,B,R,?_,hp,hnot⟩
  refine ⟨c,r.le_residual,r.outside,hunique,hleft,?_,r.quotient,
    r.S_normalizes,r.cartan_normalizes,r.borel,r.characteristic_two hi hH c hleft hN⟩
  intro i
  fin_cases i
  · exact hSylow
  · exact r.sylow

/-- After the exchanged-component bound, the source can choose either the
whole residual or a nonshort perfect factor. This rules out the two block
rows in the remaining marked diagram branch, without assuming recognition. -/
theorem rankOne_global_residual_or_not_short_of_core_bound
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hpar : 1 < ChapterE.generationParameter H)
    (hthree : ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hN : localBorel T L ≤ normalizer (residual H : Set G))
    (hunique : ∀ X : Subgroup G, IsMaximalTwoLocal X → L ≤ X →
      X = normalizer (L : Set G))
    (hcore : ∀ A B R : Subgroup G, Global.Preparation T L H A B R →
      Group.IsPerfect R →
      (R.pCoreIn 2).relIndex ((R ⊔ Global.sourceS L H).pCoreIn 2) ≤ 2) :
    ∃ A B R : Subgroup G, Global.Preparation T L H A B R ∧
      Group.IsPerfect R ∧ (R = residual H ∨ ¬ ChapterC.IsShort R) := by
  rcases D.rankOne_global_residual_or_diagram_of_core_bound h hmany hn hpsl
    hH hpar hN hunique hcore with ⟨A,B,d,hp⟩ | hd
  · exact ⟨A,B,residual H,d,hp,Or.inl rfl⟩
  · obtain ⟨A,B,R,d,hp,hnot⟩ := D.rankOne_global_preparation_not_short_of_diagram
      h hmany hn hpsl hH hpar hthree hN hunique hd
    exact ⟨A,B,R,d,hp,Or.inr hnot⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
