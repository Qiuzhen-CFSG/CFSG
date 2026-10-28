module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.LocalAction
public import CFSG.Quasithin.ChapterI.Section04To05.A3SourceGeometry

/-!
# Recognition of the actual large-case overgroup

The completed I.5 coset geometry recognizes the three-vertex system on the
literal generated subgroup. Together with the original local-action theorem,
this removes the incidence premise from the large-case consumer. Its only
remaining local input is the distinct second Y-member and the marked middle
quotient, to be constructed by the 14.4.2 and 14.4.9--12 model analysis.

The final theorem applies this construction to the original 14.4.14 case
split. The second-member implication remains this large-branch owner's work;
the earlier faithful classification is owned by qt-d-1434-source, and the
other two recognition branches and final discharge by qt-d-14414-source.
No incidence or local recognition callback remains in these statements.

Source: Aschbacher--Smith, 14.4.13--14, printed p.1012; I.5.1, pp.419--422.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open LargerDimension LargerDimension.LocalAction LargerDimension.IntrinsicSource
open LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The literal G₀ is recognized from a second marked Y-member, using the
proved I.5 incidence construction rather than assuming its geometry. -/
theorem actual_overgroup_of_partner (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (classification : EarlierFaithfulClassification G (T : Subgroup G))
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (g : G) (hg : g ∈ L) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (partner : Partner T L V F g) :
    ∃ X : Subgroup G, X ∈ YFamily F.H T (F.Vi 2) (F.E g) ∧ X ≠ F.Li L 1 ∧
      (T : Subgroup G) ≤ actualG0 L T (F.Li L 1) (F.Li L 2) X ∧
      Nonempty (actualG0 L T (F.Li L 1) (F.Li L 2) X ≃*
        Matrix.ProjectiveSpecialLinearGroup (Fin 4) (ZMod 2)) := by
  obtain ⟨X, hX, hXne, ⟨e₂⟩⟩ := partner
  let a := source_marked_system d earlier hq chosen structural F g hg
    (source_local_data d earlier hq chosen structural alternatives classification
      F hne hZ g hg hgP hgH) X hX hXne e₂
  exact ⟨X, hX, hXne, source_T_le_actualG0 L T (F.Li L 1) (F.Li L 2) X,
    a.system.a3_source_recognition⟩

/-- The original large-branch contradiction once its marked partner is
constructed. All local actions and all incidence premises are discharged. -/
theorem contradiction_of_partner (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (classification : EarlierFaithfulClassification G (T : Subgroup G))
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hlarge : 64 < Nat.card F.U)
    (g : G) (hg : g ∈ L) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (partner : Partner T L V F g) : False := by
  obtain ⟨X, _, _, hT, ⟨e⟩⟩ := actual_overgroup_of_partner d earlier hq chosen
    structural alternatives classification F hne hZ g hg hgP hgH partner
  exact source_large_overgroup_exclusion d earlier hq chosen structural alternatives
    F hne hZ (by omega) _ hT e

/-- Literal 14.4.14 consumer with only the second-actor source implication
left in the large branch. This is conditional until that implication and
the two other source recognition branches are proved. -/
theorem recognition_of_partner_source (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (classification : EarlierFaithfulClassification G (T : Subgroup G))
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (nonextraspecial : F.ZU ≠ F.Vi 1 → Nonempty (G ≃* Sporadic.LeechRelated.HS.Carrier))
    (small : F.ZU = F.Vi 1 → Nat.card F.U = 32 →
      Nonempty (G ≃* Atlas.G2.Model (ZMod 3)))
    (partnerSource : F.ZU = F.Vi 1 → 64 < Nat.card F.U →
      ∀ g : G, g ∈ L → g ∈ F.P L → g ∉ F.H → Partner T L V F g) :
    Nonempty (G ≃* Sporadic.LeechRelated.HS.Carrier) ∨
      Nonempty (G ≃* Atlas.G2.Model (ZMod 3)) := by
  apply recognition_of_source_branches d earlier hq chosen structural alternatives F hne
    nonextraspecial small
  intro hZ hlarge
  obtain ⟨g, hg, hgP, hgH⟩ := exists_source_conjugator d earlier hq chosen structural F
  obtain ⟨X, _, _, hT, he⟩ := actual_overgroup_of_partner d earlier hq chosen
    structural alternatives classification F hne hZ g hg hgP hgH
    (partnerSource hZ hlarge g hg hgP hgH)
  exact ⟨actualG0 L T (F.Li L 1) (F.Li L 2) X, hT, he⟩

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
