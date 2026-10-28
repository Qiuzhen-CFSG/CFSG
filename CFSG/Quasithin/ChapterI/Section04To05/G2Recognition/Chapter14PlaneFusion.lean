module
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.Chapter14PlaneNormalizer
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.PlaneFusion

/-!
# Exact cubic-plane fusion in the dimension-four source configuration

For the original SourceLocalData, fusion in H is exactly equality or
inversion. If the plane is Sylow, this is also its ambient fusion, and
none of its distinct subgroups are conjugate. The actual M still supplies
a diagonal cubic with precisely that pair as its class in the plane.
The actual diagonal is torus invariant even without the Sylow premise.
All factor embeddings, M, and the conjugating element are retained.

This applies the q=3 calculation in `PlaneFusion` to Aschbacher–Smith
I.4(G1)–(G2), printed p.417. It discharges the fusion calculation only;
it does not discharge the I.4.5 recognize callback. The exceptional
branch exclusions and the Atlas equivalence remain in this recognition
task, while `qt-d-14414-g2-source` produces SourceLocalData.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource Chapter14.Section04.CaseOneGeometry
open Chapter14.Section04.CaseOneDimensionFour Chapter14.Section04.DimensionFour
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

theorem source_cubic_plane_fusion (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32)
    (localData : SourceLocalData L F) :
    ∃ (c : G2ThreeConfiguration G) (t : CubicTorus c) (m : c.M) (g : G),
      let E : Subgroup G := zpowers ((t.x:c.H):G) ⊔ zpowers ((t.y:c.H):G)
      let v : G := MulAut.conj g (m:G)
      orderOf m = 3 ∧ v ∈ E ∧
      v ∉ zpowers ((t.x:c.H):G) ∧ v ∉ zpowers ((t.y:c.H):G) ∧
      t.torus.map c.H.subtype ≤ normalizer (zpowers v : Set G) ∧
      (∀ a ∈ E, ∀ b ∈ E,
        (∃ h ∈ c.H, MulAut.conj h a = b) ↔ b = a ∨ b = a⁻¹) ∧
      ((∃ P : Sylow 3 G, (P:Subgroup G) = E) →
        (∀ a ∈ E, ∀ b ∈ E, IsConj a b ↔ b = a ∨ b = a⁻¹) ∧
        (∀ A ≤ E, ∀ B ≤ E, ∀ h : G,
          A.map (MulAut.conj h).toMonoidHom = B → A = B) ∧
        (∀ a ∈ E, IsConj (m:G) a ↔ a = v ∨ a = v⁻¹)) := by
  obtain ⟨c⟩ := configuration_of_source_local d earlier hq chosen structural alternatives
    F hne hZ hcard localData
  obtain ⟨t⟩ := exists_cubic_torus c
  obtain ⟨m, g, hm, hv, hvx, hvy, hTv, hf⟩ := t.exists_marked_M_plane_fusion
  refine ⟨c, t, m, g, hm, hv, hvx, hvy, hTv, ?_, ?_⟩
  · intro a ha b hb
    exact t.plane_fusion_in_H_iff a b ha hb
  · intro hSylow
    exact ⟨fun a ha b hb => t.plane_isConj_iff_of_sylow hSylow a b ha hb,
      fun A hA B hB h hh => t.plane_subgroup_eq_of_conjugate_of_sylow hSylow A B hA hB h hh,
      hf hSylow⟩

end CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
