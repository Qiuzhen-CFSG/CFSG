module
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.MaximalRecognition
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.Chapter14Completion

/-!
# Actual G₂(3) recognition in the large-core Chapter 14 branch

The literal source configuration now yields an actual Atlas isomorphism
whenever 27 divides the original group order. All endpoint action, whole-middle
compatibility, generation and completion-recognition premises are discharged.
The alternate theorem retains the precise strongly-three-embedded subgroup
for its independent exclusion producer qt-i45-g2-strong-three-exclusion.

The source-local-data premise and universal earlier-source inputs retain their
original meanings and producers. In particular a same-group Structural1222At
instance is not promoted to universal Structural1222. Unconditional I.4.5 and
the guarded Chapter14 final assembly still require their independent inputs.
Source: Aschbacher–Smith I.4.5, p.417; 14.4.3–5 and 14.4.14, pp.1007–1010.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource Chapter14.Section04.CaseOneGeometry
open Chapter14.Section04.CaseOneDimensionFour Chapter14.Section04.DimensionFour
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The literal Chapter14 large-core application concludes the actual Atlas
isomorphism, with no endpoint-map or completion-recognition callback. -/
theorem source_recognition_of_cube_dvd (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU=F.Vi 1) (hcard : Nat.card F.U=32)
    (localData : SourceLocalData L F) (hbig : 3^3∣Nat.card G) :
    Nonempty (G ≃* Atlas.G2.Model (ZMod 3)) := by
  obtain ⟨c⟩ := configuration_of_source_local d earlier hq chosen structural alternatives
    F hne hZ hcard localData
  exact nonempty_mulEquiv_of_cube_dvd c hbig

/-- The original marked source alternative now ends in an actual ambient
isomorphism in its large-core branch. The strong-three branch is not omitted. -/
theorem source_cubic_recognition (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU=F.Vi 1) (hcard : Nat.card F.U=32)
    (localData : SourceLocalData L F) :
    ∃ (c : G2ThreeConfiguration G) (t : CubicTorus c) (m : c.M) (g : G),
      let E := zpowers ((t.x:c.H):G) ⊔ zpowers ((t.y:c.H):G)
      orderOf m=3 ∧ MulAut.conj g (m:G)∈E ∧
      MulAut.conj g (m:G)∉zpowers ((t.x:c.H):G) ∧
      MulAut.conj g (m:G)∉zpowers ((t.y:c.H):G) ∧
      ((c.H≠⊤ ∧ 3∣Nat.card c.H ∧
        ∀ a : G,a∉c.H → ¬3∣Nat.card (c.H ⊓ c.H.map (MulAut.conj a).toMonoidHom : Subgroup G)) ∨
        Nonempty (G ≃* Atlas.G2.Model (ZMod 3))) := by
  obtain ⟨c,t,m,g,hm,hg,hgx,hgy,h⟩ := source_cubic_aligned_completion d earlier hq chosen
    structural alternatives F hne hZ hcard localData
  refine ⟨c,t,m,g,hm,hg,hgx,hgy,?_⟩
  rcases h with hsmall | ⟨_,_,p,_⟩
  · exact Or.inl hsmall
  · exact Or.inr p.nonempty_mulEquiv

end CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
