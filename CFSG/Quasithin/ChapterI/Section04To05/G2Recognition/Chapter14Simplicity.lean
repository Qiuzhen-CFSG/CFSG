module
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.Chapter14Extension
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.AmbientNormal

/-!
# The source-local data force ambient simplicity

Apply the normal-subgroup argument to the actual configuration produced by
Chapter 14. Simplicity is proved from these local data, without an added
simplicity or recognition premise. The recognition equivalence and the
callback in `recognition_of_source_local` remain with
`qt-i45-g2-recognition`; the independent SourceLocalData producer is
`qt-d-14414-g2-local-source`, and `qt-d-14414-g2-source` owns final assembly.

Source: Aschbacher–Smith I.4.5, printed p.417, and 14.4.3–5, pp.1007–1008;
Fong–Wong, Nagoya Math. J.36 (1969), §2F, pp.153–154.
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

theorem source_ambient_simple (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32)
    (localData : SourceLocalData L F) : IsSimpleGroup G := by
  obtain ⟨c⟩ := configuration_of_source_local d earlier hq chosen structural alternatives
    F hne hZ hcard localData
  exact ambient_simple c

end CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
