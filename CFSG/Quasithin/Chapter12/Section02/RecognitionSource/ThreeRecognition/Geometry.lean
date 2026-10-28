module

public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.ThreeRecognition.Reduction
public import CFSG.Quasithin.ChapterI.Section04To05.A3SourceGeometry.NonnormalRecognition

/-!
# Dimension-three recognition after constructing the A₃ geometry

The original source applications now require only the affine local I.4.6
calculation. All incidence premises are discharged on the actual coset
spaces. The marked 12.2.13 alternatives retain the original block.

This is still conditional on the local hypotheses and nonnormality inside
C_G(z); their construction and the final 12.2.27 assembly remain with
qt-d-12213-three-recognition.
Source: Aschbacher–Smith 12.2.27(2), printed p.807.
-/

public section
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource.ThreeRecognition
open Extraspecial32
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G}

theorem source_recognition_of_local {K : GroupClass.{u}}
    (h : Hypothesis1223 K T L)
    (localData : ∃ z : G, Nonempty (Hypotheses z) ∧ QuaternionSubgroupsNonnormal z) :
    ClassicalGroup.IsPSL G 4 2 ∨ Nonempty (G ≃* alternatingGroup (Fin 9)) :=
  source_recognition_of_local_geometry h localData (fun _ S _ => S.a3_source_geometry)

theorem recognizedGroup_of_local {K : GroupClass.{u}}
    (h : Hypothesis1223 K T L)
    (localData : ∃ z : G, Nonempty (Hypotheses z) ∧ QuaternionSubgroupsNonnormal z) :
    RecognizedGroup G 3 :=
  recognizedGroup_of_local_geometry h localData (fun _ S _ => S.a3_source_geometry)

theorem alternatives_of_local {K : GroupClass.{u}}
    (h : Hypothesis1223 K T L) (C : SplitLinearConfiguration L V 3)
    (localData : ∃ z : G, Nonempty (Hypotheses z) ∧ QuaternionSubgroupsNonnormal z) :
    Alternatives12213 T L V :=
  alternatives_of_local_geometry h C localData (fun _ S _ => S.a3_source_geometry)

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource.ThreeRecognition
