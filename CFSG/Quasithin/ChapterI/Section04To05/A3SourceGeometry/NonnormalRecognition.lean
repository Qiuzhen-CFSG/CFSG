module

public import CFSG.Quasithin.ChapterI.Section04To05.A3SourceGeometry
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.ThreeSourceReduction

/-!
# The nonnormal quaternion branch of I.4.6

The actual A₃ coset geometry discharges the last premise of the earlier
source reduction. The original involution-centralizer hypotheses and
quaternion nonnormality inside that centralizer give the elementary-eight,
A₈ or A₉ alternatives. No ambient recognition premise remains.

Source: Aschbacher–Smith I.4.6(1–2), printed p.417; Aschbacher,
“A 2-local characterization of M12”, Proposition 3.3.
-/

public section
namespace CFSG.Quasithin.Extraspecial32.NonnormalRecognition
variable {G : Type*} [Group G] [Finite G] {z : G}

theorem nonnormal_recognition (h : Hypotheses z) (hn : QuaternionSubgroupsNonnormal z) :
    ElementaryEightAlternative G ∨ Nonempty (G ≃* alternatingGroup (Fin 8)) ∨
      Nonempty (G ≃* alternatingGroup (Fin 9)) :=
  nonnormal_recognition_of_geometry h hn (fun _ S _ => S.a3_source_geometry)

end CFSG.Quasithin.Extraspecial32.NonnormalRecognition
