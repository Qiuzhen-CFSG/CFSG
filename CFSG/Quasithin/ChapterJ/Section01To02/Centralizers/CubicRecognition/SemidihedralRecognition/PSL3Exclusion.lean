module

public import Theory.SpecificGroups.PSL3Two.SemidihedralExtensionObstruction
public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.CubicRecognition.SemidihedralRecognition.LocalReduction

/-!
# The PSL₃(2) exclusion in the intrinsic recognition problem

The involution centralizer supplied by the local hypotheses is Sylow and has
model SD16. The actual index-two PSL₃(2) extension obstruction therefore excludes
the L₃(2) alternative after I.4.1(2). The construction of the normal two-residual
and the application of I.4.1 remain with the recognition assembly.

Source: Aschbacher–Smith, J.2.7, printed p.435 (PDF p.446).
-/

public section
namespace CFSG.Quasithin.ChapterJ.SemidihedralRecognition.Hypotheses

/-- The L₃(2) alternative is impossible for an actual normal index-two subgroup
of the intrinsic involution-centralizer recognition problem. -/
theorem no_psl3_index_two {W : Type*} [Group W] [Finite W]
    (h : CFSG.Quasithin.ChapterJ.SemidihedralRecognition.Hypotheses W)
    (N : Subgroup W) [N.Normal] (hi : N.index = 2)
    (eN : N ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)) : False := by
  obtain ⟨S, hS⟩ := h.centralizer_isSylow
  exact Matrix.PSL3Two.SemidihedralExtensionObstruction.no_index_two_extension
    N hi eN S ((MulEquiv.subgroupCongr hS).trans h.model)

end CFSG.Quasithin.ChapterJ.SemidihedralRecognition.Hypotheses
