module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.LocalGeometry.SecondCentralizer.LocalConstruction.Inputs
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.LocalGeometry.SecondCentralizer.LocalConstruction.AmalgamModel.Reflection
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.LocalGeometry.SecondCentralizer.LocalConstruction.AmalgamModel.Splitting
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.LocalGeometry.SecondCentralizer.LocalConstruction.AmalgamModel.Marking

/-!
# The marked C₂ × S₄ model of the local amalgam centralizer

For the literal join of Q and its selected left conjugate, let
C = C_{⟨Q,Qᵍ⟩}(t), E = Q ∩ Qᵍ, and V = E ∩ F. The action on V
has kernel E and forces |C| = 48. An element of C_Q(t) outside EF
can be adjusted by E to an involution r. Since r and tr lie in Q outside F,
neither is an ambient z-conjugate. The elementary extension therefore
splits as C₂ × S₄, and its complete involution-class calculation marks the
first ambient class exactly as the three even involutions in the S₄ factor.
The central factor is the original t in G.

This direct argument supplies all fields of LocalModelData. It assumes
neither Sylow placement nor either full ambient centralizer model, and
requires no ambient order or mixed-pair count. Quaternion normality and
two-class coverage are retained in the source-facing wrapper; once the
fusion eight and selected configuration are supplied, the stronger theorem
below does not need them separately.

Source: Aschbacher, “A 2-local characterization of M12”, Illinois J. Math.
47 (2003), 31–47, Lemma 4.1 and the opening of Lemma 4.2, pp.38–39.
-/

namespace CFSG.Quasithin.Extraspecial32.DegreeTwelve.SecondCentralizer
open Subgroup Amalgam
variable {G : Type*} [Group G] [Finite G] {z : G}

/-- The exact marked local model already follows from the supplied fusion
eight and selected intersection. No full-centralizer or ambient-order input is used. -/
public theorem nonempty_localModelData_of_fusion_eight (h : Hypotheses z)
    (d : FusionEightData z) (a : SelectedFusionData h) (t : G)
    (htE : t ∈ coreIntersection z a.g) (ht : orderOf t = 2) (hnt : ¬ IsConj z t) :
    Nonempty (LocalModelData z t a.g) := by
  obtain ⟨r, hrQ, hrC, hrord, hrEF⟩ := exists_reflection h d a htE ht hnt
  let rL : localCentralizer z t a.g := ⟨⟨r, hrC⟩, mem_sup_left hrQ⟩
  have hrL : orderOf rL = 2 := by
    rw [← orderOf_injective (ambient z t a.g) (ambient_injective z t a.g)]
    exact hrord
  have hrE : rL ∉ eight z t a.g := fun hx => hrEF (mem_sup_left hx)
  have hrn : ¬ IsConj z (ambient z t a.g rL) := fun hc =>
    hrEF (mem_sup_right (subset_closure ⟨hrQ, hc⟩))
  have htrn : ¬ IsConj z (ambient z t a.g (centralElement h a htE * rL)) := by
    intro hc
    have hm : t * r ∈ fusionCore z := subset_closure ⟨(coreInG z).mul_mem htE.1 hrQ, hc⟩
    have hp := (coreIntersection z a.g ⊔ fusionCore z).mul_mem
      (mem_sup_left ((coreIntersection z a.g).inv_mem htE)) (mem_sup_right hm)
    exact hrEF (by simpa only [inv_mul_cancel_left] using hp)
  obtain ⟨e⟩ := nonempty_unmarked_of_outside h d a htE ht hnt rL hrL hrE
  refine ⟨{ equiv := e, central := ?_, first := ?_ }⟩
  · have he := unmarked_central h a htE ht e
    have hs : e.symm (centralInvolution 4) = centralElement h a htE := by
      rw [← he, e.symm_apply_apply]
    change ambient z t a.g (e.symm (centralInvolution 4)) = t
    rw [hs]
    rfl
  · exact local_marking h d a htE ht hnt e rL hrL hrE hrn htrn

/-- The marked `C₂ × S₄` conclusion of source 4.1 and the opening of 4.2,
on the literal t-centralizer in the join of the selected conjugate cores. -/
public theorem nonempty_localModelData (h : Hypotheses z) (_hn : QuaternionSubgroupsNormal z)
    (d : FusionEightData z) (a : SelectedFusionData h) (t : G)
    (htE : t ∈ coreIntersection z a.g) (ht : orderOf t = 2) (hnt : ¬ IsConj z t)
    (_hclasses : ∀ x : G, orderOf x = 2 → IsConj z x ∨ IsConj t x) :
    Nonempty (LocalModelData z t a.g) := by
  exact nonempty_localModelData_of_fusion_eight h d a t htE ht hnt

end CFSG.Quasithin.Extraspecial32.DegreeTwelve.SecondCentralizer
