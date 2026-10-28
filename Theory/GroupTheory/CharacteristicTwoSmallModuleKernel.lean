module
public import Theory.GroupTheory.TwoLayerCentralizer
public import Theory.GroupTheory.PResidual.Quotient
/-!
# The exact kernel on a small module inside a characteristic-two group

Let Q be a self-centralizing normal subgroup, and let W be a two-group
normalized by D. If Q centralizes W and [Q,D] lies in W, then the
centralizer of W in D maps to a normal two-group in DQ/Q. When that
quotient has trivial two-core, the kernel is exactly D intersect Q.
This retains the original quotient instead of assuming that an action
through an arbitrary two-core quotient is faithful.
Source application: Aschbacher--Smith C.5.12, printed p.163.
-/
public section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]
theorem centralizer_small_module_eq_quotient_kernel
    (Q D W : Subgroup G) [Q.Normal]
    (hCQ : centralizer (Q : Set G) ≤ Q)
    (hW : IsPGroup 2 W) (hWD : W ≤ D) (hDW : D ≤ normalizer (W : Set G))
    (hQW : Q ≤ centralizer (W : Set G)) (hc : ⁅Q,D⁆ ≤ W)
    (hcore : pCore 2 (D.map (QuotientGroup.mk' Q)) = ⊥) :
    centralizer (W.subgroupOf D : Set D) = Q.comap D.subtype := by
  let C := D ⊓ centralizer (W : Set G)
  let q := QuotientGroup.mk' Q
  let f := q.subgroupMap D
  let s := f.comp (inclusion (show C ≤ D from inf_le_left))
  have hce : C.subgroupOf D = centralizer (W.subgroupOf D : Set D) := by
    ext d
    constructor
    · rintro ⟨_,hd⟩ w hw
      exact Subtype.ext (hd w hw)
    · intro hd
      refine ⟨d.property,?_⟩
      intro w hw
      exact congrArg D.subtype (hd ⟨w,hWD hw⟩ hw)
  let : (W.subgroupOf D).Normal := (normal_subgroupOf_iff_le_normalizer hWD).mpr hDW
  have hCn : (C.subgroupOf D).Normal := hce.symm ▸ inferInstance
  let := hCn
  have hsrange : s.range = (C.subgroupOf D).map f := by
    rw [MonoidHom.range_comp,inclusion_range]
  have hres : (pResidual 2 C).map C.subtype ≤ Q :=
    (residual_centralizes_of_two_layer C Q W hW inf_le_right
      (by rw [commutator_comm]; exact (commutator_mono le_rfl inf_le_left).trans hc)).trans hCQ
  have hresker : pResidual 2 C ≤ s.ker := by
    intro c hc'
    apply MonoidHom.mem_ker.mpr
    apply Subtype.ext
    exact (QuotientGroup.eq_one_iff _).mpr (hres (mem_map_of_mem C.subtype hc'))
  have hp : IsPGroup 2 s.range :=
    ((pResidual_le_iff_isPGroup_quotient 2 s.ker).mp hresker).of_equiv
      (QuotientGroup.quotientKerEquivRange s)
  have hsn : s.range.Normal := by
    rw [hsrange]
    exact Normal.map hCn f (q.subgroupMap_surjective D)
  have hz : s.range = ⊥ := bot_unique ((show s.range ≤ pCore 2 (D.map q) from le_sSup ⟨hsn,hp⟩).trans hcore.le)
  apply le_antisymm
  · intro d hd
    have hc' : d.val ∈ C := by
      change d ∈ C.subgroupOf D
      rw [hce]
      exact hd
    have hs : s ⟨d.val,hc'⟩ = 1 := mem_bot.mp (hz ▸ (show s ⟨d.val,hc'⟩ ∈ s.range from ⟨⟨d.val,hc'⟩,rfl⟩))
    have hq : q d.val = 1 := congrArg Subtype.val hs
    exact (QuotientGroup.eq_one_iff (N := Q) d.val).mp hq
  · intro d hd w hw
    exact Subtype.ext (hQW hd w hw)
end Subgroup
