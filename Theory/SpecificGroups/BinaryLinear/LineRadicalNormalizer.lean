module
public import Theory.SpecificGroups.BinaryLinear.LineRadical

/-!
# Normalizers of nontrivial subgroups of a binary line radical

A nonidentity element of a line radical is a transvection with that line as
its displacement space. Conjugation by a normalizer preserves the common
displacement line, so the normalizer lies in the corresponding parabolic.
This supplies the local core escape used in Aschbacher–Smith 13.8.19,
via the natural-three argument of 13.7.6(1), printed pp.940 and 953.
-/

public section

open Subgroup
namespace BinaryLinear.LineRadical
variable {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]

theorem normalizer_le_parabolic_of_nontrivial_subgroup
    (w : E) (hw : w ≠ 0) (N : Subgroup (BinaryLinear.GL E))
    (hN : N ≤ radical (Submodule.span (ZMod 2) {w})) (hne : N ≠ ⊥) :
    normalizer (N : Set (BinaryLinear.GL E)) ≤ parabolic (Submodule.span (ZMod 2) {w}) := by
  obtain ⟨t,ht,ht1⟩ := (Subgroup.bot_or_exists_ne_one N).resolve_left hne
  obtain ⟨f,hf,hfw,he⟩ := exists_transvection_of_mem_line_radical hw (hN ht) ht1
  obtain ⟨b,hb⟩ := LinearMap.range_eq_top.mp (Module.Dual.range_eq_top_of_ne_zero hf) 1
  have moved (g : BinaryLinear.GL E) (hg : g ∈ normalizer (N : Set _)) :
      g w ∈ Submodule.span (ZMod 2) {w} := by
    have hm := (hN ((mem_normalizer_iff.mp hg t).mp ht)).2 (g b)
    change g (t (g.symm (g b))) - g b ∈ _ at hm
    rw [g.symm_apply_apply,he,hb,one_smul,map_add,add_sub_cancel_left] at hm
    exact hm
  intro g hg v
  constructor
  · intro hv
    obtain ⟨a,ha⟩ := Submodule.mem_span_singleton.mp hv
    have hmem := (Submodule.span (ZMod 2) {w}).smul_mem a
      (moved g⁻¹ ((normalizer (N : Set (BinaryLinear.GL E))).inv_mem hg))
    have heq := congrArg g.symm ha
    rw [g.symm_apply_apply,map_smul] at heq
    exact heq ▸ hmem
  · intro hv
    obtain ⟨a,rfl⟩ := Submodule.mem_span_singleton.mp hv
    rw [map_smul]
    exact (Submodule.span (ZMod 2) {w}).smul_mem a (moved g hg)
end BinaryLinear.LineRadical
