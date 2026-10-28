module
public import Theory.LinearAlgebra.BinaryFivePointStabilizer.Basic
public import Theory.GroupTheory.PCoreLocalSetup
public import Theory.SpecificGroups.BinaryLinear.LineRadical
public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.TwoBlocks

/-!
# Normal two-subgroups of a binary point parabolic

Every nontrivial two-subgroup normalized by and contained in the full
point parabolic is its line radical. The two-core calculation gives
containment; conjugacy of the nonidentity line transvections gives equality.
This retains relative normality in the parabolic.

Source application: Aschbacher–Smith, 13.8.31(1), printed p.965.
-/

public section
open Subgroup
namespace BinaryLinear.LineRadical
variable {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
  [FiniteDimensional (ZMod 2) E]
omit [FiniteDimensional (ZMod 2) E] in
/-- Over the binary field, fixing a line means fixing its nonzero vector. -/
theorem parabolic_eq_point_stabilizer (v : E) (hv : v ≠ 0) :
    parabolic (Submodule.span (ZMod 2) {v}) =
      Theory.LinearAlgebra.BinaryFivePointStabilizer.stabilizer v := by
  ext g
  constructor
  · intro hg
    obtain ⟨a,ha⟩ := Submodule.mem_span_singleton.mp
      ((hg v).mpr (Submodule.mem_span_singleton_self v))
    have ha0 : a ≠ 0 := by
      intro hz
      exact hv (g.map_eq_zero_iff.mp (by simpa [hz] using ha.symm))
    have ha1 : a = 1 := (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) a ha0
    change g v = v
    simpa only [ha1,one_smul] using ha.symm
  · intro hg x
    have hfix : g v = v := hg
    constructor
    · intro hx
      obtain ⟨a,ha⟩ := Submodule.mem_span_singleton.mp hx
      exact Submodule.mem_span_singleton.mpr ⟨a,g.injective (by simpa [hfix] using ha)⟩
    · intro hx
      obtain ⟨a,rfl⟩ := Submodule.mem_span_singleton.mp hx
      simpa [map_smul,hfix] using Submodule.smul_mem
        (Submodule.span (ZMod 2) {v}) a (Submodule.mem_span_singleton_self v)

/-- No proper nontrivial normal two-subgroup of the full point parabolic survives. -/
theorem normal_two_eq_radical (v : E) (hv : v ≠ 0)
    (A : Subgroup (BinaryLinear.GL E)) (hA : IsPGroup 2 A) (hne : A ≠ ⊥)
    (hle : A ≤ parabolic (Submodule.span (ZMod 2) {v}))
    (hn : parabolic (Submodule.span (ZMod 2) {v}) ≤ normalizer (A : Set _)) :
    A = radical (Submodule.span (ZMod 2) {v}) := by
  have hAR : A ≤ radical (Submodule.span (ZMod 2) {v}) := by
    rw [← SmallParabolicLevi.map_twoCore_eq_radical]
    exact le_pCoreIn_of_normalizes hA hle hn
  obtain ⟨s,hs,hs1⟩ := (Subgroup.bot_or_exists_ne_one A).resolve_left hne
  obtain ⟨f,hf,hfv,he⟩ := exists_transvection_of_mem_line_radical hv (hAR hs) hs1
  have hse : s = transvection v f hfv := LinearEquiv.ext he
  apply le_antisymm hAR
  intro t ht
  by_cases ht1 : t = 1
  · exact ht1 ▸ A.one_mem
  obtain ⟨c,hcv,hct⟩ := conjugate_fixing_center v hv f hf hfv ht ht1
  have hc : c ∈ parabolic (Submodule.span (ZMod 2) {v}) := by
    intro x
    constructor
    · intro hx
      obtain ⟨a,ha⟩ := Submodule.mem_span_singleton.mp hx
      exact Submodule.mem_span_singleton.mpr ⟨a,c.injective (by simpa [hcv] using ha)⟩
    · intro hx
      obtain ⟨a,rfl⟩ := Submodule.mem_span_singleton.mp hx
      simpa [map_smul,hcv] using Submodule.smul_mem
        (Submodule.span (ZMod 2) {v}) a (Submodule.mem_span_singleton_self v)
  rw [←hct,←hse]
  exact (mem_normalizer_iff.mp (hn hc) s).mp hs
end BinaryLinear.LineRadical
