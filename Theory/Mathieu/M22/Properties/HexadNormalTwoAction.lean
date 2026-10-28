module
public import Theory.Mathieu.M22.Properties.OuterHexadRadical

/-!
# Normal two-groups in the full hexad action

The common fixed points of the literal E₁₆ translation kernel are its hexad.
A two-group centralizing that kernel therefore stabilizes the hexad. If the
inner hexad normalizes the two-group, the group lies in the two-core of their
join. The native outer-hexad radical theorem identifies this core with the
inner E₁₆, retaining every possible outer design automorphism.

Source: the binary M₂₂ hexad in Aschbacher--Smith I.2.2(6), p.412; this
extension supplies its actual ambient-core action in 2.3.9(7), p.526.
-/

public section
open scoped Pointwise
namespace Sporadic.Mathieu.M22OuterHexad
open Subgroup M22ValueBound.Concrete

/-- A normal two-group in a hexad extension which centralizes its translation
kernel lies in that same kernel; the possible outer action is retained. -/
theorem normal_two_fixer_le_kernel {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    (P : Subgroup m22DesignAut) (hp : IsPGroup 2 P)
    (hc : P ≤ centralizer ((m22HexadPointwiseKernel B).map inclusion : Set m22DesignAut))
    (hn : (MulAction.stabilizer M22 B).map inclusion ≤ normalizer (P : Set m22DesignAut)) :
    P ≤ (m22HexadPointwiseKernel B).map inclusion := by
  let H := (MulAction.stabilizer M22 B).map inclusion
  let R := H ⊔ P
  have hP : P ≤ MulAction.stabilizer m22DesignAut B := by
    intro g hg
    apply MulAction.mem_stabilizer_finset'.mpr
    intro x hx
    apply (mem_hexad_iff_m22HexadPointwiseKernel_fixed hB _).mpr
    intro v hv
    have he := mem_centralizer_iff.mp (hc hg) (inclusion v) (mem_map_of_mem inclusion hv)
    have hf := congrArg (fun a : m22DesignAut => a.val x) he
    change v.val (g.val x) = g.val (v.val x) at hf
    have hvx := (mem_m22HexadPointwiseKernel B v).mp hv x hx
    change v.val x = x at hvx
    change v.val (g.val x) = g.val x
    rw [hf,hvx]
  have hR : R ≤ MulAction.stabilizer m22DesignAut B := sup_le
    (by rintro _ ⟨x,hx,rfl⟩; exact hx) hP
  have he := radical_eq hB R le_sup_left hR
  rw [← he]
  exact le_pCoreIn_of_normalizes hp le_sup_right (sup_le hn P.le_normalizer)

end Sporadic.Mathieu.M22OuterHexad
