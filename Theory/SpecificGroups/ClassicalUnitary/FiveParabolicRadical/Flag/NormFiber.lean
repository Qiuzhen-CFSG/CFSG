module
public import Theory.SpecificGroups.ClassicalUnitary.FiveParabolicTorus.Cover
public import Theory.Representation.BinaryPrimeDegree

/-!
# The norm-one pentagon spans the binary field of sixteen elements

Multiplication by fifth roots preserves their binary span and acts faithfully
there, because the span contains one. The order-five representation bound
forces four dimensions, filling the original field. This supplies the faithful
five-point action used in the actual PSU₅(4) Sylow automorphism calculation.

Source application: Aschbacher--Smith 4.4.10--11 and 12.1.9,
printed pp.621 and 793, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Representation
namespace Theory.SpecificGroups.UnitaryFive.Flag
variable {F : Type*} [Field F] [Finite F] [Algebra (ZMod 2) F]

/-- The literal norm-one fiber spans the original field over its binary
prime field; no replacement of its stored field coordinates is made. -/
theorem normOne_span_eq_top (hcard : Nat.card F = 16) :
    Submodule.span (ZMod 2) {x : F | x ^ 5 = 1} = ⊤ := by
  let W := Submodule.span (ZMod 2) {x : F | x ^ 5 = 1}
  let ρ : Representation (ZMod 2) (rootsOfUnity 5 F) F := {
    toFun a := ((a.val.val : F) • (LinearMap.id : F →ₗ[F] F)).restrictScalars (ZMod 2)
    map_one' := by ext x; simp
    map_mul' a b := by ext x; simp [mul_assoc] }
  have hstable : ∀ a : rootsOfUnity 5 F, ∀ x ∈ W, ρ a x ∈ W := by
    intro a x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      apply Submodule.subset_span
      change (a.val.val * x) ^ 5 = 1
      rw [mul_pow,(mem_rootsOfUnity' 5 a.val).mp a.property,hx,one_mul]
    | zero => simpa only [map_zero] using W.zero_mem
    | add x y hx hy ihx ihy => simpa only [map_add] using W.add_mem ihx ihy
    | smul c x hx ih => simpa only [map_smul] using W.smul_mem c ih
  let σ := ρ.subrepresentation W hstable
  have hfaith : Function.Injective σ := by
    intro a b he
    have h1 : (1 : F) ∈ W := Submodule.subset_span (by simp)
    have hv := congrArg (fun f : Module.End (ZMod 2) W => (f ⟨1,h1⟩).val) he
    apply rootsOfUnity.coe_injective
    change a.val.val * 1 = b.val.val * 1 at hv
    simpa only [mul_one] using hv
  have hfour : 4 ≤ Module.finrank (ZMod 2) W := by
    have hh := BinaryPrimeDegree.orderOf_le_finrank σ hfaith
      (by decide : Nat.Prime 5) (by decide)
      (by rw [card_fifthRoots hcard])
    rwa [BinaryPrimeDegree.orderOf_two_mod_five] at hh
  have hd : Module.finrank (ZMod 2) F = 4 := by
    apply Nat.pow_right_injective (by decide : 1 < (2 : ℕ))
    have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := F)
    simpa only [Nat.card_zmod,hcard] using hc.symm
  exact Submodule.eq_top_of_finrank_eq (Nat.le_antisymm (Submodule.finrank_le W)
    (hd.symm ▸ hfour))

end Theory.SpecificGroups.UnitaryFive.Flag
