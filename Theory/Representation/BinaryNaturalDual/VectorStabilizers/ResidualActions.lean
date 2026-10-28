module

public import Theory.Representation.BinaryNaturalDual.VectorStabilizers.Pure.Modules
public import Theory.Representation.BinaryNaturalDual.VectorStabilizers.Pure.Residual

/-!
# Actions of the embedded vector-stabilizer two-residuals

The proved residual equalities identify the source actor O²(C_L(v)) with
the actual inner stabilizer. Transporting the restriction maps through
these equalities gives its full natural action on ker(f), the exact dual
action on ann(x), and the fixed and commutator spaces in the original
coordinate module. The pure-vector commutator formula uses the same actor.

Source: Aschbacher–Smith, H.9.1(3–4), printed pp.389–390, with the corrected
nonsingular statement independent of the pure-vector Sylow marking.
-/

@[expose] public section

namespace BinaryNaturalDual.VectorStabilizers

/-- O²(C_M(x,f)), with its actual ambient embedding, is the same source L_v. -/
theorem componentStabilizer_embedded_twoResidual {n : ℕ} (hn : n = 4 ∨ n = 5)
    (d : CoordinateAction n) {x : BinaryLinear.OuterCyclic.Space n}
    {f : Module.Dual (ZMod 2) (BinaryLinear.OuterCyclic.Space n)} (h : f x = 1) :
    (pResidual 2 (componentStabilizer d x f)).map (componentStabilizer d x f).subtype =
      innerResidual d (x,f) := by
  rw [componentStabilizer_eq_innerStabilizer hn d (vector_ne_zero h)]
  rfl

/-- The original representation restricted to the embedded O²(C_L(v)). -/
def residualRepresentation {n : ℕ} (d : CoordinateAction n) (v : CoordinateSpace n) :
    Representation (ZMod 2) (innerResidual d v) (CoordinateSpace n) :=
  d.representation.comp (innerResidual d v).subtype

/-- The source residual acts as the full linear group of the covector kernel. -/
noncomputable def residualEquivKernel {n : ℕ} (hn : n = 4 ∨ n = 5)
    (d : CoordinateAction n) {x : BinaryLinear.OuterCyclic.Space n}
    {f : Module.Dual (ZMod 2) (BinaryLinear.OuterCyclic.Space n)} (h : f x = 1) :
    innerResidual d (x,f) ≃* BinaryLinear.GL f.ker :=
  (MulEquiv.subgroupCongr (innerResidual_eq_innerStabilizer hn d h)).trans
    (innerStabilizerEquivKernel d h)

/-- The kernel action is the original natural action, including its embedding. -/
theorem residual_kernel_action {n : ℕ} (hn : n = 4 ∨ n = 5)
    (d : CoordinateAction n) {x : BinaryLinear.OuterCyclic.Space n}
    {f : Module.Dual (ZMod 2) (BinaryLinear.OuterCyclic.Space n)} (h : f x = 1)
    (a : innerResidual d (x,f)) (w : f.ker) :
    d.representation a.val (w.val,0) = ((residualEquivKernel hn d h a w).val,0) :=
  inner_kernel_action d h
    (MulEquiv.subgroupCongr (innerResidual_eq_innerStabilizer hn d h) a) w

/-- The whole dual vector, not just its evaluations, is the exact contragredient
of the same kernel action under restriction to ker(f). -/
theorem residual_dual_action {n : ℕ} (hn : n = 4 ∨ n = 5)
    (d : CoordinateAction n) {x : BinaryLinear.OuterCyclic.Space n}
    {f : Module.Dual (ZMod 2) (BinaryLinear.OuterCyclic.Space n)} (h : f x = 1)
    (a : innerResidual d (x,f)) (q : annihilator x) :
    d.representation a.val (0,q.val) =
      (0,((annihilatorEquivKernelDual h).symm
        ((residualEquivKernel hn d h a).symm.dualMap
          (annihilatorEquivKernelDual h q))).val) := by
  let b := MulEquiv.subgroupCongr (innerResidual_eq_innerStabilizer hn d h) a
  let g := innerStabilizerEquivPair d x f b
  have he := annihilatorEquivKernelDual_equivariant h g q
  have he' : annihilatorAction x f g q =
      (annihilatorEquivKernelDual h).symm
        ((kernelAction x f g).symm.dualMap (annihilatorEquivKernelDual h q)) :=
    (annihilatorEquivKernelDual h).eq_symm_apply.mpr he
  have ha := innerStabilizer_action d x f b (0,q.val)
  rw [naturalDualRepresentation_apply, map_zero] at ha
  change d.representation a.val (0,q.val) =
    (0,((annihilatorEquivKernelDual h).symm
      ((kernelAction x f g).symm.dualMap (annihilatorEquivKernelDual h q))).val)
  rw [← he']
  exact ha

/-- C_V(O²(C_L(v))) is exactly the two marked lines. -/
theorem residual_invariants {n : ℕ} (hn : n = 4 ∨ n = 5)
    (d : CoordinateAction n) {x : BinaryLinear.OuterCyclic.Space n}
    {f : Module.Dual (ZMod 2) (BinaryLinear.OuterCyclic.Space n)} (h : f x = 1) :
    Representation.invariants (residualRepresentation d (x,f)) =
      (Submodule.span (ZMod 2) {x}).prod (Submodule.span (ZMod 2) {f}) := by
  unfold residualRepresentation
  rw [innerResidual_eq_innerStabilizer hn d h]
  exact inner_invariants hn d h

/-- [V,O²(C_L(v))] is exactly ker(f) ⊕ ann(x). -/
theorem residual_commutator {n : ℕ} (hn : n = 4 ∨ n = 5)
    (d : CoordinateAction n) {x : BinaryLinear.OuterCyclic.Space n}
    {f : Module.Dual (ZMod 2) (BinaryLinear.OuterCyclic.Space n)} (h : f x = 1) :
    Representation.Coinvariants.ker (residualRepresentation d (x,f)) =
      f.ker.prod (annihilator x) := by
  unfold residualRepresentation
  rw [innerResidual_eq_innerStabilizer hn d h]
  exact inner_commutator hn d h

/-- The pure residual commutator space is X ⊕ ann(x). -/
theorem pure_residual_commutator {n : ℕ} (hn : n = 4 ∨ n = 5)
    (d : CoordinateAction n) {x : BinaryLinear.OuterCyclic.Space n} (hx : x ≠ 0) :
    Representation.Coinvariants.ker (residualRepresentation d (x,0)) =
      (⊤ : Submodule (ZMod 2) (BinaryLinear.OuterCyclic.Space n)).prod (annihilator x) := by
  unfold residualRepresentation
  rw [Pure.innerResidual_eq (by omega) d hx]
  exact Pure.inner_commutator hn d hx

end BinaryNaturalDual.VectorStabilizers
