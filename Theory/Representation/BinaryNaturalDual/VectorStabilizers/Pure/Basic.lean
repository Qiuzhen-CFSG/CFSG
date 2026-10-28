module

public import Theory.Representation.BinaryNaturalDual.VectorStabilizers.Modules
public import Theory.LinearAlgebra.BinaryFivePointStabilizer.Quotient
public import Theory.LinearAlgebra.BinaryFivePointStabilizer.KernelCard
public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.TwoBlocks

/-!
# Pure-vector stabilizers and their geometric radical

The inner stabilizer of a pure vector is the actual point stabilizer in the
binary linear group. Its quotient action has the elementary displacement
kernel, which is the line radical and the intrinsic two-core. The comparison
with the automorphism group remembers the conjugating matrix and its action.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), H.9.1(3),
printed pp.389–390. The coordinate action is an explicit input.
-/

@[expose] public section

namespace BinaryNaturalDual.VectorStabilizers.Pure
open BinaryLinear
open Theory.LinearAlgebra
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

abbrev pointStabilizer (x : V) := BinaryFivePointStabilizer.stabilizer x
abbrev pointQuotient (x : V) := BinaryFivePointStabilizer.QuotientSpace x
abbrev pointQuotientAction (x : V) := BinaryFivePointStabilizer.quotientAction x
abbrev pointKernel (x : V) := BinaryFivePointStabilizer.kernel x

theorem pairStabilizer_zero (x : V) : pairStabilizer x 0 = pointStabilizer x := by
  ext g
  simp only [mem_pairStabilizer, LinearMap.zero_apply, forall_const, and_true,
    BinaryFivePointStabilizer.mem_stabilizer]

/-- Over F₂ a line stabilizer fixes its unique nonzero vector. -/
theorem parabolic_line_eq {x : V} (hx : x ≠ 0) :
    parabolic (Submodule.span (ZMod 2) {x}) = pointStabilizer x := by
  ext g
  constructor
  · intro hg
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp
      ((hg x).mpr (Submodule.mem_span_singleton_self x))
    have ha0 : a ≠ 0 := by
      intro hz
      exact hx (g.map_eq_zero_iff.mp (by simpa [hz] using ha.symm))
    have ha1 : a = 1 := (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) a ha0
    simpa [ha1, BinaryFivePointStabilizer.mem_stabilizer] using ha.symm
  · intro hg v
    have hfix : g x = x := hg
    constructor
    · intro hv
      obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hv
      exact Submodule.mem_span_singleton.mpr ⟨a, g.injective (by simpa [hfix] using ha)⟩
    · intro hv
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hv
      simpa [map_smul, hfix] using Submodule.smul_mem
        (Submodule.span (ZMod 2) {x}) a (Submodule.mem_span_singleton_self x)

/-- The quotient-action kernel is the actual line radical inside the point stabilizer. -/
theorem pointKernel_eq_radical (x : V) :
    pointKernel x = (radical (Submodule.span (ZMod 2) {x})).subgroupOf (pointStabilizer x) := by
  ext g
  rw [BinaryFivePointStabilizer.mem_kernel_iff]
  exact ⟨fun h => ⟨BinaryFivePointStabilizer.fixes_line x g, h⟩, fun h => h.2⟩

/-- The point kernel is exactly the intrinsic two-core, in every finite dimension. -/
theorem point_twoCore [FiniteDimensional (ZMod 2) V] (x : V) :
    pCore 2 (pointStabilizer x) = pointKernel x := by
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let : Finite (BinaryLinear.GL V) := Finite.of_injective (fun g : BinaryLinear.GL V => (g : V → V))
    DFunLike.coe_injective
  let : Finite (pointQuotient x) := Module.finite_of_finite (ZMod 2)
  let : Finite (BinaryLinear.GL (pointQuotient x)) := Finite.of_injective
    (fun g : BinaryLinear.GL (pointQuotient x) => (g : pointQuotient x → pointQuotient x))
    DFunLike.coe_injective
  have h := (pointQuotientAction x).comap_pCore_of_ker_isPGroup
    (BinaryFivePointStabilizer.quotientAction_surjective x)
    (IsElementaryAbelian.isPGroup 2 (pointKernel x))
  rw [SmallParabolicLevi.linearGroup_twoCore_eq_bot] at h
  exact h.symm

/-- The elementary radical has the order predicted by its displacement space. -/
theorem pointKernel_card [FiniteDimensional (ZMod 2) V] {x : V} (hx : x ≠ 0) :
    Nat.card (pointKernel x) = 2 ^ (Module.finrank (ZMod 2) V - 1) := by
  rw [Nat.card_congr (BinaryFivePointStabilizer.kernelDisplacementEquiv x).toEquiv]
  change Nat.card (pointQuotient x →ₗ[ZMod 2] BinaryFivePointStabilizer.line x) = _
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Module.finrank_linearMap,
    finrank_span_singleton hx, mul_one, Nat.card_zmod]
  congr 1
  have hd := (BinaryFivePointStabilizer.line x).finrank_quotient_add_finrank
  rw [finrank_span_singleton hx] at hd
  change Module.finrank (ZMod 2) (pointQuotient x) + 1 = _ at hd
  omega

open BinaryLinear.OuterCyclic

/-- The matrix comparison for the actual inner pure-vector stabilizer. -/
noncomputable def innerEquivPoint {n : ℕ} (d : CoordinateAction n) (x : OuterCyclic.Space n) :
    innerStabilizer d (x,0) ≃* pointStabilizer x :=
  (innerStabilizerEquivPair d x 0).trans (MulEquiv.subgroupCongr (pairStabilizer_zero x))

@[simp] theorem innerEquivPoint_conj {n : ℕ} (d : CoordinateAction n)
    (x : OuterCyclic.Space n) (a : innerStabilizer d (x,0)) :
    MulAut.conj (innerEquivPoint d x a).val = a.val :=
  innerStabilizerEquivPair_conj d x 0 a

/-- Comparison of the full stabilizer with the actual point stabilizer. -/
noncomputable def fullEquivPoint {n : ℕ} (hn : n = 4 ∨ n = 5)
    (d : CoordinateAction n) {x : OuterCyclic.Space n} (hx : x ≠ 0) :
    fullStabilizer d (x,0) ≃* pointStabilizer x :=
  (MulEquiv.subgroupCongr (pure_fullStabilizer_eq_innerStabilizer hn d hx)).trans
    (innerEquivPoint d x)

theorem inner_action {n : ℕ} (d : CoordinateAction n)
    (x : OuterCyclic.Space n) (a : innerStabilizer d (x,0)) (v : CoordinateSpace n) :
    d.representation a.val v = naturalDualRepresentation (innerEquivPoint d x a).val v :=
  innerStabilizer_action d x 0 a v

/-- Quotient action of the actual inner stabilizer on X/span(x). -/
noncomputable def innerQuotientAction {n : ℕ} (d : CoordinateAction n) (x : OuterCyclic.Space n) :
    innerStabilizer d (x,0) →* BinaryLinear.GL (pointQuotient x) :=
  (pointQuotientAction x).comp (innerEquivPoint d x).toMonoidHom

/-- The actual radical inside the inner stabilizer, defined by its quotient action. -/
noncomputable def innerRadical {n : ℕ} (d : CoordinateAction n) (x : OuterCyclic.Space n) :
    Subgroup (innerStabilizer d (x,0)) := (innerQuotientAction d x).ker

/-- The same radical embedded in the full automorphism group. -/
noncomputable def embeddedRadical {n : ℕ} (d : CoordinateAction n) (x : OuterCyclic.Space n) :
    Subgroup (MulAut (LinearGroup n)) :=
  (innerRadical d x).map (innerStabilizer d (x,0)).subtype

end BinaryNaturalDual.VectorStabilizers.Pure
