module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientFourHyperplaneGeometry
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Unique trace-polar poles of binary Hermitian hyperplanes

The actual trace-polar map is binary-linear and injective by the established
nondegeneracy calculation. Equal finite dimensions make it an equivalence
with the entire binary dual. Every binary hyperplane is the kernel of a
nonzero functional; over F₂ that functional is uniquely determined by its
kernel. Thus every actual binary hyperplane has a unique nonzero pole.

This supplies the dual-coordinate input for the conjugate normalization in
Aschbacher–Smith 6.1.4, printed p.665. Singular and nonsingular pole orbit
normalization remain separate geometry statements.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter6.Source.FourHyperplaneGeometry
open Representation.OrthogonalFourMinus.FiniteModel
variable (s : ℕ) [NeZero s]

local instance dualityFixedAlgebra : Algebra (ZMod 2) (fixedField s) := ZMod.algebra _ 2
local instance dualityBinaryModule : Module (ZMod 2) (Space s) :=
  Module.compHom (Space s) (algebraMap (ZMod 2) (fixedField s))

/-- The trace-polar functional varies binary-linearly with its actual pole. -/
def tracePolarMap : Space s →ₗ[ZMod 2] Module.Dual (ZMod 2) (Space s) :=
  AddMonoidHom.toZModLinearMap 2 {
    toFun := tracePolarFunctional s
    map_zero' := by
      apply LinearMap.ext
      intro w
      change Algebra.trace (ZMod 2) (fixedField s) ((form s).polarBilin 0 w) = 0
      rw [map_zero,LinearMap.zero_apply,map_zero]
    map_add' := by
      intro v w
      apply LinearMap.ext
      intro x
      change Algebra.trace (ZMod 2) (fixedField s) ((form s).polarBilin (v+w) x) =
        Algebra.trace (ZMod 2) (fixedField s) ((form s).polarBilin v x) +
        Algebra.trace (ZMod 2) (fixedField s) ((form s).polarBilin w x)
      rw [map_add,LinearMap.add_apply,map_add] }

/-- No two different poles induce the same binary functional. -/
theorem tracePolarMap_injective : Function.Injective (tracePolarMap s) := by
  apply LinearMap.ker_eq_bot.mp
  apply bot_unique
  intro v hv
  by_contra hne
  exact tracePolarFunctional_ne_zero s hne hv

/-- The trace-polar map reaches every binary linear functional. -/
def tracePolarEquiv : Space s ≃ₗ[ZMod 2] Module.Dual (ZMod 2) (Space s) :=
  LinearEquiv.ofBijective (tracePolarMap s)
    ⟨tracePolarMap_injective s,
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        (Subspace.dual_finrank_eq (K := ZMod 2) (V := Space s)).symm).mp
          (tracePolarMap_injective s)⟩

/-- Over F₂, equality of the kernels determines the actual pole uniquely. -/
theorem traceHyperplane_injective : Function.Injective (traceHyperplane s) := by
  intro v w hker
  apply tracePolarMap_injective s
  apply LinearMap.ext
  intro x
  have hzero : tracePolarFunctional s v x = 0 ↔ tracePolarFunctional s w x = 0 := by
    change x ∈ traceHyperplane s v ↔ x ∈ traceHyperplane s w
    rw [hker]
  have hbinary : ∀ a b : ZMod 2, (a = 0 ↔ b = 0) → a = b := by decide
  exact hbinary _ _ hzero

/-- Every literal binary hyperplane has a unique nonzero trace-polar pole. -/
theorem existsUnique_traceHyperplane
    (U : Submodule (ZMod 2) (Space s))
    (hU : Module.finrank (ZMod 2) U + 1 = Module.finrank (ZMod 2) (Space s)) :
    ∃! v : Space s, v ≠ 0 ∧ U = traceHyperplane s v := by
  have hproper : U < ⊤ := by
    apply lt_of_le_of_ne le_top
    intro he
    rw [he,finrank_top] at hU
    omega
  obtain ⟨f,hf,hle⟩ := U.exists_le_ker_of_lt_top hproper
  obtain ⟨v,rfl⟩ := (tracePolarEquiv s).surjective f
  have hv : v ≠ 0 := by
    intro hz
    exact hf (by rw [hz,map_zero])
  have heq : U = traceHyperplane s v := by
    apply Submodule.eq_of_le_of_finrank_eq hle
    change Module.finrank (ZMod 2) U = Module.finrank (ZMod 2) (traceHyperplane s v)
    have hd := traceHyperplane_finrank s hv
    omega
  refine ⟨v,⟨hv,heq⟩,?_⟩
  intro w hw
  exact traceHyperplane_injective s (hw.2.symm.trans heq)

/-- Actual determinant-one congruence moves a binary hyperplane by moving
its unique pole with the same Hermitian action. -/
theorem traceHyperplane_map
    (g : Matrix.SpecialLinearGroup (Fin 2) (Field s)) (v : Space s) :
    (traceHyperplane s v).map (Representation.SL2.BinarySmall.hermitian s g) =
      traceHyperplane s (action s g v) := by
  have hinv (x y : Space s) :
      (form s).polarBilin (action s g x) (action s g y) = (form s).polarBilin x y :=
    Representation.OrthogonalFourMinus.HermitianEquiv.polar_preserved s
      (Representation.OrthogonalFourMinus.HermitianEquiv.orthogonalAction s g) x y
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    change Algebra.trace (ZMod 2) (fixedField s)
      ((form s).polarBilin (action s g v) (action s g y)) = 0
    rw [hinv]
    exact hy
  · intro hx
    have hcancel : action s g (action s g⁻¹ x) = x := (action s).self_inv_apply g x
    refine ⟨action s g⁻¹ x,?_,hcancel⟩
    change Algebra.trace (ZMod 2) (fixedField s)
      ((form s).polarBilin v (action s g⁻¹ x)) = 0
    rw [←hinv,hcancel]
    exact hx

end CFSG.Quasithin.Chapter6.Source.FourHyperplaneGeometry
