module

public import Theory.SpecificGroups.SL2.BinaryTetrahedral
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Mathlib.Tactic.NormNum

/-!
# The solvable linear factors in dimension at most two over F₃

The actual binary tetrahedral equivalence identifies SL₂(3) with Q₈ ⋊ C₃.
The determinant then proves GL₂(3) solvable. A choice of basis transfers
this to any two-dimensional ternary space. In dimension one, all linear
automorphisms commute because they are scalar maps.

The determinant argument follows the existing local proof in
`Theory/SpecificGroups/PSL3Three/ParabolicSolvability.lean`. These factors
are used for reducible Sp₄(3) subgroups in the condition K application of
Aschbacher–Smith, Theorem 0.1.2(4), printed pp.4 and 482.
-/

public section
noncomputable section
namespace Matrix.PSp4Three.ReducibleLinear

private abbrev F := ZMod 3
private abbrev GL2 := Matrix.GeneralLinearGroup (Fin 2) F
private abbrev SL2 := Matrix.SpecialLinearGroup (Fin 2) F

private theorem gl2_three_isSolvable : Group.IsSolvable GL2 := by
  let hQ : IsPGroup 2 (QuaternionGroup 2) :=
    IsPGroup.of_card (n := 3) (by norm_num [QuaternionGroup.card])
  let : Group.IsNilpotent (QuaternionGroup 2) := hQ.isNilpotent
  let : Group.IsSolvable
      (QuaternionGroup 2 ⋊[GLS3.Chapter5.SchurPresentation.q8C3Action]
        Multiplicative (ZMod 3)) :=
    Group.isSolvable_of_ker_le_range SemidirectProduct.inl
      SemidirectProduct.rightHom SemidirectProduct.range_inl_eq_ker_rightHom.ge
  let : Group.IsSolvable SL2 := by
    apply Group.isSolvable_of_surjective
      (G := (QuaternionGroup 2 ⋊[GLS3.Chapter5.SchurPresentation.q8C3Action]
        Multiplicative (ZMod 3))) (G' := SL2)
      (f := GLS3.Chapter5.SchurPresentation.binaryTetrahedralEquivSL.toMonoidHom)
    exact GLS3.Chapter5.SchurPresentation.binaryTetrahedralEquivSL.surjective
  let det := Matrix.GeneralLinearGroup.det (n := Fin 2) (R := F)
  apply Group.isSolvable_of_ker_le_range (SpecialLinearGroup.toGL (R := F)) det
  intro g hg
  let y : SL2 := ⟨(g : Matrix (Fin 2) (Fin 2) F), by
    have h := congr_arg Units.val hg
    change Matrix.det (g : Matrix (Fin 2) (Fin 2) F) = 1 at h
    exact h⟩
  refine ⟨y, ?_⟩
  apply Units.ext
  rfl

variable {V : Type*} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]

theorem linearEquiv_isSolvable_finrank_two (hdim : Module.finrank (ZMod 3) V = 2) :
    Group.IsSolvable (V ≃ₗ[ZMod 3] V) := by
  let := gl2_three_isSolvable
  let e := (Matrix.GeneralLinearGroup.toLin' (Module.finBasisOfFinrankEq (ZMod 3) V hdim)).trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 3) V)
  exact Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective

theorem linearEquiv_isSolvable_finrank_one {K : Type*} [Field K]
    {M : Type*} [AddCommGroup M] [Module K M] [FiniteDimensional K M]
    (hdim : Module.finrank K M = 1) : Group.IsSolvable (M ≃ₗ[K] M) := by
  apply Group.isSolvable_of_comm
  intro g h
  obtain ⟨a, ha⟩ := (LinearEquiv.smul_id_of_finrank_eq_one hdim).surjective g.toLinearMap
  obtain ⟨b, hb⟩ := (LinearEquiv.smul_id_of_finrank_eq_one hdim).surjective h.toLinearMap
  have hga (v : M) : g v = a • v := by
    exact (LinearMap.congr_fun ha v).symm
  have hhb (v : M) : h v = b • v := by
    exact (LinearMap.congr_fun hb v).symm
  ext v
  simp only [LinearEquiv.mul_apply, hga, hhb, smul_smul, mul_comm]

end Matrix.PSp4Three.ReducibleLinear
