module

public import Theory.AtlasPort.ExceptionalIsomorphisms.Support

/-!
# Kernels of the degree-three special linear projection

The natural projection `SL₃(F) → PSL₃(F)` has scalar kernel, identified with
the cube roots of unity. The existing finite-field center count and cyclicity
give a multiplicative equivalence with `C_gcd(3, |F| - 1)`.

These are projection-kernel calculations, not assertions of universality.
In particular the projection has kernel of order three over a four-element
field, so cannot realize the exceptional `C₄ × C₄ × C₃` multiplier.
The universal-cover calculations required by Aschbacher–Smith, I.1.3(2),(6),
and I.1.4(2), printed pp.407–408, require separate universality proofs.

The center count is reused from the attributed ATLAS port in
`Theory.AtlasPort.ExceptionalIsomorphisms.Support`.
-/

@[expose] public section

namespace Matrix.PSL3

open scoped MatrixGroups

variable (F : Type*) [Field F]

/-- The actual central quotient projection in degree three. -/
def projection : SL(3, F) →* PSL(3, F) :=
  QuotientGroup.mk' (Subgroup.center SL(3, F))

theorem projection_surjective : Function.Surjective (projection F) :=
  QuotientGroup.mk'_surjective _

theorem projection_ker : (projection F).ker = Subgroup.center SL(3, F) :=
  QuotientGroup.ker_mk' _

/-- Scalar matrices identify the projection kernel with the cube roots of unity. -/
noncomputable def projectionKernelEquivRoots :
    (projection F).ker ≃* rootsOfUnity 3 F :=
  (MulEquiv.subgroupCongr (projection_ker F)).trans
    (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity' (R := F) (0 : Fin 3))

instance projectionKernel_isCyclic : IsCyclic (projection F).ker :=
  (projectionKernelEquivRoots F).isCyclic.mpr inferInstance

variable [Finite F]

theorem card_projectionKernel :
    Nat.card (projection F).ker = Nat.gcd 3 (Nat.card F - 1) := by
  rw [projection_ker]
  exact Atlas.ExceptionalSupport.card_sl_center

/-- The cyclic structure, not only the order, of the ordinary projection kernel. -/
noncomputable def projectionKernelEquivCyclic :
    (projection F).ker ≃* Multiplicative (ZMod (Nat.gcd 3 (Nat.card F - 1))) :=
  mulEquivOfCyclicCardEq (by
    change Nat.card (projection F).ker = Nat.card (ZMod (Nat.gcd 3 (Nat.card F - 1)))
    rw [card_projectionKernel, Nat.card_zmod])

/-- The ordinary projection has kernel `C₃` when the field order is `1 mod 3`. -/
noncomputable def projectionKernelEquivThree (h : Nat.card F % 3 = 1) :
    (projection F).ker ≃* Multiplicative (ZMod 3) := by
  have hg : Nat.gcd 3 (Nat.card F - 1) = 3 := by
    rw [Nat.gcd_comm]
    apply Nat.gcd_eq_right_iff_dvd.mpr
    exact Nat.dvd_of_mod_eq_zero (by omega)
  exact cast (congrArg (fun d => (projection F).ker ≃* Multiplicative (ZMod d)) hg)
    (projectionKernelEquivCyclic F)

/-- The other ordinary projection kernels are trivial, including at field order
two. This does not compute the Schur multiplier of `PSL₃(2)`. -/
noncomputable def projectionKernelEquivOne (h : Nat.card F % 3 ≠ 1) :
    (projection F).ker ≃* Multiplicative (ZMod 1) := by
  have hg : Nat.gcd 3 (Nat.card F - 1) = 1 := by
    apply Nat.Coprime.gcd_eq_one
    apply (Nat.Prime.coprime_iff_not_dvd (by decide : Nat.Prime 3)).mpr
    intro hd
    have hp : 0 < Nat.card F := Nat.card_pos
    have hm := Nat.mod_eq_zero_of_dvd hd
    omega
  exact cast (congrArg (fun d => (projection F).ker ≃* Multiplicative (ZMod d)) hg)
    (projectionKernelEquivCyclic F)

/-- The ordinary projection over a four-element field cannot realize the
exceptional multiplier; its kernel is too small. -/
theorem projectionKernel_not_exceptional (hF : Nat.card F = 4) :
    ¬ Nonempty ((projection F).ker ≃*
      ((Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) ×
        Multiplicative (ZMod 3))) := by
  rintro ⟨e⟩
  have hcard := Nat.card_congr e.toEquiv
  change Nat.card (projection F).ker = Nat.card ((ZMod 4 × ZMod 4) × ZMod 3) at hcard
  rw [card_projectionKernel, hF] at hcard
  norm_num [Nat.card_prod, Nat.card_zmod] at hcard

end Matrix.PSL3
