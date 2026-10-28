module

public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.NaturalAction
public import Theory.GroupTheory.WreathTwoSylowModel

/-!
# The fixed-space stabilizer in the natural orthogonal wreath model

An actor stabilizes a supported plane precisely when its coordinate shift is
trivial. For the standard dihedral Sylow subgroup, direct kernel computation
on the literal matrix action identifies the stabilizer of the fixed space of
its base subgroup with the dihedral subgroup itself. Conjugacy of Sylow
subgroups transfers this equality to every Sylow subgroup: the kernel of the
shift homomorphism is invariant under conjugation, and fixed spaces transform
under the same vector action.

This is the concrete calculation used for `N_{Mbar}(Z_S) = Tbar`, with
`S = N_T(V₁)` and `Z_S = C_V(S)`. It retains the actual action and embedded
Sylow subgroup throughout.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the plane
setup on printed pp.1121–1122 and the first paragraph of p.1143.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.ExtraspecialLocal.NormalizerAction.WreathModel

open Subgroup
open scoped Pointwise

attribute [local instance] orthogonalAction
private instance : DecidableEq OrthogonalActor :=
  fun a b => decidable_of_iff (a.left = b.left ∧ a.right = b.right)
    RegularWreathProduct.ext_iff.symm

private instance : Fintype OrthogonalActor :=
  Fintype.ofEquiv ((OrthogonalPlaneIndex → OrthogonalPlaneActor) × OrthogonalPlaneIndex)
    (RegularWreathProduct.equivProd _ _).symm

/-- Vectors fixed by the part of `P` that does not interchange the coordinates. -/
def baseFixed (P : Subgroup OrthogonalActor) (v : OrthogonalVector) : Prop :=
  ∀ h ∈ P, h.right = 1 → h • v = v

set_option synthInstance.maxSize 4096 in
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
/-- An actor preserves either supported plane exactly when its shift is trivial. -/
theorem plane_iff_shift : ∀ (w : OrthogonalActor) (i : OrthogonalPlaneIndex),
    (∀ v : OrthogonalVector,
      (∀ j, j ≠ i → v j = 1) ↔ (∀ j, j ≠ i → (w • v) j = 1)) ↔ w.right = 1 := by
  decide +kernel

set_option synthInstance.maxSize 4096 in
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem standard_normalizer : ∀ w : OrthogonalActor,
    (∀ v : OrthogonalVector,
      (∀ h : DihedralGroup 4, (wreathTwoDihedralHom h).right = 1 →
        wreathTwoDihedralHom h • v = v) ↔
      (∀ h : DihedralGroup 4, (wreathTwoDihedralHom h).right = 1 →
        wreathTwoDihedralHom h • (w • v) = w • v)) ↔
    ∃ h : DihedralGroup 4, wreathTwoDihedralHom h = w := by
  decide +kernel

private theorem shift_conj (a h : OrthogonalActor) :
    (a * h * a⁻¹).right = 1 ↔ h.right = 1 := by
  simp [mul_assoc]

private theorem baseFixed_conj (P : Subgroup OrthogonalActor)
    (a : OrthogonalActor) (v : OrthogonalVector) :
    baseFixed (MulAut.conj a • P) (a • v) ↔ baseFixed P v := by
  constructor
  · intro hv h hh hr
    have hh' : a * h * a⁻¹ ∈ MulAut.conj a • P :=
      Subgroup.smul_mem_pointwise_smul h (MulAut.conj a) P hh
    have he := hv _ hh' ((shift_conj a h).mpr hr)
    apply MulAction.injective a
    simpa only [mul_smul, inv_smul_smul] using he
  · intro hv h hh hr
    have hh' : a⁻¹ * h * a ∈ P :=
      Subgroup.mem_pointwise_smul_iff_inv_smul_mem.mp hh
    have he := hv _ hh' (by simpa only [inv_inv] using (shift_conj a⁻¹ h).mpr hr)
    have he' := congrArg (fun w : OrthogonalVector => a • w) he
    simpa only [mul_smul, smul_inv_smul] using he'

private theorem baseFixed_conj_iff (P : Subgroup OrthogonalActor)
    (a : OrthogonalActor) (v : OrthogonalVector) :
    baseFixed (MulAut.conj a • P) v ↔ baseFixed P (a⁻¹ • v) := by
  simpa only [smul_inv_smul] using baseFixed_conj P a (a⁻¹ • v)

/-- The setwise stabilizer of the base fixed space of a Sylow two-subgroup is that Sylow subgroup. -/
theorem sylow_normalizer (P : Sylow 2 OrthogonalActor) (w : OrthogonalActor) :
    (∀ v, baseFixed (P : Subgroup OrthogonalActor) v ↔
      baseFixed (P : Subgroup OrthogonalActor) (w • v)) ↔ w ∈ P := by
  change (∀ v, baseFixed (P : Subgroup OrthogonalActor) v ↔
    baseFixed (P : Subgroup OrthogonalActor) (w • v)) ↔ w ∈ (P : Subgroup OrthogonalActor)
  obtain ⟨a, rfl⟩ := MulAction.exists_smul_eq OrthogonalActor wreathTwoSylow P
  rw [Sylow.coe_subgroup_smul]
  have hstd : ∀ u : OrthogonalActor,
      (∀ v, baseFixed (wreathTwoSylow : Subgroup OrthogonalActor) v ↔
        baseFixed (wreathTwoSylow : Subgroup OrthogonalActor) (u • v)) ↔
      u ∈ (wreathTwoSylow : Subgroup OrthogonalActor) := by
    intro u
    simpa only [wreathTwoSylow_coe, baseFixed, MonoidHom.mem_range,
      forall_exists_index, forall_apply_eq_imp_iff] using standard_normalizer u
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  change _ ↔ a⁻¹ * w * a ∈ (wreathTwoSylow : Subgroup OrthogonalActor)
  rw [← hstd]
  constructor
  · intro h v
    simpa only [baseFixed_conj_iff, mul_smul, inv_smul_smul] using h (a • v)
  · intro h v
    simpa only [baseFixed_conj_iff, mul_smul, smul_inv_smul] using h (a⁻¹ • v)


end CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.ExtraspecialLocal.NormalizerAction.WreathModel
end
