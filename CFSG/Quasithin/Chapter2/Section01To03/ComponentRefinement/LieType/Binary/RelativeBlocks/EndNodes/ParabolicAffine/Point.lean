module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.Binary.RelativeBlocks.EndNodes.Affine
public import Theory.Representation.BinaryNaturalDual.VectorStabilizers.Pure.Structure
public import Theory.Representation.BinaryNaturalDual.VectorStabilizers.Pure.Modules

/-!
# Affine coordinates for the binary point stabilizer

Displacement identifies the line radical with the annihilator of the marked
vector. Its conjugation action is the inverse dual of the quotient action.
A complement splits the quotient map, and reparametrizing that quotient by
contragredience gives the published column-vector affine group. The kernel
and quotient equations retain both geometric markings.

This is the intrinsic end-node calculation used in Aschbacher–Smith 2.3.9(7),
printed pp.525–526; the block-module conventions are C.1.7/C.1.12, pp.123–124.
The splitting formula follows the construction in
`BinaryNaturalDual.VectorStabilizers.Pure.Split`.
-/

public section

open BinaryLinear BinaryNaturalDual.VectorStabilizers BinaryNaturalDual.VectorStabilizers.Pure
open Theory.LinearAlgebra
namespace CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.Binary.EndNodes.ParabolicAffine
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

noncomputable def displacementCoordinates {x : V} (hx : x ≠ 0) :
    (pointQuotient x →ₗ[ZMod 2] BinaryFivePointStabilizer.line x) ≃ₗ[ZMod 2] annihilator x :=
  (LinearEquiv.congrRight (LinearEquiv.toSpanNonzeroSingleton (ZMod 2) V x hx).symm).trans
    (annihilatorQuotientDual x).symm

noncomputable def kernelCoordinates {x : V} (hx : x ≠ 0) :
    pointKernel x ≃* Multiplicative (annihilator x) :=
  (BinaryFivePointStabilizer.kernelDisplacementEquiv x).trans
    (AddEquiv.toMultiplicative (displacementCoordinates hx).toAddEquiv)

theorem kernelCoordinates_smul {x : V} (hx : x ≠ 0) (k : pointKernel x) (v : V) :
    (Multiplicative.toAdd (kernelCoordinates hx k)).val v • x = k.val.val v - v := by
  change ((displacementCoordinates hx)
    (Multiplicative.toAdd (BinaryFivePointStabilizer.kernelDisplacementEquiv x k))).val v • x = _
  rw [BinaryFivePointStabilizer.kernelDisplacementEquiv_apply]
  change ((LinearEquiv.toSpanNonzeroSingleton (ZMod 2) V x hx).symm
    (BinaryFivePointStabilizer.kernelDisplacement x k ((BinaryFivePointStabilizer.line x).mkQ v))) • x = _
  rw [LinearEquiv.toSpanNonzeroSingleton_symm_apply_smul,
    BinaryFivePointStabilizer.kernelDisplacement_mk]

theorem kernelCoordinates_conj {x : V} (hx : x ≠ 0)
    (g : pointStabilizer x) (k : pointKernel x) :
    Multiplicative.toAdd (kernelCoordinates hx (MulAut.conjNormal g k)) =
      pointAnnihilatorAction x g (Multiplicative.toAdd (kernelCoordinates hx k)) := by
  apply Subtype.ext
  ext v
  apply smul_left_injective (ZMod 2) hx
  dsimp only
  rw [kernelCoordinates_smul]
  change g.val (k.val.val (g.val.symm v)) - v =
    (Multiplicative.toAdd (kernelCoordinates hx k)).val (g.val.symm v) • x
  have h := congrArg g.val (kernelCoordinates_smul hx k (g.val.symm v))
  rw [map_smul, g.property, map_sub, g.val.apply_symm_apply] at h
  exact h.symm

private def sectionAction {G H : Type*} [Group G] [Group H]
    (π : G →* H) (s : H →* G) : H →* MulAut π.ker :=
  (MulAut.conjNormal : G →* MulAut π.ker).comp s

private def sectionEquiv {G H : Type*} [Group G] [Group H]
    (π : G →* H) (s : H →* G) (hs : Function.RightInverse s π) :
    SemidirectProduct π.ker H (sectionAction π s) ≃* G where
  toFun z := z.left.val * s z.right
  invFun g := ⟨⟨g * (s (π g))⁻¹, by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hs, mul_inv_cancel]⟩, π g⟩
  left_inv z := by
    apply SemidirectProduct.ext
    · apply Subtype.ext
      change z.left.val * s z.right * (s (π (z.left.val * s z.right)))⁻¹ = z.left.val
      rw [map_mul, (MonoidHom.mem_ker.mp z.left.property), hs, one_mul, mul_inv_cancel_right]
    · change π (z.left.val * s z.right) = z.right
      rw [map_mul, (MonoidHom.mem_ker.mp z.left.property), hs, one_mul]
  right_inv g := by
    change g * (s (π g))⁻¹ * s (π g) = g
    exact inv_mul_cancel_right _ _
  map_mul' a b := by
    change a.left.val * (s a.right * b.left.val * (s a.right)⁻¹) * s (a.right * b.right) = _
    rw [map_mul]
    group

variable [FiniteDimensional (ZMod 2) V]

noncomputable def quotientCoordinates {x : V} {d : ℕ}
    (b : annihilator x ≃ₗ[ZMod 2] Vector d) : BinaryLinear.GL (pointQuotient x) ≃* SL d :=
  (quotientAnnihilatorGroupEquiv x).trans
    ((linearGroupCongr b).trans (slEquivLinear d).symm)

noncomputable def translationCoordinates {x : V} (hx : x ≠ 0) {d : ℕ}
    (b : annihilator x ≃ₗ[ZMod 2] Vector d) : pointKernel x ≃* Multiplicative (Vector d) :=
  (kernelCoordinates hx).trans (AddEquiv.toMultiplicative b.toAddEquiv)

theorem translationCoordinates_conj {x : V} (hx : x ≠ 0) {d : ℕ}
    (b : annihilator x ≃ₗ[ZMod 2] Vector d) (g : pointStabilizer x) (k : pointKernel x) :
    translationCoordinates hx b (MulAut.conjNormal g k) =
      naturalAction d (quotientCoordinates b (pointQuotientAction x g))
        (translationCoordinates hx b k) := by
  apply Multiplicative.toAdd.injective
  change b (Multiplicative.toAdd (kernelCoordinates hx (MulAut.conjNormal g k))) = _
  rw [kernelCoordinates_conj, naturalAction_apply]
  rw [← slEquivLinear_apply]
  change _ = slEquivLinear d ((slEquivLinear d).symm
    (linearGroupCongr b (quotientAnnihilatorGroupEquiv x (pointQuotientAction x g))))
      (b (Multiplicative.toAdd (kernelCoordinates hx k)))
  rw [MulEquiv.apply_symm_apply, linearGroupCongr_apply, LinearEquiv.symm_apply_apply,
    ← pointAnnihilatorAction_eq]

noncomputable def pointAffineEquiv {x : V} (hx : x ≠ 0) {d : ℕ}
    (b : annihilator x ≃ₗ[ZMod 2] Vector d) : pointStabilizer x ≃* Affine d := by
  let f := Classical.choose (exists_pairing hx)
  have hf : f x = 1 := Classical.choose_spec (exists_pairing hx)
  let s := pointQuotientSection hf
  have hs : Function.RightInverse s (pointQuotientAction x) := pointQuotientSection_rightInverse hf
  exact (sectionEquiv (pointQuotientAction x) s hs).symm.trans
    (SemidirectProduct.congr (translationCoordinates hx b) (quotientCoordinates b) (by
      intro g
      ext k : 1
      change translationCoordinates hx b (MulAut.conjNormal (s g) k) = _
      rw [translationCoordinates_conj, hs]
      rfl))

theorem pointAffineEquiv_right {x : V} (hx : x ≠ 0) {d : ℕ}
    (b : annihilator x ≃ₗ[ZMod 2] Vector d) (g : pointStabilizer x) :
    (pointAffineEquiv hx b g).right = quotientCoordinates b (pointQuotientAction x g) := by rfl

theorem pointAffineEquiv_kernel {x : V} (hx : x ≠ 0) {d : ℕ}
    (b : annihilator x ≃ₗ[ZMod 2] Vector d) (k : pointKernel x) :
    pointAffineEquiv hx b k.val = SemidirectProduct.inl (translationCoordinates hx b k) := by
  have hk : pointQuotientAction x k.val = 1 := k.property
  apply SemidirectProduct.ext
  · change translationCoordinates hx b ⟨k.val *
      (pointQuotientSection (Classical.choose_spec (exists_pairing hx))
        (pointQuotientAction x k.val))⁻¹, _⟩ = translationCoordinates hx b k
    congr 1
    apply Subtype.ext
    simp [hk]
  · rw [pointAffineEquiv_right, hk, map_one]
    rfl
end CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.Binary.EndNodes.ParabolicAffine

end
