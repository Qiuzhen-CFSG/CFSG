module
public import Theory.Representation.AlternatingFiveMovedPair.Natural
public import Theory.Representation.OrthogonalFourPlusMatrix.Commutant
public import Theory.Representation.QuasithinRankTwoInvolutionExclusions.OrthogonalFour.TensorModel
import Mathlib.Tactic.FinCases

/-!
# The commutant of the two natural descent tensor types

The invariant alternating pairing identifies the natural tensor with the
matrix determinant module, whose additive commutant consists of field scalars.
For the two different descent types, opposite trace-omega matrices have the
same left trace and different right traces. Their trace difference is the
identity in F4, forcing every additive cross intertwiner to vanish. The binary
commutant of the actual direct sum therefore consists of independent scalars.

Source: Aschbacher–Smith, quasithin manuscript, D.3.5, printed pp.195–196.
-/

@[expose] public noncomputable section
open scoped TensorProduct
namespace Representation.AlternatingFiveMovedPair.NaturalCommutant
open BinaryOffender.NaturalTensor

variable {K : Type*} [Field K]

theorem tensor_centralizer_scalar (f : TensorSpace K →+ TensorSpace K)
    (hf : ∀ g, ∀ v, f (tensorAction K g v) = tensorAction K g (f v)) :
    ∃ c : K, ∀ v, f v = c • v := by
  let E := RankTwo.OrthogonalFour.tensorCoordinates (K := K)
  have he (g : ClassicalOrthogonal.FourPlusMatrix.PairSL (F := K)) (v : TensorSpace K) :
      E (tensorAction K g v) = ClassicalOrthogonal.FourPlusMatrix.matrixAction g (E v) := by
    exact RankTwo.OrthogonalFour.tensorCoordinates_equivariant g v
  let q := E.toAddEquiv.toAddMonoidHom.comp (f.comp E.symm.toAddEquiv.toAddMonoidHom)
  obtain ⟨c, hc⟩ := ClassicalOrthogonal.FourPlusMatrix.centralizer_scalar q (by
    intro g M
    change E (f (E.symm (ClassicalOrthogonal.FourPlusMatrix.matrixAction g M))) =
      ClassicalOrthogonal.FourPlusMatrix.matrixAction g (E (f (E.symm M)))
    rw [← E.apply_symm_apply M, ← he, E.symm_apply_apply, hf, he]
    simp only [E.symm_apply_apply])
  refine ⟨c, fun v => E.injective ?_⟩
  have h := hc (E v)
  change E (f (E.symm (E v))) = c • E v at h
  simpa only [E.symm_apply_apply, map_smul] using h

abbrev F := SL2FourNatural.F
abbrev SL := SL2FourNatural.SL
abbrev Tensor := TensorSpace F
def leftTrace : SL := ⟨!![0, 1; 1, QuadraticAlgebra.omega], by decide +kernel⟩
def rightTrace : SL := ⟨!![QuadraticAlgebra.omega, 1; 1, 0], by decide +kernel⟩
abbrev omega : F := QuadraticAlgebra.omega

theorem natural_trace (v : Fin 2 → F) :
    specialLinearNatural 2 leftTrace v + specialLinearNatural 2 rightTrace v = omega • v := by
  revert v
  decide +kernel

theorem natural_twisted_trace (v : Fin 2 → F) :
    specialLinearNatural 2 (SL2FourNatural.slFrobenius leftTrace) v +
      specialLinearNatural 2 (SL2FourNatural.slFrobenius rightTrace) v = omega ^ 2 • v := by
  revert v
  decide +kernel

private theorem tensor_tmul (g : SL × SL) (x y : Fin 2 → F) :
    tensorAction F g (x ⊗ₜ[F] y) =
      (specialLinearNatural 2 g.1 x) ⊗ₜ[F] (specialLinearNatural 2 g.2 y) := rfl

theorem tensor_left_trace (v : Tensor) :
    tensorAction F (leftTrace, 1) v + tensorAction F (rightTrace, 1) v = omega • v := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    simp only [tensor_tmul, map_one, Module.End.one_apply]
    change (specialLinearNatural 2 leftTrace x ⊗ₜ[F] y) +
      (specialLinearNatural 2 rightTrace x ⊗ₜ[F] y) = omega • (x ⊗ₜ[F] y)
    rw [← TensorProduct.add_tmul, natural_trace, TensorProduct.smul_tmul']
  | add x y hx hy =>
    simp only [map_add, smul_add]
    rw [add_add_add_comm, hx, hy]

theorem tensor_right_trace (v : Tensor) :
    tensorAction F (1, leftTrace) v + tensorAction F (1, rightTrace) v = omega • v := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    simp only [tensor_tmul, map_one, Module.End.one_apply]
    change (x ⊗ₜ[F] specialLinearNatural 2 leftTrace y) +
      (x ⊗ₜ[F] specialLinearNatural 2 rightTrace y) = omega • (x ⊗ₜ[F] y)
    rw [← TensorProduct.tmul_add, natural_trace, TensorProduct.tmul_smul]
  | add x y hx hy =>
    simp only [map_add, smul_add]
    rw [add_add_add_comm, hx, hy]

theorem tensor_right_twisted_trace (v : Tensor) :
    tensorAction F (1, SL2FourNatural.slFrobenius leftTrace) v +
      tensorAction F (1, SL2FourNatural.slFrobenius rightTrace) v = omega ^ 2 • v := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    simp only [tensor_tmul, map_one, Module.End.one_apply]
    change (x ⊗ₜ[F] specialLinearNatural 2 (SL2FourNatural.slFrobenius leftTrace) y) +
      (x ⊗ₜ[F] specialLinearNatural 2 (SL2FourNatural.slFrobenius rightTrace) y) =
        omega ^ 2 • (x ⊗ₜ[F] y)
    rw [← TensorProduct.tmul_add, natural_twisted_trace, TensorProduct.tmul_smul]
  | add x y hx hy =>
    simp only [map_add, smul_add]
    rw [add_add_add_comm, hx, hy]

/-- The two tensor types have no additive intertwiners. -/
theorem cross_intertwiner_eq_zero (f : Tensor →+ Tensor)
    (hf : ∀ g : SL × SL, ∀ v,
      f (tensorAction F g v) =
        tensorAction F (g.1, SL2FourNatural.slFrobenius g.2) (f v)) : f = 0 := by
  apply AddMonoidHom.ext
  intro v
  change f v = 0
  have hl : f (omega • v) = omega • f v := by
    rw [← tensor_left_trace, f.map_add, hf, hf]
    simpa only [map_one] using tensor_left_trace (f v)
  have hr : f (omega • v) = omega ^ 2 • f v := by
    rw [← tensor_right_trace, f.map_add, hf, hf]
    exact tensor_right_twisted_trace (f v)
  have ho : omega + omega ^ 2 = (1 : F) := by decide +kernel
  have hz : (omega + omega ^ 2) • f v = 0 := by
    rw [add_smul, ← hl, ← hr]
    have h := @two_smul F Tensor _ _ _ (f (omega • v))
    simpa only [show (2 : F) = 0 by decide +kernel, zero_smul] using h.symm
  simpa only [ho, one_smul] using hz

/-- The reverse additive intertwiner vanishes as well. -/
theorem reverse_cross_intertwiner_eq_zero (f : Tensor →+ Tensor)
    (hf : ∀ g : SL × SL, ∀ v,
      f (tensorAction F (g.1, SL2FourNatural.slFrobenius g.2) v) =
        tensorAction F g (f v)) : f = 0 := by
  apply cross_intertwiner_eq_zero f
  intro g v
  simpa only [SL2FourNatural.slFrobenius_involutive] using
    hf (g.1, SL2FourNatural.slFrobenius g.2) v

theorem twisted_tensor_centralizer_scalar (f : Tensor →+ Tensor)
    (hf : ∀ g : SL × SL, ∀ v,
      f (tensorAction F (g.1, SL2FourNatural.slFrobenius g.2) v) =
        tensorAction F (g.1, SL2FourNatural.slFrobenius g.2) (f v)) :
    ∃ c : F, ∀ v, f v = c • v := by
  apply tensor_centralizer_scalar f
  intro g v
  simpa only [SL2FourNatural.slFrobenius_involutive] using
    hf (g.1, SL2FourNatural.slFrobenius g.2) v

/-- The first literal binary tensor type has only scalar additive endomorphisms. -/
theorem first_centralizer_scalar (f : Natural.Tensor →+ Natural.Tensor)
    (hf : ∀ g, ∀ v, f (Natural.first g v) = Natural.first g (f v)) :
    ∃ c : F, ∀ v, f v = c • v := tensor_centralizer_scalar f hf

/-- The second literal binary tensor type has only scalar additive endomorphisms. -/
theorem second_centralizer_scalar (f : Natural.Tensor →+ Natural.Tensor)
    (hf : ∀ g, ∀ v, f (Natural.second g v) = Natural.second g (f v)) :
    ∃ c : F, ∀ v, f v = c • v := twisted_tensor_centralizer_scalar f hf

/-- No additive map intertwines the two literal descent constituents. -/
theorem first_second_intertwiner_zero (f : Natural.Tensor →+ Natural.Tensor)
    (hf : ∀ g, ∀ v, f (Natural.first g v) = Natural.second g (f v)) : f = 0 :=
  cross_intertwiner_eq_zero f hf

/-- No additive map intertwines the descent constituents in the reverse direction. -/
theorem second_first_intertwiner_zero (f : Natural.Tensor →+ Natural.Tensor)
    (hf : ∀ g, ∀ v, f (Natural.second g v) = Natural.first g (f v)) : f = 0 :=
  reverse_cross_intertwiner_eq_zero f hf

/-- The two actual binary descent constituents are inequivalent. -/
theorem first_second_not_equiv : ¬ Nonempty (Representation.Equiv Natural.first Natural.second) := by
  rintro ⟨e⟩
  have hz := first_second_intertwiner_zero e.toLinearEquiv.toAddEquiv.toAddMonoidHom
    (fun g v => LinearMap.congr_fun (e.isIntertwining' g) v)
  obtain ⟨v, hv⟩ := exists_ne (0 : Natural.Tensor)
  apply hv
  apply e.toLinearEquiv.injective
  have h := DFunLike.congr_fun hz v
  change e.toLinearEquiv v = 0 at h
  simpa only [map_zero] using h

/-- The actual natural pair has independent scalar blocks as its entire binary commutant. -/
theorem centralizer_block_scalars (q : Module.End (ZMod 2) Natural.Space)
    (hq : ∀ g, ∀ v, q (Natural.action g v) = Natural.action g (q v)) :
    ∃ a b : F, ∀ v, q v = (a • v.1, b • v.2) := by
  let inl := LinearMap.inl (ZMod 2) Natural.Tensor Natural.Tensor
  let inr := LinearMap.inr (ZMod 2) Natural.Tensor Natural.Tensor
  let fst := LinearMap.fst (ZMod 2) Natural.Tensor Natural.Tensor
  let snd := LinearMap.snd (ZMod 2) Natural.Tensor Natural.Tensor
  let q₁₁ := (fst.comp (q.comp inl)).toAddMonoidHom
  let q₁₂ := (fst.comp (q.comp inr)).toAddMonoidHom
  let q₂₁ := (snd.comp (q.comp inl)).toAddMonoidHom
  let q₂₂ := (snd.comp (q.comp inr)).toAddMonoidHom
  have h₁₁ (g : SL × SL) (v : Natural.Tensor) :
      q₁₁ (Natural.first g v) = Natural.first g (q₁₁ v) := by
    have h := congrArg Prod.fst (hq g (v, 0))
    change (q (Natural.first g v, Natural.second g 0)).1 = Natural.first g (q (v, 0)).1 at h
    simpa [q₁₁, fst, inl] using h
  have h₁₂ (g : SL × SL) (v : Natural.Tensor) :
      q₁₂ (Natural.second g v) = Natural.first g (q₁₂ v) := by
    have h := congrArg Prod.fst (hq g (0, v))
    change (q (Natural.first g 0, Natural.second g v)).1 = Natural.first g (q (0, v)).1 at h
    simpa [q₁₂, fst, inr] using h
  have h₂₁ (g : SL × SL) (v : Natural.Tensor) :
      q₂₁ (Natural.first g v) = Natural.second g (q₂₁ v) := by
    have h := congrArg Prod.snd (hq g (v, 0))
    change (q (Natural.first g v, Natural.second g 0)).2 = Natural.second g (q (v, 0)).2 at h
    simpa [q₂₁, snd, inl] using h
  have h₂₂ (g : SL × SL) (v : Natural.Tensor) :
      q₂₂ (Natural.second g v) = Natural.second g (q₂₂ v) := by
    have h := congrArg Prod.snd (hq g (0, v))
    change (q (Natural.first g 0, Natural.second g v)).2 = Natural.second g (q (0, v)).2 at h
    simpa [q₂₂, snd, inr] using h
  obtain ⟨a, ha⟩ := first_centralizer_scalar q₁₁ h₁₁
  obtain ⟨b, hb⟩ := second_centralizer_scalar q₂₂ h₂₂
  have h₁₂zero := second_first_intertwiner_zero q₁₂ h₁₂
  have h₂₁zero := first_second_intertwiner_zero q₂₁ h₂₁
  refine ⟨a, b, fun v => ?_⟩
  have hv : v = (v.1, 0) + (0, v.2) := by simp
  have h₁₂v : (q (0, v.2)).1 = 0 := DFunLike.congr_fun h₁₂zero v.2
  have h₂₁v : (q (v.1, 0)).2 = 0 := DFunLike.congr_fun h₂₁zero v.1
  calc
    q v = q (v.1, 0) + q (0, v.2) := by rw [← map_add, ← hv]
    _ = (a • v.1, b • v.2) := by
      apply Prod.ext
      · change (q (v.1, 0)).1 + (q (0, v.2)).1 = a • v.1
        rw [h₁₂v, add_zero]
        exact ha v.1
      · change (q (v.1, 0)).2 + (q (0, v.2)).2 = b • v.2
        rw [h₂₁v, zero_add]
        exact hb v.2

end Representation.AlternatingFiveMovedPair.NaturalCommutant

