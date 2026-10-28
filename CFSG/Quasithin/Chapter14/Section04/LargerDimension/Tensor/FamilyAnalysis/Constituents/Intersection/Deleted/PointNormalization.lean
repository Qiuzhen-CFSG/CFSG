module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.FamilyAnalysis.Constituents.Intersection.Deleted.Coordinates
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.FamilyAnalysis.Constituents.Intersection.Reduction
public import Theory.Representation.BinaryPermutation.ThreeTensor

/-!
# Normalizing the deleted Sylow-fixed tensor point

Conjugate the standard Klein four into the given Sylow two-subgroup. In the
five-point augmentation core its fixed space is the line on `(1,1,1,1,0)`.
The two natural-module tensor coordinates then give a pure tensor, and
transporting back gives an actual permutation of that weight-four vector.
The coordinate equivalence explicitly reverses the source tensor factors
when applying the `ThreeTensor` fixed-space calculation.

Evaluation at a nonzero coordinate of the weight-four factor contracts the
literal displacement equation to the natural factor. The selected element
has trivial five-point coordinate, so this contraction supplies the required
natural-module displacement preimage. No purity, singularity or position of
the point is assumed. The argument works for every subgroup containing A₅,
in particular both source cases A₅ and S₅.

`point_normalization` discharges `PointNormalization` in the existing
`actorPlacement_of_normalization` consumer. The separate `ActorGenerators`
premise remains with its independent producer and final source assembly.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
14.4.10, first proof paragraph, printed p.1010, in case 14.4.2(5), p.1006.
The Sylow-fixed point is supplied by 12.8.12, pp.854–855, in the setup
of 14.3.10, p.993.
-/

public section

open Subgroup TensorProduct Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor
variable {D : Subgroup Five} {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
namespace Deleted

private theorem normalization_fixed_core (v : Core)
    (h₁ : permAction first.val v = v) (h₂ : permAction second.val v = v) :
    v = v.val 0 • point := by
  have h : ∀ x : BinaryPermutation.Full (Fin 5), (∑ i, x i) = 0 →
      BinaryPermutation.representation (Fin 5) first.val x = x →
      BinaryPermutation.representation (Fin 5) second.val x = x →
      x = x 0 • ![1,1,1,1,0] := by decide
  exact Subtype.ext (h v.val v.property (congrArg Subtype.val h₁) (congrArg Subtype.val h₂))

private theorem normalization_fixed_tensor (z : Core ⊗[ZMod 2] Natural)
    (h₁ : BinaryPermutation.ThreeTensor.action permAction (first.val, 1) z = z)
    (h₂ : BinaryPermutation.ThreeTensor.action permAction (second.val, 1) z = z) :
    ∃ w : Natural, z = point ⊗ₜ[ZMod 2] w := by
  let p := BinaryPermutation.ThreeTensor.pairEquiv z
  have hfirst := congrArg BinaryPermutation.ThreeTensor.pairEquiv h₁
  have hsecond := congrArg BinaryPermutation.ThreeTensor.pairEquiv h₂
  rw [BinaryPermutation.ThreeTensor.pairEquiv_equivariant] at hfirst hsecond
  have hp₁ := normalization_fixed_core p.1
    (congrArg Prod.fst hfirst) (congrArg Prod.fst hsecond)
  have hp₂ := normalization_fixed_core p.2
    (congrArg Prod.snd hfirst) (congrArg Prod.snd hsecond)
  let w : Natural := ⟨![p.1.val 0, p.2.val 0, -p.1.val 0 - p.2.val 0], by
    rw [BinaryPermutation.mem_core, Fin.sum_univ_three]
    change p.1.val 0 + p.2.val 0 + (-p.1.val 0 - p.2.val 0) = 0
    ring⟩
  refine ⟨w, BinaryPermutation.ThreeTensor.pairEquiv.injective ?_⟩
  rw [BinaryPermutation.ThreeTensor.pairEquiv_tmul]
  exact Prod.ext hp₁ hp₂

private noncomputable def normalizationEquiv (f : V ≃ₗ[ZMod 2] Core) :
    IntersectionSpace V ≃ₗ[ZMod 2] (Core ⊗[ZMod 2] Natural) :=
  (TensorProduct.congr (LinearEquiv.refl (ZMod 2) Natural) f).trans
    (TensorProduct.comm (ZMod 2) Natural Core)

private theorem normalizationEquiv_tmul (f : V ≃ₗ[ZMod 2] Core) (n : Natural) (v : V) :
    normalizationEquiv f (n ⊗ₜ[ZMod 2] v) = f v ⊗ₜ[ZMod 2] n := rfl

private theorem normalizationEquiv_equivariant (σ : Representation (ZMod 2) D V)
    (f : V ≃ₗ[ZMod 2] Core)
    (hf : ∀ (a : D) (v : V), f (σ a v) = permAction a.val (f v))
    (a : Three × D) (z : IntersectionSpace V) :
    normalizationEquiv f (sourceTensorAction σ a z) =
      BinaryPermutation.ThreeTensor.action permAction (a.2.val, a.1) (normalizationEquiv f z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul n v =>
    change f (σ a.2 v) ⊗ₜ[ZMod 2] naturalAction a.1 n = _
    rw [hf]
    rfl
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy

private theorem normalization_sylow_coordinates (hAD : AltFive ≤ D)
    (σ : Representation (ZMod 2) D V) (f : V ≃ₗ[ZMod 2] Core)
    (hf : ∀ (a : D) (v : V), f (σ a v) = permAction a.val (f v))
    (d : ComplementIntersectionData σ) :
    ∃ g : Five, ∃ n : Natural, d.point = n ⊗ₜ[ZMod 2] f.symm (permAction g point) := by
  let ι : AltFive →* Three × D := (MonoidHom.inr _ _).comp (inclusion hAD)
  obtain ⟨Q, hKQ⟩ := (BinaryPermutation.CubicFixedSpace.Five.klein_isPGroup.map ι).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Three × D) Q d.sylow
  have hP : (Q : Subgroup _).map (MulAut.conj g).toMonoidHom = (d.sylow : Subgroup _) := by
    rw [← hg, Sylow.smul_def, Sylow.pointwise_smul_def, Subgroup.pointwise_smul_def]
    rfl
  let ρ := sourceTensorAction σ
  have hinv (x : IntersectionSpace V) : ρ g⁻¹ (ρ g x) = x := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have hginv (x : IntersectionSpace V) : ρ g (ρ g⁻¹ x) = x := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have hK (a : AltFive) (ha : a ∈ BinaryPermutation.CubicFixedSpace.Five.klein) :
      ρ (ι a) (ρ g⁻¹ d.point) = ρ g⁻¹ d.point := by
    have hm : g * ι a * g⁻¹ ∈ (d.sylow : Subgroup _) := by
      rw [← hP]
      exact ⟨ι a, hKQ (Subgroup.mem_map_of_mem ι ha), rfl⟩
    have hh := congrArg (ρ g⁻¹) (d.point_fixed _ hm)
    change ρ g⁻¹ (ρ (g * ι a * g⁻¹) d.point) = _ at hh
    simpa only [map_mul, Module.End.mul_apply, hinv] using hh
  have hfix (a : AltFive) (ha : a ∈ BinaryPermutation.CubicFixedSpace.Five.klein) :
      BinaryPermutation.ThreeTensor.action permAction (a.val, 1)
        (normalizationEquiv f (ρ g⁻¹ d.point)) = normalizationEquiv f (ρ g⁻¹ d.point) := by
    have hh := congrArg (normalizationEquiv f) (hK a ha)
    rw [normalizationEquiv_equivariant σ f hf] at hh
    exact hh
  obtain ⟨w, hw⟩ := normalization_fixed_tensor (normalizationEquiv f (ρ g⁻¹ d.point))
    (hfix first BinaryPermutation.CubicFixedSpace.Five.first_mem)
    (hfix second BinaryPermutation.CubicFixedSpace.Five.second_mem)
  have hx : ρ g⁻¹ d.point = w ⊗ₜ[ZMod 2] f.symm point := by
    apply (normalizationEquiv f).injective
    simpa only [normalizationEquiv_tmul, f.apply_symm_apply] using hw
  have he : σ g.2 (f.symm point) = f.symm (permAction g.2.val point) := by
    apply f.injective
    simp only [hf, f.apply_symm_apply]
  refine ⟨g.2.val, naturalAction g.1 w, ?_⟩
  rw [← hginv d.point, hx]
  change naturalAction g.1 w ⊗ₜ[ZMod 2] σ g.2 (f.symm point) = _
  rw [he]

private noncomputable def normalizationContract (ℓ : V →ₗ[ZMod 2] ZMod 2) :
    IntersectionSpace V →ₗ[ZMod 2] Natural :=
  (TensorProduct.rid (ZMod 2) Natural).toLinearMap.comp (TensorProduct.map LinearMap.id ℓ)

private theorem normalizationContract_tmul (ℓ : V →ₗ[ZMod 2] ZMod 2) (n : Natural) (v : V) :
    normalizationContract ℓ (n ⊗ₜ[ZMod 2] v) = ℓ v • n := rfl

private theorem normalizationContract_equivariant (σ : Representation (ZMod 2) D V)
    (ℓ : V →ₗ[ZMod 2] ZMod 2) (a : Three × D) (ha : a.2 = 1) (z : IntersectionSpace V) :
    normalizationContract ℓ (sourceTensorAction σ a z) =
      naturalAction a.1 (normalizationContract ℓ z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul n v =>
    change ℓ (σ a.2 v) • naturalAction a.1 n = naturalAction a.1 (ℓ v • n)
    rw [ha, map_one, Module.End.one_apply, map_smul]
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy

/-- Sylow fixation gives the weight-four tensor coordinates, and the actual
first displacement space supplies the natural-factor preimage. -/
theorem point_normalization (hAD : AltFive ≤ D) (_hcase : D = ⊤ ∨ D = AltFive)
    (σ : Representation (ZMod 2) D V) : PointNormalization σ := by
  intro f hf d
  obtain ⟨g, n, hn⟩ := normalization_sylow_coordinates hAD σ f hf d
  let ℓ : V →ₗ[ZMod 2] ZMod 2 :=
    ((LinearMap.proj (g 0)).comp (BinaryPermutation.core (Fin 5)).subtype).comp f.toLinearMap
  have hℓ : ℓ (f.symm (permAction g point)) = 1 := by
    change (f (f.symm (permAction g point))).val (g 0) = 1
    rw [f.apply_symm_apply]
    change point.val (g.symm (g 0)) = 1
    rw [g.symm_apply_apply]
    rfl
  have hm := d.point_mem_first
  rw [d.first_eq_range] at hm
  obtain ⟨y, hy⟩ := hm
  refine ⟨{
    coordinate := g
    natural := n
    preimage := normalizationContract ℓ y
    displacement := ?_
    point_eq := hn }⟩
  have hh := congrArg (normalizationContract ℓ) hy
  change normalizationContract ℓ (sourceTensorAction σ d.element y - y) =
    normalizationContract ℓ d.point at hh
  rw [map_sub, normalizationContract_equivariant σ ℓ d.element
    (element_second_eq_one hAD d), hn, normalizationContract_tmul, hℓ, one_smul] at hh
  exact hh

/-- Apply the proved point normalization to the existing placement consumer.
Only the independent actor-generator obligation remains. -/
theorem actorPlacement_of_actorGenerators (hAD : AltFive ≤ D)
    (hcase : D = ⊤ ∨ D = AltFive) (σ : Representation (ZMod 2) D V)
    (hactor : ActorGenerators hAD σ) : ActorPlacement hAD σ :=
  actorPlacement_of_normalization (point_normalization hAD hcase σ) hactor

end Deleted
end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor

end
