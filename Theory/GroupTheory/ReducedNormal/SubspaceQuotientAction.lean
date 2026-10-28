module
public import Theory.GroupTheory.ReducedNormal.OrbitReduced
public import Theory.Representation.NormalElementaryQuotient
public import Theory.Representation.BinaryOffender.CubicRatio.Equivariant
/-!
# The centralizer quotient of an invariant reduced subspace

The original multiplicative inclusion identifies an invariant subspace of
R₂(H) with a normal elementary subgroup of H. Its conjugation kernel is
exactly the centralizer of that subgroup. We construct the corresponding
group and linear equivalences, prove their literal conjugation formula, and
transport cubic bounds from the original quotient to the faithful action
image. This is the coordinate step between the source statements 3.1.8(1)
and 3.2.5, retaining the whole orbit rather than its chosen seed.
-/
public section
open Subgroup
open scoped IsMulCommutative
open Representation.BinaryOffender
namespace Theory.GroupTheory.ReducedNormal
variable {G : Type*} [Group G] (H : Subgroup G)
  (W : Submodule (ZMod 2) (Additive (ModuleGroup H)))

abbrev intrinsicSubspace : Subgroup H :=
  W.toAddSubgroup.toSubgroup'.map (ModuleGroup H).subtype

theorem intrinsicSubspace_eq : intrinsicSubspace H W = (subspaceImage H W).subgroupOf H :=
  (comap_map_eq_self_of_injective H.subtype_injective _).symm

instance intrinsicSubspace_elementary : IsElementaryAbelian 2 (intrinsicSubspace H W) :=
  IsElementaryAbelian.of_le (map_subtype_le _)

theorem intrinsicSubspace_normal
    (hW : (⊤ : Subgroup H) ≤ subspaceStabilizer (representation H) W) :
    (intrinsicSubspace H W).Normal := by
  refine ⟨?_⟩
  rintro _ ⟨v, hv, rfl⟩ g
  exact ⟨conjugation H g v, (hW (mem_top g) (Additive.ofMul v)).mpr hv, rfl⟩

theorem invariantActionHom_ker_centralizer
    (hW : (⊤ : Subgroup H) ≤ subspaceStabilizer (representation H) W) :
    (invariantActionHom (representation H) W hW).ker =
      centralizer (intrinsicSubspace H W : Set H) := by
  rw [invariantActionHom_ker]
  ext g
  simp only [mem_subspaceKernel, mem_top, true_and, mem_centralizer_iff]
  constructor
  · intro hf x hx
    obtain ⟨v, hv, rfl⟩ := hx
    have hh := congrArg (fun w : Additive (ModuleGroup H) => w.toMul.val)
      (hf (Additive.ofMul v) hv)
    change g * v.val * g⁻¹ = v.val at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  · intro hg v hv
    have hvQ : v.toMul.val ∈ intrinsicSubspace H W := ⟨v.toMul, hv, rfl⟩
    have hvg : v.toMul.val * g = g * v.toMul.val := hg _ hvQ
    apply Additive.toMul.injective
    apply Subtype.ext
    change g * v.toMul.val * g⁻¹ = v.toMul.val
    rw [← hvg, mul_inv_cancel_right]

noncomputable def intrinsicLinearMap : W →ₗ[ZMod 2] Additive (intrinsicSubspace H W) :=
  ({ toFun v := Additive.ofMul ⟨v.val.toMul.val, ⟨v.val.toMul, v.property, rfl⟩⟩
     map_zero' := rfl
     map_add' := fun _ _ => rfl } : W →+ Additive (intrinsicSubspace H W)).toZModLinearMap 2

theorem intrinsicLinearMap_bijective : Function.Bijective (intrinsicLinearMap H W) := by
  constructor
  · intro v w he
    apply Subtype.ext
    apply Additive.toMul.injective
    apply Subtype.ext
    exact congrArg (fun u : Additive (intrinsicSubspace H W) => u.toMul.val) he
  · intro u
    obtain ⟨v, hv, he⟩ := u.toMul.property
    refine ⟨⟨Additive.ofMul v, hv⟩, ?_⟩
    apply Additive.toMul.injective
    exact Subtype.ext he

noncomputable def intrinsicLinearEquiv : W ≃ₗ[ZMod 2] Additive (intrinsicSubspace H W) :=
  LinearEquiv.ofBijective _ (intrinsicLinearMap_bijective H W)

@[simp] theorem intrinsicLinearEquiv_apply (w : W) :
    ((intrinsicLinearEquiv H W w).toMul : H) = w.val.toMul.val := by rfl

variable (hW : (⊤ : Subgroup H) ≤ subspaceStabilizer (representation H) W)
variable [(intrinsicSubspace H W).Normal]

noncomputable def intrinsicQuotientEquiv :
    H ⧸ centralizer (intrinsicSubspace H W : Set H) ≃*
      subspaceActionImage (representation H) W :=
  QuotientGroup.liftEquiv _ (invariantActionHom_surjective (representation H) W hW)
    (invariantActionHom_ker_centralizer H W hW).symm

@[simp] theorem intrinsicQuotientEquiv_mk (g : H) :
    intrinsicQuotientEquiv H W hW (QuotientGroup.mk' _ g) =
      invariantActionHom (representation H) W hW g := by rfl

theorem intrinsicLinearEquiv_equivariant
    (g : H ⧸ centralizer (intrinsicSubspace H W : Set H)) (w : W) :
    intrinsicLinearEquiv H W
      (subspaceImageRepresentation (representation H) W (intrinsicQuotientEquiv H W hW g) w) =
    Representation.NormalElementaryQuotient.representation (intrinsicSubspace H W)
      (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) g
        (intrinsicLinearEquiv H W w) := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective _ g
  apply Additive.toMul.injective
  apply Subtype.ext
  rw [Representation.NormalElementaryQuotient.representation_apply]
  rfl

include hW in
theorem cubicRatio_image_le_of_intrinsic_quotient [Finite G] (n : ℕ)
    (hb : cubicRatio (Representation.NormalElementaryQuotient.representation
      (intrinsicSubspace H W) (QuotientGroup.mk' _)
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)) ≤ n) :
    cubicRatio (subspaceImageRepresentation (representation H) W) ≤ n := by
  apply cubicRatio_le_nat_of_equivariant _ _
    (intrinsicQuotientEquiv H W hW).toMonoidHom
    (intrinsicQuotientEquiv H W hW).injective
    (intrinsicLinearEquiv H W).symm ?_ n hb
  intro g w
  apply (intrinsicLinearEquiv H W).injective
  rw [LinearEquiv.apply_symm_apply]
  simpa only [LinearEquiv.apply_symm_apply, MulEquiv.coe_toMonoidHom] using
    (intrinsicLinearEquiv_equivariant H W hW g ((intrinsicLinearEquiv H W).symm w)).symm
end Theory.GroupTheory.ReducedNormal
