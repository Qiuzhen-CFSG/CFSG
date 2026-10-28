module
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourSection

/-!
# The original plane actor supplements its pointwise centralizer

The pointwise fixer of the Hermitian corner in the inner image is exactly
the plane radical. Thus an inner actor fixing that corner has the same
module action as an element of the marked A. Their quotient lies in the
original Sylow centralizer of V, which supplies the whole kernel Q.

The Chapter12 application takes X = O₂(N_L(U)^∞) and Q = O₂(LT).
Source: Aschbacher–Smith H.4.6(2) and 8.2.10(3), printed pp.382,721.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
open scoped IsMulCommutative MatrixGroups commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter8.Section02.HermitianSource
open ChapterE
variable {G : Type*} [Group G]
set_option backward.isDefEq.respectTransparency false

/-- The literal marked actor supplements every inner corner fixer in T,
retaining the full Sylow centralizer kernel. -/
theorem marked_plane_centralizer_supplement
    (V A X T Q : Subgroup G) [IsElementaryAbelian 2 V]
    (hAT : A ≤ T) (hXT : X ≤ T) (hTN : T ≤ normalizer (V : Set G))
    (hQ : T ⊓ centralizer (V : Set G) ≤ Q)
    (e : Additive V ≃ₗ[ZMod 2] Space 1)
    (f : Automizer V →* (Space 1 ≃ₗ[ZMod 2] Space 1)) (hf : Function.Injective f)
    (he : ∀ a v, e (automizerRepresentation V a v) = f a (e v))
    (hA : (inducedAutomizer V A).map f = UnipotentRadicals.plane 1)
    (hX : (inducedAutomizer V X).map f ≤ binaryImage 1)
    (hXC : X ≤ centralizer (V ⊓ centralizer (A : Set G) : Set G)) :
    X ≤ A ⊔ Q := by
  let α := V.normalizerMonoidHom.rangeRestrict
  intro x hx
  let xN : normalizer (V : Set G) := ⟨x,hTN (hXT hx)⟩
  have hxA : f (α xN) ∈ UnipotentRadicals.plane 1 := by
    apply (field_four_plane_pointwise_stabilizer _ (hX (mem_map_of_mem f
      (show α xN ∈ inducedAutomizer V X from ⟨xN,hx,rfl⟩)))).mp
    intro Z hZ
    obtain ⟨v,rfl⟩ := e.surjective Z
    have hvC : (v.toMul : G) ∈ centralizer (A : Set G) := by
      apply (mem_fixedSpace_inducedAutomizer V A (hAT.trans hTN) v).mp
      intro a
      apply e.injective
      change e (automizerRepresentation V a.val v) = e v
      rw [he]
      exact hZ ⟨f a.val,hA ▸ mem_map_of_mem f a.property⟩
    rw [←he]
    apply congrArg e
    apply Additive.toMul.injective
    apply Subtype.ext
    change x * (v.toMul : G) * x⁻¹ = (v.toMul : G)
    rw [←hXC hx _ ⟨v.toMul.property,hvC⟩,mul_assoc,mul_inv_cancel,mul_one]
  obtain ⟨b,hb,heq⟩ := (show f (α xN) ∈ (inducedAutomizer V A).map f from hA.symm ▸ hxA)
  obtain ⟨a,ha,rfl⟩ := hb
  have heq' : α a = α xN := hf heq
  have hc : xN * a⁻¹ ∈ α.ker := by
    change α (xN * a⁻¹) = 1
    rw [map_mul,map_inv,heq',mul_inv_cancel]
  have hc' : x * (a : G)⁻¹ ∈ centralizer (V : Set G) := by
    rw [show α.ker = (centralizer (V : Set G)).subgroupOf (normalizer (V : Set G)) by
      rw [MonoidHom.ker_rangeRestrict,normalizerMonoidHom_ker]] at hc
    exact hc
  have hq : x * (a : G)⁻¹ ∈ Q := hQ ⟨T.mul_mem (hXT hx) (T.inv_mem (hAT ha)),hc'⟩
  have hh := (A ⊔ Q).mul_mem (mem_sup_right hq) (mem_sup_left ha)
  change x * (a : G)⁻¹ * (a : G) ∈ A ⊔ Q at hh
  simpa only [inv_mul_cancel_right] using hh

end CFSG.Quasithin.Chapter8.Section02.HermitianSource
