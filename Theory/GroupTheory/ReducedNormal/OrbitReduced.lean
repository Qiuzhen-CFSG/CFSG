module

public import Theory.GroupTheory.ReducedNormal.Representation
public import Theory.Representation.BinaryOffender.InvariantAction

/-!
# Reducedness of an invariant subspace in the original group

For an invariant binary subspace of R₂(H), its multiplicative image is a
normal elementary abelian subgroup of H. The faithful action on that
subspace has exactly the literal centralizer as its kernel. If the action
image has trivial two-core, this identifies its centralizer quotient as
reduced and proves membership in the original R₂-family.

This is the conversion of D.3.4(1) into Aschbacher–Smith, Lemma 3.2.2(2),
combined manuscript of 1 March 2004, printed p.579.
-/

public section
open Subgroup
open scoped IsMulCommutative
open Representation.BinaryOffender
namespace Theory.GroupTheory.ReducedNormal
variable {G : Type*} [Group G]

/-- Centralization of the literal ambient subgroup means pointwise
fixation in its original binary representation. -/
theorem representation_fixes_of_centralizes_subspaceImage (H : Subgroup G)
    (W : Submodule (ZMod 2) (Additive (ModuleGroup H))) (g : H)
    (hg : (g : G) ∈ centralizer (subspaceImage H W : Set G))
    (v : Additive (ModuleGroup H)) (hv : v ∈ W) : representation H g v = v := by
  have hm : (v.toMul.val : G) ∈ subspaceImage H W :=
    mem_map_of_mem H.subtype (mem_map_of_mem (ModuleGroup H).subtype hv)
  have hc := mem_centralizer_iff.mp hg _ hm
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Subtype.ext
  change (g : G) * v.toMul.val.val * (g : G)⁻¹ = v.toMul.val.val
  rw [← hc, mul_inv_cancel_right]

/-- Reducedness is established for the actual subgroup of H represented
by the invariant subspace, using its original conjugation action. -/
theorem subspaceImage_isPReduced_of_action_core (H : Subgroup G)
    (W : Submodule (ZMod 2) (Additive (ModuleGroup H)))
    (hW : (⊤ : Subgroup H) ≤ subspaceStabilizer (representation H) W)
    (hc : pCore 2 (subspaceActionImage (representation H) W) = ⊥) :
    IsPReduced 2 ((subspaceImage H W).subgroupOf H) := by
  let Q : Subgroup H := W.toAddSubgroup.toSubgroup'.map (ModuleGroup H).subtype
  have hQ : Q.Normal := by
    refine ⟨?_⟩
    rintro _ ⟨v, hv, rfl⟩ g
    exact ⟨conjugation H g v, (hW (mem_top g) (Additive.ofMul v)).mpr hv, rfl⟩
  let := hQ
  have he : (subspaceImage H W).subgroupOf H = Q :=
    comap_map_eq_self_of_injective H.subtype_injective Q
  rw [he]
  let f := invariantActionHom (representation H) W hW
  have hk : f.ker = centralizer (Q : Set H) := by
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
      have hvQ : v.toMul.val ∈ Q := ⟨v.toMul, hv, rfl⟩
      have hvg : v.toMul.val * g = g * v.toMul.val := hg _ hvQ
      apply Additive.toMul.injective
      apply Subtype.ext
      change g * v.toMul.val * g⁻¹ = v.toMul.val
      rw [← hvg, mul_inv_cancel_right]
  refine ⟨hQ, IsElementaryAbelian.of_le (map_subtype_le _), ?_⟩
  let e := QuotientGroup.liftEquiv (centralizer (Q : Set H))
    (invariantActionHom_surjective (representation H) W hW) hk.symm
  have hm := pCore_map_iso 2 e
  rw [hc] at hm
  exact (map_eq_bot_iff_of_injective _ e.injective).mp hm

end Theory.GroupTheory.ReducedNormal
