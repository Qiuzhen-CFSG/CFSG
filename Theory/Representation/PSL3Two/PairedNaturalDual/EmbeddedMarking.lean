module
public import Theory.Representation.PSL3Two.NaturalDualNormalizerMarking
public import Theory.Representation.PSL3Two.PairedNaturalDual

/-!
# Constructing two simultaneous natural--dual component markings

An invariant embedded natural--dual module identifies the normal component's
full action. Transporting the ambient action into these same coordinates and
using the faithful linear normalizer constructs its automorphism marking.
For two components, the original cross-centralization identities determine
all four restrictions of the two actor maps. Both embeddings and the fixed
supplement are retained, so the paired quadratic estimates concern the same
whole module.

Source application: Aschbacher--Smith 14.6.24(3), printed pp.1039--1041.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace BinaryLinearThree.NaturalDual
variable {H E : Type*} [_root_.Group H] [AddCommGroup E] [Module (ZMod 2) E]

/-- Extend the actual natural--dual component coordinates to its ambient normalizer. -/
theorem exists_embedded_automorphism_marking
    (ρ : Representation (ZMod 2) H E)
    (κ : Group →* H) (hκ : Function.Injective κ) (hn : κ.range.Normal)
    (e : Space →ₗ[ZMod 2] E) (hi : Function.Injective e)
    (he : ∀ k v, ρ (κ k) (e v) = e (action k v))
    (hs : ∀ a v, v ∈ e.range → ρ a v ∈ e.range) :
    ∃ α : H →* MulAut Group,
      (∀ a v, ρ a (e v) = e (autAction (α a) v)) ∧
      (∀ k, α (κ k) = MulAut.conj k) := by
  let R : Subrepresentation ρ := {
    toSubmodule := e.range
    apply_mem_toSubmodule := hs }
  let t : Space ≃ₗ[ZMod 2] R.toSubmodule := LinearEquiv.ofInjective e hi
  let η : Representation (ZMod 2) H Space :=
    t.symm.conjRingEquiv.toMonoidHom.comp R.toRepresentation
  have ht (a : H) (v : Space) : e (η a v) = ρ a (e v) := by
    change (t (t.symm (R.toRepresentation a (t v))) : E) = _
    rw [t.apply_symm_apply]
    rfl
  let : κ.range.Normal := hn
  let j := MonoidHom.ofInjective hκ
  have hη (k : κ.range) : η k = action (j.symm k) := by
    apply LinearMap.ext
    intro v
    apply hi
    rw [ht]
    have hk : (k : H) = κ (j.symm k) :=
      (congrArg Subtype.val (j.apply_symm_apply k)).symm
    rw [hk,he]
  obtain ⟨α,hα,_⟩ := exists_automorphism_marking η κ.range j.symm.toMonoidHom
    j.symm.surjective hη
  refine ⟨α,?_,?_⟩
  · intro a v
    rw [←hα]
    exact (ht a v).symm
  · intro k
    apply autAction_injective
    rw [←hα,autAction_inner]
    apply LinearMap.ext
    intro v
    apply hi
    rw [ht,he]

namespace Paired
/-- Simultaneous component actions and their fixed supplement construct the
paired marking, preserving both original embeddings and component maps. -/
theorem exists_marking_of_component_embeddings
    (ρ : Representation (ZMod 2) H E)
    (κ₁ κ₂ : Group →* H) (hi₁ : Function.Injective κ₁) (hi₂ : Function.Injective κ₂)
    (hn₁ : κ₁.range.Normal) (hn₂ : κ₂.range.Normal)
    (e₁ e₂ : Space →ₗ[ZMod 2] E)
    (he₁ : Function.Injective e₁) (he₂ : Function.Injective e₂)
    (hs₁ : ∀ a v, v ∈ e₁.range → ρ a v ∈ e₁.range)
    (hs₂ : ∀ a v, v ∈ e₂.range → ρ a v ∈ e₂.range)
    (ha₁ : ∀ k v, ρ (κ₁ k) (e₁ v) = e₁ (action k v))
    (ha₂ : ∀ k v, ρ (κ₂ k) (e₂ v) = e₂ (action k v))
    (hc₁ : ∀ k v, ρ (κ₁ k) (e₂ v) = e₂ v)
    (hc₂ : ∀ k v, ρ (κ₂ k) (e₁ v) = e₁ v)
    (hd : Disjoint e₁.range e₂.range)
    (hspan : e₁.range ⊔ e₂.range ⊔ fixedSpace ρ ⊤ = ⊤) :
    ∃ m : Marking ρ, m.leftEmbedding = e₁ ∧ m.rightEmbedding = e₂ ∧
      (∀ k, m.left (κ₁ k) = MulAut.conj k) ∧ (∀ k, m.right (κ₁ k) = 1) ∧
      (∀ k, m.left (κ₂ k) = 1) ∧ (∀ k, m.right (κ₂ k) = MulAut.conj k) := by
  obtain ⟨α,hα,hακ⟩ := exists_embedded_automorphism_marking ρ κ₁ hi₁ hn₁ e₁ he₁ ha₁ hs₁
  obtain ⟨β,hβ,hβκ⟩ := exists_embedded_automorphism_marking ρ κ₂ hi₂ hn₂ e₂ he₂ ha₂ hs₂
  let m : Marking ρ := {
    left := α
    right := β
    leftEmbedding := e₁
    rightEmbedding := e₂
    left_injective := he₁
    right_injective := he₂
    disjoint := hd
    span := hspan
    left_intertwines := hα
    right_intertwines := hβ }
  refine ⟨m,rfl,rfl,hακ,?_,?_,hβκ⟩
  · intro k
    apply autAction_injective
    rw [map_one]
    apply LinearMap.ext
    intro v
    apply he₂
    exact (hβ (κ₁ k) v).symm.trans (hc₁ k v)
  · intro k
    apply autAction_injective
    rw [map_one]
    apply LinearMap.ext
    intro v
    apply he₁
    exact (hα (κ₂ k) v).symm.trans (hc₂ k v)
end Paired
end BinaryLinearThree.NaturalDual
