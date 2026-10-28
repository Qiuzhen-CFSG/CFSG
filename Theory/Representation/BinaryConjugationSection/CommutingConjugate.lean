module
public import Theory.Representation.BinaryConjugationSection.NormalizingActors

/-!
# Commuting conjugate actions on faithfully marked elementary subgroups

When a conjugating element preserves the numerator of a zero-kernel binary
section, its literal conjugation gives a linear equivalence of the model.
Commutation of the two original component actions becomes commutation with
the conjugate representation under that same equivalence.

Source application: Aschbacher--Smith 10.1.1(6), printed p.741.
-/
public noncomputable section
open Subgroup
open scoped commutatorElement IsMulCommutative
namespace Representation.BinaryConjugationSection
variable {G J V : Type*} [Group G] [Group J] [AddCommGroup V] [Module (ZMod 2) V]
  {L E : Subgroup G} [IsElementaryAbelian 2 E]

/-- Transport the two literal commuting conjugation actions through a zero-kernel marking. -/
theorem exists_commuting_conjugate
    (σ : Representation (ZMod 2) J V) (q : L →* J) (hq : Function.Surjective q)
    (d : BinaryConjugationSection L E ⊥ (σ.comp q))
    {t : G} (ht : t ∈ normalizer (E : Set G))
    (hc : ⁅L.map (MulAut.conj t).toMonoidHom,L⁆ ≤ centralizer (E : Set G)) :
    ∃ τ : V ≃ₗ[ZMod 2] V, ∀ a b v,
      τ (σ a (τ.symm (σ b v))) = σ b (τ (σ a (τ.symm v))) := by
  have hi : Function.Injective d.coordinates := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    rw [d.kernel_eq,bot_subgroupOf]
  let φ : Additive E ≃ₗ[ZMod 2] V := LinearEquiv.ofBijective
    (d.coordinates.toAdditiveLeft.toZModLinearMap 2) ⟨hi,d.onto⟩
  let β : L →* MulAut E := E.normalizerMonoidHom.comp (inclusion d.normalized)
  let tN : normalizer (E : Set G) := ⟨t,ht⟩
  let γ : MulAut E := E.normalizerMonoidHom tN
  let γV : Additive E ≃ₗ[ZMod 2] Additive E := LinearEquiv.ofBijective
    (γ.toMonoidHom.toAdditive.toZModLinearMap 2) γ.bijective
  let τ : V ≃ₗ[ZMod 2] V := (φ.symm.trans γV).trans φ
  have hφ (l : L) (w : E) : σ (q l) (φ (Additive.ofMul w)) =
      φ (Additive.ofMul (β l w)) := (d.equivariant l w).symm
  have hτ (w : E) : τ (φ (Additive.ofMul w)) = φ (Additive.ofMul (γ w)) := by
    change φ (γV (φ.symm (φ (Additive.ofMul w)))) = _
    rw [φ.symm_apply_apply]
    rfl
  have hτi (w : E) : τ.symm (φ (Additive.ofMul w)) =
      φ (Additive.ofMul (γ⁻¹ w)) := by
    apply τ.injective
    rw [τ.apply_symm_apply,hτ]
    change φ (Additive.ofMul w) = φ (Additive.ofMul ((γ * γ⁻¹) w))
    rw [mul_inv_cancel]
    rfl
  have hco (l k : L) : Commute (γ * β l * γ⁻¹) (β k) := by
    apply commutatorElement_eq_one_iff_mul_comm.mp
    change ⁅E.normalizerMonoidHom tN *
      E.normalizerMonoidHom (inclusion d.normalized l) * (E.normalizerMonoidHom tN)⁻¹,
      E.normalizerMonoidHom (inclusion d.normalized k)⁆ = 1
    rw [←map_inv,←map_mul,←map_mul,←map_commutatorElement]
    change ⁅tN * inclusion d.normalized l * tN⁻¹, inclusion d.normalized k⁆ ∈
      E.normalizerMonoidHom.ker
    rw [normalizerMonoidHom_ker]
    exact hc (commutator_mem_commutator
      (mem_map_of_mem (MulAut.conj t).toMonoidHom l.property) k.property)
  refine ⟨τ,?_⟩
  intro a b v
  obtain ⟨l,rfl⟩ := hq a
  obtain ⟨k,rfl⟩ := hq b
  obtain ⟨w,rfl⟩ := φ.surjective v
  change τ (σ (q l) (τ.symm (σ (q k) (φ (Additive.ofMul w.toMul))))) =
    σ (q k) (τ (σ (q l) (τ.symm (φ (Additive.ofMul w.toMul)))))
  rw [hφ,hτi,hφ,hτ,hτi,hφ,hτ,hφ]
  exact congrArg (fun w : E => φ (Additive.ofMul w)) (DFunLike.congr_fun (hco l k).eq w.toMul)
end Representation.BinaryConjugationSection
