module
public import Theory.Representation.MathieuCodeRestriction.NormalizedShadowRows.M22CodeChiefProjection
import all Theory.Representation.MathieuCodeRestriction.NormalizedShadowRows.M22CodeCommutant
import all Theory.Representation.MathieuCodeRestriction.NormalizedShadowRows.M22CodeFiveAction

/-!
# Survival of the M22 moved seed on an active interval

Every nonzero invariant submodule of the marked quintet contains its moved
four-space. Thus an ambient normal subgroup meets the moved seed trivially
or contains it. If an interval has nontrivial movement confined to that seed,
its numerator contains the whole seed and its denominator misses the seed.
The result retains the original conjugation embedding and actor map.

Source: Aschbacher--Smith 8.2.9, printed p.721, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace MathieuCode.NormalizedShadowRows.M22CodeSection
set_option backward.isDefEq.respectTransparency false

private theorem marked_seed_normal_interval
    {A R X : Type*} [Group A] [Group R] [Group X] [IsElementaryAbelian 2 X]
    (σ : Representation (ZMod 2) R (Additive X))
    (r : R →* alternatingGroup (Fin 5)) (hrs : Function.Surjective r)
    (e : Additive X ≃ₗ[ZMod 2] Additive MathieuCode.M22Quintet.K)
    (he : ∀ x v, e (σ x v) = fiveAction (r x) (e v))
    (j : X →* A) (a : R →* A)
    (hjσ : ∀ r x, j ((σ r (Additive.ofMul x)).toMul) = a r * j x * (a r)⁻¹)
    (W : Subgroup A)
    (hW : (Coinvariants.ker σ).toAddSubgroup.toSubgroup'.map j = W)
    (K : Subgroup A) [K.Normal] : W ⊓ K = ⊥ ∨ W ≤ K := by
  let T := AddSubgroup.toZModSubmodule 2 (K.comap j).toAddSubgroup
  have hes (x : R) (v : Additive MathieuCode.M22Quintet.K) :
      e.symm (fiveAction (r x) v) = σ x (e.symm v) := by
    apply e.injective
    rw [e.apply_symm_apply,he,e.apply_symm_apply]
  let S : Subrepresentation fiveAction := {
    toSubmodule := T.comap e.symm.toLinearMap
    apply_mem_toSubmodule g v hv := by
      obtain ⟨x,rfl⟩ := hrs g
      change j (e.symm (fiveAction (r x) v)).toMul ∈ K
      rw [hes]
      have hσ : j ((σ x (e.symm v)).toMul) = a x * j (e.symm v).toMul * (a x)⁻¹ :=
        hjσ x (e.symm v).toMul
      rw [hσ]
      exact (inferInstance : K.Normal).conj_mem _ hv _ }
  rcases five_subrepresentation S with hz | hinner
  · left
    apply bot_unique
    rintro w ⟨hw,hk⟩
    obtain ⟨x,hx,rfl⟩ := hW.ge hw
    have hxS : e (Additive.ofMul x) ∈ S := by
      change j (e.symm (e (Additive.ofMul x))).toMul ∈ K
      rwa [e.symm_apply_apply]
    rw [hz] at hxS
    change e (Additive.ofMul x) = 0 at hxS
    have hx0 : Additive.ofMul x = 0 := e.injective (hxS.trans e.map_zero.symm)
    have hx1 : x = 1 := congrArg Additive.toMul hx0
    change j x = 1
    rw [hx1,map_one]
  · right
    intro w hw
    obtain ⟨x,hx,rfl⟩ := hW.ge hw
    obtain ⟨eS,heS⟩ := moved_equiv_of_marking σ r hrs e he
    have hm : e (Additive.ofMul x) ∈ fiveMoved.toSubmodule := by
      rw [←heS ⟨Additive.ofMul x,hx⟩]
      exact (eS ⟨Additive.ofMul x,hx⟩).property
    rw [fiveMoved_eq_inner] at hm
    have hh := hinner hm
    change j (e.symm (e (Additive.ofMul x))).toMul ∈ K at hh
    rwa [e.symm_apply_apply] at hh

/-- Nontrivial section movement confined to the marked M22 seed forces the
whole seed into the numerator and makes it disjoint from the denominator. -/
theorem moved_seed_survives_interval
    {A R X : Type*} [Group A] [Group R] [Group X] [IsElementaryAbelian 2 X]
    (σ : Representation (ZMod 2) R (Additive X))
    (r : R →* alternatingGroup (Fin 5)) (hrs : Function.Surjective r)
    (e : Additive X ≃ₗ[ZMod 2] Additive MathieuCode.M22Quintet.K)
    (he : ∀ x v, e (σ x v) = fiveAction (r x) (e v))
    (j : X →* A) (a : R →* A)
    (hjσ : ∀ r x, j ((σ r (Additive.ofMul x)).toMul) = a r * j x * (a r)⁻¹)
    (W : Subgroup A)
    (hW : (Coinvariants.ker σ).toAddSubgroup.toSubgroup'.map j = W)
    (K C V : Subgroup A) [K.Normal] [C.Normal]
    (hmove : ⁅C,V⁆ ≤ W) (hne : ¬ ⁅C,V⁆ ≤ K) :
    W ≤ C ∧ W ⊓ K = ⊥ := by
  have hWC := marked_seed_normal_interval σ r hrs e he j a hjσ W hW C
  have hWK := marked_seed_normal_interval σ r hrs e he j a hjσ W hW K
  refine ⟨hWC.resolve_left ?_,hWK.resolve_right ?_⟩
  · intro hb
    apply hne
    exact (le_inf hmove (commutator_le_left _ _)).trans (hb.le.trans bot_le)
  · intro h
    exact hne (hmove.trans h)


end MathieuCode.NormalizedShadowRows.M22CodeSection
