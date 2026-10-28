module
public import Theory.Representation.MathieuCodeRestriction.NormalizedShadowRows.M22CodeCommutant
import all Theory.Representation.MathieuCodeRestriction.NormalizedShadowRows.M22CodeCommutant
import all Theory.Representation.MathieuCodeRestriction.NormalizedShadowRows.M22CodeFiveAction

/-!
# The irreducible moved part of the native M22 five-space

The internal five-space proofs identify its displacement span with the
irreducible inner four-space. This companion exposes that precise boundary
and the resulting injectivity of a nonzero equivariant projection. The
private imports deliberately reuse the native five-space implementation;
no private declaration occurs in the exported statements.

The projection is defined only on the moved four-space. Extending it to the
whole indecomposable five-space would impose an unjustified source condition.
Source: Aschbacher--Smith H.14.3(2), H.16.3(3), and 8.2.9, pp.397,403,721.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Sporadic.Mathieu MathieuCode MathieuCode.M22Quintet MathieuCode.M22Quintet.CocodeTransfer
open scoped IsMulCommutative
namespace MathieuCode.NormalizedShadowRows.M22CodeSection
open M22ChapterH.Quintet

/-- The literal displacement space, with its restricted A5 action. -/
@[expose] def fiveMoved : Subrepresentation fiveAction where
  toSubmodule := Coinvariants.ker fiveAction
  apply_mem_toSubmodule g v hv := by
    simpa only [sub_add_cancel] using
      (Coinvariants.ker fiveAction).add_mem (Coinvariants.sub_mem_ker g v) hv

/-- The moved four-space is the actual inner translation space. -/
theorem fiveMoved_eq_inner : fiveMoved.toSubmodule = innerInclusion.range := by
  apply Submodule.eq_of_le_of_finrank_eq (show fiveMoved.toSubmodule ≤ innerInclusion.range from moved_le_inner)
  exact fiveAction_moved_dim.trans fiveInner_dim.symm

/-- Only the moved four-space, rather than the whole quintet, is irreducible. -/
instance fiveMoved_irreducible : IsIrreducible fiveMoved.toRepresentation := by
  have he : fiveMoved = fiveInner := Subrepresentation.toSubmodule_injective fiveMoved_eq_inner
  rw [he]
  exact fiveInner_irreducible

/-- Every nonzero equivariant projection on the moved four-space is injective
and has image of binary dimension four, also under a surjective actor marking. -/
theorem fiveMoved_projection {R W : Type*} [Group R] [AddCommGroup W]
    [Module (ZMod 2) W] (r : R →* alternatingGroup (Fin 5))
    (hr : Function.Surjective r) (τ : Representation (ZMod 2) R W)
    (c : fiveMoved.toSubmodule →ₗ[ZMod 2] W)
    (hc : ∀ x v, c (fiveMoved.toRepresentation (r x) v) = τ x (c v))
    (hne : c ≠ 0) :
    Function.Injective c ∧ Module.finrank (ZMod 2) (LinearMap.range c) = 4 := by
  let : IsIrreducible (fiveMoved.toRepresentation.comp r) :=
    (irreducible_comp_surjective_iff r hr fiveMoved.toRepresentation).mpr inferInstance
  let F : IntertwiningMap (fiveMoved.toRepresentation.comp r) τ :=
    ⟨c,fun x => LinearMap.ext (hc x)⟩
  have hF : F ≠ 0 := fun hh => hne (congrArg IntertwiningMap.toLinearMap hh)
  have hinj : Function.Injective c := (IsIrreducible.injective_or_eq_zero F).resolve_right hF
  exact ⟨hinj,(LinearMap.finrank_range_of_inj hinj).trans fiveAction_moved_dim⟩

/-- Marked coordinates restrict to the actual moved four-space, with the
original actor map in the intertwining equation. -/
theorem moved_equiv_of_marking {R X : Type*} [Group R] [AddCommGroup X]
    [Module (ZMod 2) X]
    (σ : Representation (ZMod 2) R X) (r : R →* alternatingGroup (Fin 5))
    (hr : Function.Surjective r) (e : X ≃ₗ[ZMod 2] Additive M22Quintet.K)
    (he : ∀ x v, e (σ x v) = fiveAction (r x) (e v)) :
    ∃ eS : Coinvariants.ker σ ≃ₗ[ZMod 2] fiveMoved.toSubmodule,
      ∀ v, (eS v : Additive M22Quintet.K) = e v := by
  have hmap : (Coinvariants.ker σ).map e.toLinearMap = Coinvariants.ker fiveAction := by
    apply le_antisymm
    · apply Submodule.map_le_iff_le_comap.mpr
      apply Submodule.span_le.mpr
      rintro _ ⟨⟨x,v⟩,rfl⟩
      change e (σ x v-v) ∈ Coinvariants.ker fiveAction
      rw [map_sub,he]
      exact Coinvariants.sub_mem_ker _ _
    · apply Submodule.span_le.mpr
      rintro _ ⟨⟨x,v⟩,rfl⟩
      obtain ⟨x,rfl⟩ := hr x
      obtain ⟨v,rfl⟩ := e.surjective v
      exact ⟨σ x v-v,Coinvariants.sub_mem_ker _ _,by
        simp only [LinearEquiv.coe_coe,map_sub,he]⟩
  exact ⟨(e.submoduleMap (Coinvariants.ker σ)).trans (LinearEquiv.ofEq _ _ hmap),
    fun _ => rfl⟩

/-- Nonzero equivariant projections of a marked source four-space are
injective. No map on the entire five-space is required. -/
theorem moved_projection_of_marking {R X W : Type*} [Group R] [AddCommGroup X]
    [Module (ZMod 2) X] [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) R X) (r : R →* alternatingGroup (Fin 5))
    (hr : Function.Surjective r) (e : X ≃ₗ[ZMod 2] Additive M22Quintet.K)
    (he : ∀ x v, e (σ x v) = fiveAction (r x) (e v))
    (τ : Representation (ZMod 2) R W)
    (c : Coinvariants.ker σ →ₗ[ZMod 2] W)
    (hc : ∀ x (v w : Coinvariants.ker σ), (w : X) = σ x v → c w = τ x (c v))
    (hne : c ≠ 0) :
    Function.Injective c ∧ Module.finrank (ZMod 2) (LinearMap.range c) = 4 := by
  obtain ⟨eS,heS⟩ := moved_equiv_of_marking σ r hr e he
  have hes (v : fiveMoved.toSubmodule) : e (eS.symm v) = (v : Additive M22Quintet.K) := by
    rw [←heS,eS.apply_symm_apply]
  let p := c.comp eS.symm.toLinearMap
  have hp (x : R) (v : fiveMoved.toSubmodule) :
      p (fiveMoved.toRepresentation (r x) v) = τ x (p v) := by
    apply hc x
    apply e.injective
    change e (eS.symm (fiveMoved.toRepresentation (r x) v)) = e (σ x (eS.symm v))
    rw [he,hes,hes]
    rfl
  have hpn : p ≠ 0 := by
    intro hz
    apply hne
    ext v
    have hh := LinearMap.congr_fun hz (eS v)
    change c (eS.symm (eS v)) = 0 at hh
    rwa [eS.symm_apply_apply] at hh
  obtain ⟨hpi,hpd⟩ := fiveMoved_projection r hr τ p hp hpn
  have hci : Function.Injective c := by
    intro v w hvw
    apply eS.injective
    apply hpi
    change c (eS.symm (eS v)) = c (eS.symm (eS w))
    simpa only [eS.symm_apply_apply] using hvw
  have hrange : LinearMap.range p = LinearMap.range c := by
    rw [LinearMap.range_comp,LinearEquiv.range,Submodule.map_top]
  exact ⟨hci,hrange ▸ hpd⟩

end MathieuCode.NormalizedShadowRows.M22CodeSection
