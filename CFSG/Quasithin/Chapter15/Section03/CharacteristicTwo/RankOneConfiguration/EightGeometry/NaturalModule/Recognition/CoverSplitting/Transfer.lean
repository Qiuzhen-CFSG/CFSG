module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.Recognition.Models

/-!
# Extending component coordinates to the marked symmetric group

For a normal subgroup, compare the transported action of each ambient element
with its proposed target action. Their quotient centralizes the component.
A trivial linear centralizer therefore forces equality of the two actions.
We also transport component normality and the centralizer condition through
the supplied marking onto A₈. No extension of coordinates is assumed.

`TrivialComponentCentralizer` records the precise concrete model calculation
still required for each of the six- and seven-dimensional modules. This file
proves the transport implication; it does not assert those calculations.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the module
identification in 15.3.32(1), printed pp.1132–1133.
-/

@[expose] public section

open Equiv Representation

namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.Recognition.CoverSplitting

variable {k K V W : Type*} [Field k] [Group K]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

private def actionEquiv (ρ : Representation k K V) (g : K) : V ≃ₗ[k] V :=
  LinearEquiv.ofLinearMap (f := ρ g) (g := ρ g⁻¹)
    (by rw [← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel, map_one]; rfl)
    (by rw [← Module.End.mul_eq_comp, ← map_mul, inv_mul_cancel, map_one]; rfl)

/-- A component-equivariant coordinate map extends uniquely when the component
has trivial centralizer in the target general linear group. -/
theorem extend_equivariance (ρ : Representation k K V) (τ : Representation k K W)
    (L : Subgroup K) [L.Normal]
    (rigid : ∀ a : W ≃ₗ[k] W,
      (∀ (l : L) w, a (τ l w) = τ l (a w)) → a = LinearEquiv.refl k W)
    (f : V ≃ₗ[k] W) (hf : ∀ (l : L) v, f (ρ l v) = τ l (f v)) :
    ∀ g v, f (ρ g v) = τ g (f v) := by
  have hinv (l : L) (w : W) : f.symm (τ l w) = ρ l (f.symm w) := by
    apply f.injective
    rw [f.apply_symm_apply, hf, f.apply_symm_apply]
  intro g v
  let a := (((f.symm.trans (actionEquiv ρ g)).trans f).trans (actionEquiv τ g⁻¹))
  have ha : a = LinearEquiv.refl k W := by
    apply rigid
    intro l w
    let l' : L := ⟨g * l * g⁻¹, (show L.Normal from inferInstance).conj_mem (l : K) l.property g⟩
    change τ g⁻¹ (f (ρ g (f.symm (τ l w)))) = τ l (τ g⁻¹ (f (ρ g (f.symm w))))
    rw [hinv]
    have hm : ρ g (ρ l (f.symm w)) = ρ l' (ρ g (f.symm w)) := by
      simp only [← Module.End.mul_apply, ← map_mul]
      congr 2
      simp [l', mul_assoc]
    rw [hm, hf]
    simp only [← Module.End.mul_apply, ← map_mul]
    congr 2
    simp [l', mul_assoc]
  have he := congrArg (fun b : W ≃ₗ[k] W => τ g (b (f v))) ha
  change τ g (τ g⁻¹ (f (ρ g (f.symm (f v))))) = τ g (f v) at he
  simpa only [f.symm_apply_apply, ← Module.End.mul_apply, ← map_mul,
    mul_inv_cancel, map_one, Module.End.one_apply] using he


variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

/-- The exact linear-centralizer assertion needed for marked extension. -/
def TrivialComponentCentralizer (τ : Representation (ZMod 2) (Perm (Fin 8)) W) : Prop :=
  ∀ a : W ≃ₗ[ZMod 2] W,
    (∀ (l : alternatingGroup (Fin 8)) w, a (τ l w) = τ l (a w)) →
    a = LinearEquiv.refl (ZMod 2) W

variable {K V : Type*} [Group K] [AddCommGroup V] [Module (ZMod 2) V]

theorem marked_component_normal (e : K ≃* Perm (Fin 8)) (L : Subgroup K)
    (hL : L.map e.toMonoidHom = alternatingGroup (Fin 8)) : L.Normal := by
  have hmem (x : K) : e x ∈ alternatingGroup (Fin 8) ↔ x ∈ L := by
    rw [← hL]
    exact Subgroup.mem_map_iff_mem e.injective
  refine ⟨fun l hl g => (hmem _).mp ?_⟩
  rw [map_mul, map_mul, map_inv]
  exact (show (alternatingGroup (Fin 8)).Normal from inferInstance).conj_mem
    (e l) ((hmem l).mpr hl) (e g)

theorem extend_marked_equivariance (ρ : Representation (ZMod 2) K V)
    (τ : Representation (ZMod 2) (Perm (Fin 8)) W)
    (e : K ≃* Perm (Fin 8)) (L : Subgroup K)
    (hL : L.map e.toMonoidHom = alternatingGroup (Fin 8))
    (rigid : TrivialComponentCentralizer τ)
    (f : V ≃ₗ[ZMod 2] W)
    (hf : ∀ (l : L) v, f (ρ l v) = τ (e l) (f v)) :
    ∀ g v, f (ρ g v) = τ (e g) (f v) := by
  let : L.Normal := marked_component_normal e L hL
  apply extend_equivariance ρ (τ.comp e.toMonoidHom) L _ f hf
  intro a ha
  apply rigid a
  intro l w
  have hl : l.val ∈ L.map e.toMonoidHom := hL.symm ▸ l.property
  obtain ⟨x, hx, hxl⟩ := hl
  simpa only [MonoidHom.comp_apply, ← hxl] using ha ⟨x, hx⟩ w

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.Recognition.CoverSplitting

end
