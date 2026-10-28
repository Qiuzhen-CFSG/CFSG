module

public import Theory.Representation.HexacodeAction.SixDimensionalRecognition.Normalizer
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.PGroupCore

/-!
# Extending prescribed even hexacode coordinates

A faithful action of a normal component on the hexacode extends to an
embedding of its two-reduced overgroup in the full hexacode automorphism
group. The action kernel meets the component trivially and hence embeds
in the two-group quotient. It vanishes in the trivial two-core. In the
prescribed coordinates the full actor normalizes the even image, whose
binary normalizer is the full hexacode image.

This retains both the given component marking and the linear coordinates.
Source: the hexacode normalizer calculation in Aschbacher–Smith K.1.3,
applied to the covered-six action in 13.6.22, printed pp.453 and 932.
-/

public section
open Subgroup Theory.GroupTheory Atlas.Codes
namespace Representation.Hexacode
open SixDimensional
variable {D W : Type*} [Group D] [Finite D]
  [AddCommGroup W] [Module (ZMod 2) W]
  (ρ : Representation (ZMod 2) D W) (C : Subgroup D) [C.Normal]

omit [Finite D] in
private theorem faithful_of_component
    (hquot : IsPGroup 2 (D ⧸ C)) (hcore : pCore 2 D = ⊥)
    (hC : Function.Injective (ρ.comp C.subtype)) : Function.Injective ρ := by
  let q := (QuotientGroup.mk' C).comp ρ.ker.subtype
  have hq : Function.Injective q := by
    apply q.ker_eq_bot_iff.mp
    apply bot_unique
    intro x hx
    have hxC : (x : D) ∈ C := (QuotientGroup.eq_one_iff _).mp hx
    have he : (ρ.comp C.subtype) ⟨x, hxC⟩ = (ρ.comp C.subtype) 1 := by
      rw [map_one]
      exact x.property
    exact mem_bot.mpr (Subtype.ext (show (x : D) = 1 from congrArg (fun y : C => (y : D)) (hC he)))
  have hp : IsPGroup 2 ρ.ker := hquot.of_injective q hq
  apply ρ.ker_eq_bot_iff.mp
  exact bot_unique ((show ρ.ker ≤ pCore 2 D from le_sSup ⟨inferInstance, hp⟩).trans_eq hcore)

omit [Finite D] in
/-- The complete overgroup action in the prescribed hexacode coordinates.
Its component equation is on each original element, not merely its range. -/
theorem exists_full_embedding
    (hquot : IsPGroup 2 (D ⧸ C)) (hcore : pCore 2 D = ⊥)
    (c : C ≃* HexEvenAutomorphisms) (e : W ≃ₗ[ZMod 2] hexacode)
    (he : ∀ (g : C) (w : W), e (ρ g w) = evenAction (c g) (e w)) :
    ∃ f : D →* HexAutomorphisms, Function.Injective f ∧
      (∀ g : C, f g = (c g).val) ∧
      (∀ (g : D) (w : W), e (ρ g w) = action (f g) (e w)) := by
  have hC : Function.Injective (ρ.comp C.subtype) := by
    intro a b hab
    apply c.injective
    apply Subtype.ext
    apply action_injective
    apply LinearMap.ext
    intro w
    obtain ⟨u, rfl⟩ := e.surjective w
    change evenAction (c a) (e u) = evenAction (c b) (e u)
    rw [← he, ← he]
    exact congrArg e (LinearMap.congr_fun hab u)
  have hρ := faithful_of_component ρ C hquot hcore hC
  let a := coordinateAction ρ e
  have ha (g : C) : a g = hexAction (c g).val := by
    apply LinearEquiv.ext
    intro w
    change e (ρ g (e.symm w)) = _
    rw [he, e.apply_symm_apply]
    rfl
  have himage : C.map a = evenBinaryImage := by
    apply le_antisymm
    · rintro _ ⟨g, hg, rfl⟩
      exact ⟨c ⟨g,hg⟩, (ha ⟨g,hg⟩).symm⟩
    · rintro _ ⟨g, rfl⟩
      obtain ⟨b, rfl⟩ := c.surjective g
      exact ⟨b, b.property, ha b⟩
  have hmem (g : D) : a g ∈ hexAction.range := by
    rw [← normalizer_evenBinaryImage, ← himage]
    exact le_normalizer_map a ⟨g, by rw [C.normalizer_eq_top]; trivial, rfl⟩
  let j := a.codRestrict hexAction.range hmem
  let f := (MonoidHom.ofInjective hexAction_injective).symm.toMonoidHom.comp j
  have hf (g : D) : hexAction (f g) = a g :=
    MonoidHom.apply_ofInjective_symm hexAction_injective (j g)
  refine ⟨f, ?_, ?_, ?_⟩
  · intro g h hgh
    apply coordinateAction_injective ρ e hρ
    rw [← hf, ← hf, hgh]
  · intro g
    apply hexAction_injective
    rw [hf, ha]
  · intro g w
    have h := LinearEquiv.congr_fun (hf g) (e w)
    change action (f g) (e w) = e (ρ g (e.symm (e w))) at h
    simpa only [e.symm_apply_apply] using h.symm

end Representation.Hexacode
