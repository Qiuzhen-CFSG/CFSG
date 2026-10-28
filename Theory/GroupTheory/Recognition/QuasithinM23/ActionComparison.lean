module
public import Theory.LinearAlgebra.BinaryFourAlternatingEight
public import Theory.Alternating.IndexEightSubgroups

/-!
# Comparing the actual binary four-dimensional A₇ actions

Choose linear coordinates on the two spaces. The faithful images have index
eight in GL₄(2), identified with A₈ by the proved exterior-square equivalence.
Conjugacy of its index-eight subgroups supplies a linear change of coordinates.
The two faithful image maps then construct the accompanying A₇ automorphism,
with a pointwise intertwining identity for every vector and every actor.

This is the action-comparison step in Aschbacher–Smith 5.2.17, printed p.655
(`refs/quasithin.pdf`). It uses actual linear and group equivalences, rather
than an abstract family label. The underlying GL₄(2) comparison retains its
ATLAS attribution and license in `Theory.LinearAlgebra.BinaryFourAlternatingEight`.
-/

public noncomputable section
open Subgroup
namespace Theory.GroupTheory.QuasithinM23
local notation "A7" => alternatingGroup (Fin 7)

private theorem image_index_eight
    (f : A7 →* alternatingGroup (Fin 8)) (hf : Function.Injective f) : f.range.index = 8 := by
  have hc : Nat.card f.range = 2520 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hf).toEquiv,nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hh := f.range.card_mul_index
  rw [hc,nat_card_alternatingGroup] at hh
  norm_num [Nat.factorial] at hh
  omega

/-- Faithful binary four-dimensional A₇ actions agree after an actual linear
change of coordinates and one automorphism of the original A₇. -/
theorem exceptional_action_equiv
    {V W : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (ρ : A7 →* (V ≃ₗ[ZMod 2] V)) (τ : A7 →* (W ≃ₗ[ZMod 2] W))
    (hρ : Function.Injective ρ) (hτ : Function.Injective τ)
    (hV : Module.finrank (ZMod 2) V = 4) (hW : Module.finrank (ZMod 2) W = 4) :
    ∃ (e : V ≃ₗ[ZMod 2] W) (a : MulAut A7),
      ∀ (g : A7) (v : V), e (ρ g v) = τ (a g) (e v) := by
  let b : V ≃ₗ[ZMod 2] W := LinearEquiv.ofFinrankEq _ _ (hV.trans hW.symm)
  let f : A7 →* (W ≃ₗ[ZMod 2] W) := {
    toFun := fun g => b.symm.trans ((ρ g).trans b)
    map_one' := by ext w; simp
    map_mul' := by intro g h; ext w; simp }
  have hf : Function.Injective f := by
    intro g h he
    apply hρ
    ext v
    apply b.injective
    have hh := congrArg (fun t : W ≃ₗ[ZMod 2] W => t (b v)) he
    simpa only [f,MonoidHom.coe_mk,OneHom.coe_mk,LinearEquiv.trans_apply,b.symm_apply_apply] using hh
  let E := BinaryFourAlternatingEight.linearEquivAlternatingEight hW
  let f8 := E.toMonoidHom.comp f
  let t8 := E.toMonoidHom.comp τ
  obtain ⟨c8,hc8⟩ := GroupTheory.AlternatingIndexEight.index_eight_conjugate
    f8.range t8.range (image_index_eight f8 (E.injective.comp hf))
      (image_index_eight t8 (E.injective.comp hτ))
  let c := E.symm c8
  have he : E.toMonoidHom.comp (MulAut.conj c).toMonoidHom =
      (MulAut.conj c8).toMonoidHom.comp E.toMonoidHom := by
    apply MonoidHom.ext
    intro x
    change E (c*x*c⁻¹) = c8*E x*c8⁻¹
    simp only [map_mul,map_inv,c,E.apply_symm_apply]
  have hc : f.range.map (MulAut.conj c).toMonoidHom = τ.range := by
    apply Subgroup.map_injective (f := E.toMonoidHom) E.injective
    rw [map_map,he,←map_map]
    simpa only [f8,t8,MonoidHom.range_comp] using hc8
  let a : MulAut A7 := (MonoidHom.ofInjective hf).trans
    ((f.range.equivMapOfInjective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective).trans
      ((MulEquiv.subgroupCongr hc).trans (MonoidHom.ofInjective hτ).symm))
  have ha (g : A7) : τ (a g) = c*f g*c⁻¹ := by
    exact congrArg Subtype.val ((MonoidHom.ofInjective hτ).apply_symm_apply _)
  refine ⟨b.trans c,a,?_⟩
  intro g v
  rw [ha]
  change c (b (ρ g v)) = (c*f g*c⁻¹) (c (b v))
  change c (b (ρ g v)) = c (f g (c.symm (c (b v))))
  rw [c.symm_apply_apply]
  change c (b (ρ g v)) = c (b (ρ g (b.symm (b v))))
  rw [b.symm_apply_apply]

end Theory.GroupTheory.QuasithinM23
