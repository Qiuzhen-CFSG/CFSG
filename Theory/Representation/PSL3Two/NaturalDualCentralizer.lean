module

public import Theory.Representation.PSL3Two.NaturalCoordinates
public import Theory.Representation.PSL3Two.IrreducibleCatalogue.Irreducibility
public import Theory.Representation.SL3DoubledNaturalOffenders.Centralizer

/-!
# The centralizer of the binary natural and dual pair

The two irreducible three-dimensional constituents are inequivalent. Schur's
lemma therefore kills both off-diagonal blocks of an intertwiner. Elementary
transvections make each diagonal block scalar; over the binary field an
invertible such block is the identity. This is the actor-faithfulness step
of Aschbacher–Smith 15.3.58, printed p.1149.
-/

@[expose] public section

open Representation
namespace BinaryLinearThree.NaturalDual

abbrev Space := Vector × Module.Dual (ZMod 2) Vector
noncomputable abbrev action : Representation (ZMod 2) Group Space := W.prod W.dual

theorem natural_scalar (f : W.IntertwiningMap W) :
    ∃ c : ZMod 2, ∀ v, f v = c • v :=
  Representation.SL3DoubledNaturalOffenders.natural_centralizer_scalar
    f.toLinearMap.toAddMonoidHom (fun g v =>
      LinearMap.congr_fun (f.isIntertwining' g) v)

theorem dual_scalar (f : W.dual.IntertwiningMap W.dual) :
    ∃ c : ZMod 2, ∀ v, f v = c • v := by
  let E := AutomorphismAction.graphNaturalDual
  let F : W.IntertwiningMap W := {
    toLinearMap := E.symm.toLinearMap.comp (f.toLinearMap.comp E.toLinearMap)
    isIntertwining' := by
      intro g
      apply LinearMap.ext
      intro v
      change E.symm (f (E (W g v))) = W g (E.symm (f (E v)))
      apply E.toEquiv.injective
      change E (E.symm (f (E (W g v)))) = E (W g (E.symm (f (E v))))
      rw [E.apply_symm_apply]
      have he (x : Vector) : E (W g x) = W.dual (AutomorphismAction.graph g) (E x) := by
        simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
          AutomorphismAction.graph_graph, LinearMap.comp_apply, Equiv.coe_toLinearMap] using
          LinearMap.congr_fun (E.isIntertwining' (AutomorphismAction.graph g)) x
      rw [he, he, E.apply_symm_apply]
      exact LinearMap.congr_fun (f.isIntertwining' (AutomorphismAction.graph g)) (E v) }
  obtain ⟨c, hc⟩ := natural_scalar F
  refine ⟨c, fun v => ?_⟩
  have h := congrArg E (hc (E.symm v))
  change E (E.symm (f (E (E.symm v)))) = E (c • E.symm v) at h
  simpa only [E.apply_symm_apply, map_smul] using h

theorem natural_dual_zero (f : W.IntertwiningMap W.dual) : f = 0 := by
  let := IrreducibleCatalogue.natural_irreducible
  let := IrreducibleCatalogue.dual_irreducible
  rcases IsIrreducible.bijective_or_eq_zero f with hi | hz
  · exact False.elim (AutomorphismAction.natural_not_equiv_dual ⟨f.ofBijective hi⟩)
  · exact hz

theorem dual_natural_zero (f : W.dual.IntertwiningMap W) : f = 0 := by
  let := IrreducibleCatalogue.natural_irreducible
  let := IrreducibleCatalogue.dual_irreducible
  rcases IsIrreducible.bijective_or_eq_zero f with hi | hz
  · exact False.elim (AutomorphismAction.natural_not_equiv_dual ⟨(f.ofBijective hi).symm⟩)
  · exact hz

/-- The full commutant consists of two independent binary scalars. -/
theorem block_scalars (f : Space →ₗ[ZMod 2] Space)
    (hf : ∀ g x, f (action g x) = action g (f x)) :
    ∃ a b : ZMod 2, ∀ x, f x = (a • x.1, b • x.2) := by
  let f₁₁ : W.IntertwiningMap W := {
    toLinearMap := (LinearMap.fst _ _ _).comp
      (f.comp (LinearMap.inl _ _ _))
    isIntertwining' := by
      intro g
      apply LinearMap.ext
      intro v
      simpa using congrArg Prod.fst (hf g (v, 0)) }
  let f₁₂ : W.dual.IntertwiningMap W := {
    toLinearMap := (LinearMap.fst _ _ _).comp
      (f.comp (LinearMap.inr _ _ _))
    isIntertwining' := by
      intro g
      apply LinearMap.ext
      intro v
      simpa using congrArg Prod.fst (hf g (0, v)) }
  let f₂₁ : W.IntertwiningMap W.dual := {
    toLinearMap := (LinearMap.snd _ _ _).comp
      (f.comp (LinearMap.inl _ _ _))
    isIntertwining' := by
      intro g
      apply LinearMap.ext
      intro v
      simpa using congrArg Prod.snd (hf g (v, 0)) }
  let f₂₂ : W.dual.IntertwiningMap W.dual := {
    toLinearMap := (LinearMap.snd _ _ _).comp
      (f.comp (LinearMap.inr _ _ _))
    isIntertwining' := by
      intro g
      apply LinearMap.ext
      intro v
      simpa using congrArg Prod.snd (hf g (0, v)) }
  obtain ⟨a, ha⟩ := natural_scalar f₁₁
  obtain ⟨b, hb⟩ := dual_scalar f₂₂
  have h₁₂ := dual_natural_zero f₁₂
  have h₂₁ := natural_dual_zero f₂₁
  refine ⟨a, b, fun x => ?_⟩
  have hsum : f x = f (x.1, 0) + f (0, x.2) := by
    rw [← map_add]
    simp
  rw [hsum]
  apply Prod.ext
  · change f₁₁ x.1 + f₁₂ x.2 = a • x.1
    rw [ha, h₁₂]
    simp
  · change f₂₁ x.1 + f₂₂ x.2 = b • x.2
    rw [hb, h₂₁]
    simp

/-- An invertible operator commuting with the literal natural–dual action
is the identity. No classification of representations is used. -/
theorem centralizer_eq_one (f : Space ≃ₗ[ZMod 2] Space)
    (hf : ∀ g x, f (action g x) = action g (f x)) : f = LinearEquiv.refl _ _ := by
  obtain ⟨a, b, hab⟩ := block_scalars f.toLinearMap hf
  change ∀ x : Space, f x = (a • x.1, b • x.2) at hab
  have ha : a ≠ 0 := by
    intro ha
    have he : f (fun _ => 1, 0) = f 0 := by
      rw [hab, hab, ha]
      simp
    have h := congrArg (fun x : Space => x.1 0) (f.injective he)
    exact one_ne_zero h
  have hb : b ≠ 0 := by
    intro hb
    let v : Module.Dual (ZMod 2) Vector := LinearMap.proj 0
    have he : f (0, v) = f 0 := by
      rw [hab, hab, hb]
      simp
    have h := congrArg (fun x : Space => x.2 (fun _ => 1)) (f.injective he)
    exact one_ne_zero h
  have hbit : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  have ha1 := (hbit a).resolve_left ha
  have hb1 := (hbit b).resolve_left hb
  ext x : 1
  rw [hab, ha1, hb1]
  simp

end BinaryLinearThree.NaturalDual
