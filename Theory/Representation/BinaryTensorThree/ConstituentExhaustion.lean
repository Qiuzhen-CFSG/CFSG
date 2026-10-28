module
public import Theory.Representation.BinaryTensorThree.ConstituentStability

/-!
# Exhaustion by a natural binary tensor constituent

In an irreducible ambient module, a faithfully marked binary natural tensor
constituent is the whole space whenever an elementary actor acts faithfully
on the normal square and has fixed codimension at most twice its rank.
The constituent-stability theorem gives invariance under the whole ambient
group; irreducibility then makes the original embedding surjective.

Source: Aschbacher--Smith D.3.9, printed pp.199--200. The Chapter10
QuietSeedTensor consumer uses the original full action and its actual seed.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace BinaryTensorThree
variable {H K V W : Type*} [_root_.Group H] [Finite H] [_root_.Group K]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  [AddCommGroup W] [Module (ZMod 2) W] [Nontrivial W]

/-- A marked natural tensor embedded in an irreducible ambient module
exhausts it under the original faithful elementary-actor budget. -/
theorem tensor_intertwiner_surjective
    (ρ : Representation (ZMod 2) H V) (hirr : ρ.IsIrreducible)
    (i : K →* H) (hi : Function.Injective i) [i.range.Normal]
    (σ : Representation (ZMod 2) K W)
    (f : σ.IntertwiningMap (ρ.comp i)) (hf : Function.Injective f)
    (c : K ≃* (Factor × Factor))
    (b : σ.Equiv (baseRepresentation.comp c.toMonoidHom))
    (A : Subgroup H) (hA : IsElementaryTwo A)
    (hAC : A ⊓ centralizer (i.range : Set H) = ⊥)
    (hbudget : fixedCodim ρ A ≤ 2 * rank A) : Function.Surjective f := by
  let e : i.range ≃* K := (MonoidHom.ofInjective hi).symm
  let U : Subrepresentation (ρ.comp i.range.subtype) := {
    toSubmodule := f.range.toSubmodule
    apply_mem_toSubmodule g v hv := by
      obtain ⟨k,hk⟩ := g.property
      change ρ g.val v ∈ f.range.toSubmodule
      rw [←hk]
      exact f.range.apply_mem_toSubmodule k hv }
  let d : W ≃ₗ[ZMod 2] U.toSubmodule := LinearEquiv.ofInjective f.toLinearMap hf
  let bU : U.toRepresentation.Equiv
      (baseRepresentation.comp (e.trans c).toMonoidHom) :=
    .mk (d.symm.trans b.toLinearEquiv) (by
      intro g
      apply LinearMap.ext
      intro v
      obtain ⟨w,rfl⟩ := d.surjective v
      have he : (g : H) = i (e g) := (congrArg Subtype.val
        ((MonoidHom.ofInjective hi).apply_symm_apply g)).symm
      have hd : U.toRepresentation g (d w) = d (σ (e g) w) := by
        apply Subtype.ext
        change ρ g.val (f w) = f (σ (e g) w)
        rw [he]
        exact (LinearMap.congr_fun (f.isIntertwining' (e g)) w).symm
      change b (d.symm (U.toRepresentation g (d w))) =
        baseRepresentation (c (e g)) (b (d.symm (d w)))
      rw [hd,d.symm_apply_apply,d.symm_apply_apply]
      exact LinearMap.congr_fun (b.isIntertwining' (e g)) w)
  have hstable := marked_tensor_constituent_invariant ρ i.range A hA hAC hbudget U
    (e.trans c) bU
  let U' : Subrepresentation ρ := {
    toSubmodule := U.toSubmodule
    apply_mem_toSubmodule g v hv := by
      rw [←hstable g]
      exact Submodule.mem_map_of_mem hv }
  have hne : U' ≠ ⊥ := by
    intro hz
    obtain ⟨w,hw⟩ := exists_ne (0 : W)
    have hh : f w ∈ U'.toSubmodule := ⟨w,rfl⟩
    have hz' : U'.toSubmodule = ⊥ := congrArg Subrepresentation.toSubmodule hz
    rw [hz',Submodule.mem_bot] at hh
    exact hw (hf (hh.trans f.map_zero.symm))
  have ht := (hirr.eq_bot_or_eq_top U').resolve_left hne
  apply LinearMap.range_eq_top.mp
  exact congrArg Subrepresentation.toSubmodule ht
end BinaryTensorThree
