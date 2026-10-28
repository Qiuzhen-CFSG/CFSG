module

public import Theory.Representation.BinaryConjugationSection
public import Theory.GroupAction.SubgroupConjugation
public import Theory.ElementaryAbelian.VectorSpace

/-!
# Elementary conjugation actions through a central kernel

Conjugation on an actual elementary abelian subgroup R descends through
any surjective actor map whose kernel centralizes R. The coordinates are
the identity on the additive type of R, with trivial section kernel.

This provides the original R-action, before recognizing its splitting,
in Aschbacher–Smith 14.7.72, printed p.1076 (1 March 2004 manuscript).
-/

public section

open Subgroup
open scoped IsMulCommutative
namespace Representation.BinaryConjugationSection
theorem exists_action_of_central_kernel
    {G D : Type*} [Group G] [Group D]
    (H R : Subgroup G) (hNR : H ≤ normalizer R)
    [IsElementaryAbelian 2 R]
    (q : H →* D) (hq : Function.Surjective q)
    (hk : ∀ h ∈ q.ker, (h : G) ∈ centralizer (R : Set G)) :
    ∃ σ : Representation (ZMod 2) D (Additive R),
      ∀ (h : H) (r : Additive R),
        ((σ (q h) r).toMul : G) = h * r.toMul * (h : G)⁻¹ := by
  let i : H →* normalizer R := H.subtype.codRestrict _ (fun h => hNR h.property)
  let α : H →* MulAut R := R.normalizerMonoidHom.comp i
  have hkill : q.ker ≤ α.ker := by
    intro h hh
    apply MulEquiv.ext
    intro r
    apply Subtype.ext
    change (h : G) * (r : G) * (h : G)⁻¹ = r
    rw [← hk h hh r r.property, mul_inv_cancel_right]
  let β : D →* MulAut R := q.liftOfSurjective hq ⟨α,hkill⟩
  have hβ (h : H) : β (q h) = α h :=
    q.liftOfRightInverse_comp_apply (Function.surjInv hq)
      (Function.rightInverse_surjInv hq) ⟨α,hkill⟩ h
  let σ : Representation (ZMod 2) D (Additive R) := {
    toFun a := (β a).toMonoidHom.toAdditive.toZModLinearMap 2
    map_one' := by
      apply LinearMap.ext
      intro v
      change β 1 v.toMul = v.toMul
      rw [map_one]
      rfl
    map_mul' a b := by
      apply LinearMap.ext
      intro v
      change β (a * b) v.toMul = β a (β b v.toMul)
      rw [map_mul]
      rfl }
  refine ⟨σ, ?_⟩
  intro h r
  change ((β (q h) r.toMul : R) : G) = _
  rw [hβ]
  rfl

/-- With containment in the actor, the descended action gives a literal section. -/
theorem exists_of_central_kernel
    {G D : Type*} [Group G] [Group D]
    (H R : Subgroup G) (hRH : R ≤ H) (hNR : H ≤ normalizer R)
    [IsElementaryAbelian 2 R]
    (q : H →* D) (hq : Function.Surjective q)
    (hk : ∀ h ∈ q.ker, (h : G) ∈ centralizer (R : Set G)) :
    ∃ (σ : Representation (ZMod 2) D (Additive R))
      (d : BinaryConjugationSection H R ⊥ (σ.comp q)),
      ∀ r : R, (d.coordinates r).toAdd = Additive.ofMul r := by
  obtain ⟨σ,hσ⟩ := exists_action_of_central_kernel H R hNR q hq hk
  let c : R →* Multiplicative (Additive R) := {
    toFun := fun r => Multiplicative.ofAdd (Additive.ofMul r)
    map_one' := rfl
    map_mul' _ _ := rfl }
  refine ⟨σ, {
    section_le := hRH
    kernel_le := bot_le
    normalized := hNR
    coordinates := c
    onto := fun r => ⟨r.toAdd.toMul, rfl⟩
    kernel_eq := by
      ext r
      change r = 1 ↔ (r : G) = 1
      exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
    equivariant := ?_ }, fun _ => rfl⟩
  intro h r
  apply Additive.toMul.injective
  apply Subtype.ext
  exact (hσ h (Additive.ofMul r)).symm

end Representation.BinaryConjugationSection
