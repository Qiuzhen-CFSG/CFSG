module

public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Tactic.ByContra

/-!
# Normal symmetric-three subgroups of a product

The only normal subgroups of S₃ × S₃ isomorphic to S₃ are the coordinate
factors. Every nontrivial normal subgroup of S₃ contains a fixed three-cycle,
so one coordinate projection of an embedded S₃ must be injective. Normality
then places its other coordinate in the trivial center of S₃.

This elementary product calculation supplies the two-factor orbit assertion
used in Aschbacher–Smith, *The Classification of Quasithin Groups*, proof of
15.3.49(i), combined manuscript (1 March 2004), printed p.1143.
-/

public section
namespace Theory.GroupTheory.PermThreeProduct
open Subgroup
local notation "S3" => Equiv.Perm (Fin 3)
private def cycle : S3 := Equiv.swap 0 1 * Equiv.swap 1 2

private theorem cycle_of_nonidentity : ∀ a : S3, a ≠ 1 →
    cycle = a ∨ cycle = a⁻¹ ∨ ∃ g : S3, cycle = a * (g * a * g⁻¹) := by
  decide +kernel

private theorem cycle_mem (K : Subgroup S3) [K.Normal] (hK : K ≠ ⊥) : cycle ∈ K := by
  obtain ⟨a, ha, hane⟩ : ∃ a ∈ K, a ≠ 1 := by
    by_contra! h
    exact hK (K.eq_bot_iff_forall.mpr h)
  rcases cycle_of_nonidentity a hane with h | h | ⟨g, h⟩
  · exact h ▸ ha
  · exact h ▸ K.inv_mem ha
  · exact h ▸ K.mul_mem ha ((inferInstance : K.Normal).conj_mem a ha g)

private theorem projection_injective (f : S3 →* S3 × S3) (hf : Function.Injective f) :
    Function.Injective ((MonoidHom.fst S3 S3).comp f) ∨
      Function.Injective ((MonoidHom.snd S3 S3).comp f) := by
  let f₁ := (MonoidHom.fst S3 S3).comp f
  let f₂ := (MonoidHom.snd S3 S3).comp f
  by_cases h₁ : f₁.ker = ⊥
  · exact Or.inl ((MonoidHom.ker_eq_bot_iff f₁).mp h₁)
  · right
    apply (MonoidHom.ker_eq_bot_iff f₂).mp
    by_contra h₂
    have hc₁ := cycle_mem f₁.ker h₁
    have hc₂ := cycle_mem f₂.ker h₂
    have hc : f cycle = 1 := Prod.ext hc₁ hc₂
    have hne : cycle ≠ 1 := by decide +kernel
    exact hne (hf (hc.trans f.map_one.symm))

private theorem center_trivial : ∀ x : S3, (∀ y, y * x * y⁻¹ = x) → x = 1 := by
  decide +kernel

private theorem range_eq_first (f : S3 →* S3 × S3) [f.range.Normal]
    (hf : Function.Injective ((MonoidHom.fst S3 S3).comp f)) :
    f.range = (⊤ : Subgroup S3).prod ⊥ := by
  have hsecond (a : S3) : (f a).2 = 1 := by
    apply center_trivial
    intro y
    have hmem := (inferInstance : f.range.Normal).conj_mem (f a) ⟨a, rfl⟩ (1, y)
    obtain ⟨b, hb⟩ := hmem
    have hab : b = a := hf (by simpa using congrArg Prod.fst hb)
    simpa [hab] using (congrArg Prod.snd hb).symm
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨mem_top _, hsecond a⟩
  · intro hx
    obtain ⟨a, ha⟩ := Finite.surjective_of_injective hf x.1
    refine ⟨a, Prod.ext ha ?_⟩
    exact (hsecond a).trans hx.2.symm


private theorem range_eq_coordinate (f : S3 →* S3 × S3) [f.range.Normal]
    (hf : Function.Injective f) :
    f.range = (⊤ : Subgroup S3).prod ⊥ ∨ f.range = (⊥ : Subgroup S3).prod ⊤ := by
  rcases projection_injective f hf with h | h
  · exact Or.inl (range_eq_first f h)
  · right
    let s : S3 × S3 ≃* S3 × S3 := MulEquiv.prodComm
    let fs := s.toMonoidHom.comp f
    have hnormal : fs.range.Normal := by
      rw [MonoidHom.range_comp]
      exact (inferInstance : f.range.Normal).map _ s.surjective
    have he := range_eq_first fs h
    rw [MonoidHom.range_comp] at he
    ext x
    have hm := SetLike.ext_iff.mp he (s x)
    simpa [Subgroup.mem_map_equiv, s, Subgroup.mem_prod] using hm

/-- A normal S₃ in S₃ × S₃ is one of the two coordinate factors. -/
theorem normal_subgroup_eq_factor (N : Subgroup (S3 × S3)) [N.Normal]
    (e : N ≃* S3) :
    N = (⊤ : Subgroup S3).prod ⊥ ∨ N = (⊥ : Subgroup S3).prod ⊤ := by
  let f := N.subtype.comp e.symm.toMonoidHom
  have hrange : f.range = N := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr e.symm.surjective,
      ← MonoidHom.range_eq_map, range_subtype]
  have : f.range.Normal := hrange ▸ inferInstance
  simpa only [hrange] using range_eq_coordinate f (N.subtype_injective.comp e.symm.injective)

end Theory.GroupTheory.PermThreeProduct
