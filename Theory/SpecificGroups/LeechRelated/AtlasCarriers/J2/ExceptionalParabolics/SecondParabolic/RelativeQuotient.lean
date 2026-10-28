module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.PairNormalizer.QuotientSeed

/-!
# The relative normal-closure quotient in the Hall--Janko parabolic

Given an isomorphism `p₂ / q₂ ≃ S₃ × C₃`, the image of `s` has order
`128 / 64 = 2`. Its elements have trivial second coordinate, and any
nonidentity involution normally generates the first factor. Surjectivity
therefore carries the normal closure defining `l₂` to precisely `S₃ × 1`.
Projection to the first coordinate gives a surjection from the literal
`Seed.l₂` with kernel `q₂.subgroupOf l₂`, yielding the quotient equivalence.

Normal closure and normality are relative to `Seed.p₂` throughout. This
conditional helper leaves the full-normalizer quotient as an explicit
premise; its assembly owner discharges that premise and identifies `q₂`
with the intrinsic two-core. No core identification is used here.

Source: Aschbacher--Smith, F.1.12(I)(10)--(11), printed p.263 (PDF p.274).
-/

namespace Sporadic.LeechRelated.J2.ExceptionalParabolics.SecondParabolic
open Subgroup PairNormalizer

private theorem involution_snd : ∀ x : QuotientModel, x ^ 2 = 1 → x.2 = 1 := by
  decide +kernel

private theorem perm_three_generation : ∀ t : Equiv.Perm (Fin 3),
    t ^ 2 = 1 → t ≠ 1 → ∀ u : Equiv.Perm (Fin 3),
      u = 1 ∨ (∃ a, u = a * t * a⁻¹) ∨
        (∃ a b, u = (a * t * a⁻¹) * (b * t * b⁻¹)) := by
  decide +kernel

private theorem normalClosure_order_two
    (H : Subgroup QuotientModel) (hH : Nat.card H = 2) :
    normalClosure (H : Set QuotientModel) =
      (MonoidHom.snd (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 3))).ker := by
  have hsquare (x : H) : (x : QuotientModel) ^ 2 = 1 := by
    have hx := pow_card_eq_one' (x := x)
    rw [hH] at hx
    exact congrArg H.subtype hx
  have hsnd (x : H) : (x : QuotientModel).2 = 1 :=
    involution_snd x (hsquare x)
  apply le_antisymm
  · exact normalClosure_le_normal (fun x hx => hsnd ⟨x, hx⟩)
  · obtain ⟨t, ht⟩ := ne_bot_iff_exists_ne_one.mp
      (H.one_lt_card_iff_ne_bot.mp (by omega))
    have ht₁ : (t : QuotientModel).1 ≠ 1 := by
      intro ht₁
      apply ht
      apply Subtype.ext
      exact Prod.ext ht₁ (hsnd t)
    have ht₂ : (t : QuotientModel).1 ^ 2 = 1 :=
      congrArg Prod.fst (hsquare t)
    have hconj (a : Equiv.Perm (Fin 3)) :
        (a * (t : QuotientModel).1 * a⁻¹, (1 : Multiplicative (ZMod 3))) ∈
          normalClosure (H : Set QuotientModel) := by
      have hc := (inferInstance : (normalClosure (H : Set QuotientModel)).Normal).conj_mem
        (t : QuotientModel) (subset_normalClosure t.property) (a, 1)
      simpa only [Prod.mul_def, Prod.inv_mk, hsnd t, mul_one, one_mul, inv_one] using hc
    rintro ⟨u, v⟩ hv
    change v = 1 at hv
    subst v
    rcases perm_three_generation _ ht₂ ht₁ u with rfl | ⟨a, rfl⟩ | ⟨a, b, rfl⟩
    · exact (normalClosure _).one_mem
    · exact hconj a
    · simpa only [Prod.mul_def, mul_one] using (normalClosure _).mul_mem (hconj a) (hconj b)

open Seed

private theorem sylow_image_card
    (f : p₂ →* QuotientModel) (hfker : f.ker = q₂.subgroupOf p₂) :
    Nat.card ((s.subgroupOf p₂).map f) = 2 := by
  rw [← relIndex_ker, hfker, relIndex_subgroupOf s_le_p₂]
  have hc : Nat.card (q₂.subgroupOf s) = 64 :=
    (Nat.card_congr (subgroupOfEquivOfLe q₂_le_s).toEquiv).trans card_q₂
  have h := (q₂.subgroupOf s).card_mul_index
  rw [hc, card_s] at h
  change (q₂.subgroupOf s).index = 2
  omega

private theorem normalClosure_image
    (f : p₂ →* QuotientModel) (hf : Function.Surjective f)
    (hfker : f.ker = q₂.subgroupOf p₂) :
    (l₂.subgroupOf p₂).map f =
      (MonoidHom.snd (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 3))).ker := by
  rw [l₂_subgroupOf_p₂, map_normalClosure _ _ hf, ← coe_map]
  exact normalClosure_order_two _ (sylow_image_card f hfker)

/-- The full-normalizer quotient determines the quotient of its relative normal closure. -/
public theorem l₂_radical_quotient_of_p₂_radical_quotient
    (hP : Nonempty ((p₂ ⧸ q₂.subgroupOf p₂) ≃* QuotientModel)) :
    Nonempty ((l₂ ⧸ q₂.subgroupOf l₂) ≃* Equiv.Perm (Fin 3)) := by
  obtain ⟨e⟩ := hP
  let f : p₂ →* QuotientModel := e.toMonoidHom.comp (QuotientGroup.mk' _)
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hfker : f.ker = q₂.subgroupOf p₂ := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
  have himage := normalClosure_image f hf hfker
  let j : l₂ →* p₂ := Subgroup.inclusion l₂_le_p₂
  let g : l₂ →* Equiv.Perm (Fin 3) :=
    (MonoidHom.fst _ _).comp (f.comp j)
  have hsnd (x : l₂) : (f (j x)).2 = 1 := by
    have hx : f (j x) ∈ (l₂.subgroupOf p₂).map f := ⟨j x, x.property, rfl⟩
    rw [himage] at hx
    exact hx
  have hg : Function.Surjective g := by
    intro u
    have hu : (u, (1 : Multiplicative (ZMod 3))) ∈ (l₂.subgroupOf p₂).map f := by
      rw [himage]
      rfl
    obtain ⟨x, hx, heq⟩ := hu
    refine ⟨⟨x, hx⟩, ?_⟩
    exact congrArg Prod.fst heq
  have hgker : g.ker = q₂.subgroupOf l₂ := by
    ext x
    change (f (j x)).1 = 1 ↔ (x : Carrier) ∈ q₂
    have hmem : (j x ∈ f.ker) ↔ (x : Carrier) ∈ q₂ := by
      rw [hfker]
      rfl
    rw [← hmem]
    change (f (j x)).1 = 1 ↔ f (j x) = 1
    exact ⟨fun h => Prod.ext h (hsnd x), fun h => congrArg Prod.fst h⟩
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hgker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective g hg)⟩

end Sporadic.LeechRelated.J2.ExceptionalParabolics.SecondParabolic
