module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.SecondParabolic.Overlap.Inner

/-!
# The whole outer Hall--Janko overlap

The fixed outer involution preserves s, its characteristic radical q₂,
and the relative normal closure l₂ in p₂. A checked identity also shows
that it fixes the involution defining l₁. Hence it normalizes both full
parabolics and their inner intersection B. Adjoining it doubles B to 768.
Its odd parity separates the two cosets of the inner carrier, so the
intersection of the enlarged parabolics is exactly the enlarged Borel.
The checked inner generation and the same coset argument give generation
of the explicit permutation extension.

Source: Aschbacher--Smith F.1.1, F.1.3 and F.1.12(I)(11), pp.259--263.
The first-local order and the full-normalizer order remain explicit inputs;
the latter is derived from the permitted quotient in Overlap.Inner.
-/

@[expose] public section
namespace Sporadic.LeechRelated.J2.ExceptionalParabolics.SecondParabolic.Overlap
open Theory.GroupTheory GeneratorPair Seed PairNormalizer
open PairNormalizer.SylowData PairNormalizer.QuotientData
open GeneratorPair.SecondOrbitCertificate
open scoped Pointwise

private theorem restriction_comp {H : Subgroup Carrier} (e : MulAut Carrier)
    (hH : H.map e.toMonoidHom = H) :
    H.subtype.comp ((e.subgroupMap H).trans (MulEquiv.subgroupCongr hH)).toMonoidHom =
      e.toMonoidHom.comp H.subtype := rfl

private theorem map_q₂_of_map_s (e : MulAut Carrier) (hs : s.map e.toMonoidHom = s) :
    q₂.map e.toMonoidHom = q₂ := by
  let f : MulAut s := (e.subgroupMap s).trans (MulEquiv.subgroupCongr hs)
  have hq := Subgroup.characteristic_iff_map_eq.mp q₂_characteristic f
  have hh := congrArg (Subgroup.map s.subtype) hq
  rw [Subgroup.map_map, restriction_comp, ← Subgroup.map_map,
    Subgroup.map_subgroupOf_eq_of_le q₂_le_s] at hh
  exact hh

private theorem map_p₂_of_map_s (e : MulAut Carrier) (hs : s.map e.toMonoidHom = s) :
    p₂.map e.toMonoidHom = p₂ := by
  rw [p₂, Subgroup.map_equiv_normalizer_eq, map_q₂_of_map_s e hs]

private theorem map_l₂_of_map_s (e : MulAut Carrier) (hs : s.map e.toMonoidHom = s) :
    l₂.map e.toMonoidHom = l₂ := by
  have hp := map_p₂_of_map_s e hs
  let f : MulAut p₂ := (e.subgroupMap p₂).trans (MulEquiv.subgroupCongr hp)
  have hf : p₂.subtype.comp f.toMonoidHom = e.toMonoidHom.comp p₂.subtype := rfl
  have hs' : (s.subgroupOf p₂).map f.toMonoidHom = s.subgroupOf p₂ := by
    apply Subgroup.map_injective p₂.subtype_injective
    rw [Subgroup.map_map, hf, ← Subgroup.map_map,
      Subgroup.map_subgroupOf_eq_of_le s_le_p₂, hs]
  change ((Subgroup.normalClosure (s.subgroupOf p₂ : Set p₂)).map p₂.subtype).map
    e.toMonoidHom = _
  rw [Subgroup.map_map, ← hf, ← Subgroup.map_map,
    Subgroup.map_normalClosure _ _ f.surjective, ← Subgroup.coe_map, hs']
  rfl

/-- Conjugation in the literal extension agrees with its checked action on the carrier. -/
private theorem extensionAction_into (g : Extension) (x : Carrier) :
    intoExtension (extensionAction g x) = g * intoExtension x * g⁻¹ := by
  apply extension.subtype_injective
  rfl

private theorem extensionAction_comp (g : Extension) :
    intoExtension.comp (extensionAction g).toMonoidHom =
      (MulAut.conj g).toMonoidHom.comp intoExtension := by
  apply MonoidHom.ext
  intro x
  exact extensionAction_into g x

set_option maxRecDepth 2000 in
private theorem outerAction_map_s : s.map (extensionAction outerElement).toMonoidHom = s := by
  apply Subgroup.map_injective intoExtension_injective
  rw [Subgroup.map_map]
  rw [extensionAction_comp, ← Subgroup.map_map]
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mp outerElement_normalizes_s

set_option maxRecDepth 2000 in
private theorem normalizes_of_invariant (g : Extension) (H : Subgroup Carrier)
    (hH : H.map (extensionAction g).toMonoidHom = H) :
    g ∈ Subgroup.normalizer (H.map intoExtension : Set Extension) := by
  apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
  rw [Subgroup.map_map]
  change H.map ((MulAut.conj g).toMonoidHom.comp intoExtension) = H.map intoExtension
  rw [← extensionAction_comp, ← Subgroup.map_map, hH]

set_option maxRecDepth 100000 in
private theorem outerAction_z : extensionAction outerElement z = z := by
  apply intoExtension_injective
  rw [extensionAction_into]
  apply extension.subtype_injective
  rw [map_mul, map_mul, map_inv, outerElement_inclusion]
  change outerTable * inclusion z * outerTable⁻¹ = inclusion z
  rw [show inclusion z = FirstFusion.tPerm from FirstFusion.inclusion_t]
  decide +kernel

set_option maxRecDepth 2000 in
private theorem outerAction_map_l₁ : l₁.map (extensionAction outerElement).toMonoidHom = l₁ := by
  have hle : l₁.map (extensionAction outerElement).toMonoidHom ≤ l₁ := by
    rintro _ ⟨x, hx, rfl⟩
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    have h := congrArg (extensionAction outerElement)
      (Subgroup.mem_centralizer_singleton_iff.mp hx)
    simpa only [map_mul, MulEquiv.coe_toMonoidHom, outerAction_z] using h
  exact Subgroup.eq_of_le_of_card_ge hle
    (le_of_eq (Subgroup.card_map_of_injective (extensionAction outerElement).injective).symm)

theorem outerElement_normalizes_l₁ :
    outerElement ∈ Subgroup.normalizer (l₁.map intoExtension : Set Extension) :=
  normalizes_of_invariant outerElement _ outerAction_map_l₁

theorem outerElement_normalizes_p₂ :
    outerElement ∈ Subgroup.normalizer (p₂.map intoExtension : Set Extension) :=
  normalizes_of_invariant outerElement _ (map_p₂_of_map_s _ outerAction_map_s)

theorem outerElement_normalizes_l₂ :
    outerElement ∈ Subgroup.normalizer (l₂.map intoExtension : Set Extension) :=
  normalizes_of_invariant outerElement _ (map_l₂_of_map_s _ outerAction_map_s)

def outerB : Subgroup Extension := B.map intoExtension ⊔ Subgroup.zpowers outerElement

theorem outerElement_normalizes_B (hP : Nat.card p₂ = 1152) :
    outerElement ∈ Subgroup.normalizer (B.map intoExtension : Set Extension) := by
  rw [← l₁_inf_p₂_eq_B hP, Subgroup.map_inf _ _ intoExtension intoExtension_injective]
  exact Subgroup.inf_normalizer_le_normalizer_inf
    ⟨outerElement_normalizes_l₁, outerElement_normalizes_p₂⟩

theorem card_outerB (hP : Nat.card p₂ = 1152) : Nat.card outerB = 768 := by
  rw [outerB, Subgroup.card_sup_zpowers_of_normalizing_involution _ _ outerElement_sq
    (fun h => outerElement_not_mem_range ((B.map_le_range intoExtension) h))
    (outerElement_normalizes_B hP),
    Subgroup.card_map_of_injective intoExtension_injective, card_B]

theorem outerB_normalizes (i : Fin 2) :
    outerB ≤ Subgroup.normalizer (outerL i : Set Extension) := by
  apply sup_le
  · exact (Subgroup.map_mono (B_normalizes i)).trans (Subgroup.le_normalizer_map _)
  · apply Subgroup.zpowers_le.mpr
    fin_cases i
    · exact outerElement_normalizes_l₁
    · exact outerElement_normalizes_l₂

private theorem outer_power_cases {x : Extension} (hx : x ∈ Subgroup.zpowers outerElement) :
    x = 1 ∨ x = outerElement := by
  have htne : outerElement ≠ 1 := fun h => outerElement_not_mem_range (h ▸ intoExtension.range.one_mem)
  have ho : orderOf outerElement = 2 := orderOf_eq_prime outerElement_sq htne
  rw [(isOfFinOrder_of_finite outerElement).mem_zpowers_iff_mem_range_orderOf, ho] at hx
  obtain ⟨i, hi, hix⟩ := Finset.mem_image.mp hx
  have hi2 := Finset.mem_range.mp hi
  have hi' : i = 0 ∨ i = 1 := by omega
  rcases hi' with rfl | rfl
  · exact Or.inl (by simpa using hix.symm)
  · exact Or.inr (by simpa using hix.symm)

private theorem sup_outer_inf_range (H : Subgroup Carrier)
    (hn : outerElement ∈ Subgroup.normalizer (H.map intoExtension : Set Extension)) :
    (H.map intoExtension ⊔ Subgroup.zpowers outerElement) ⊓ intoExtension.range =
      H.map intoExtension := by
  apply le_antisymm
  · intro x hx
    have hp : x ∈ (H.map intoExtension : Set Extension) * (Subgroup.zpowers outerElement : Set Extension) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left _ _ (Subgroup.zpowers_le.mpr hn)]
      exact hx.1
    obtain ⟨y, hy, t, ht, hyt⟩ := hp
    rcases outer_power_cases ht with rfl | rfl
    · have he : y = x := by simpa only [mul_one] using hyt
      exact he ▸ hy
    · have he : outerElement ∈ intoExtension.range := by
        have h := intoExtension.range.mul_mem
          (intoExtension.range.inv_mem ((H.map_le_range intoExtension) hy)) hx.2
        rw [← hyt, inv_mul_cancel_left] at h
        exact h
      exact (outerElement_not_mem_range he).elim
  · exact le_inf le_sup_left (H.map_le_range intoExtension)

theorem outer_overlap (h₁ : Nat.card l₁ = 1920) (hP : Nat.card p₂ = 1152) :
    (outerL 0 ⊔ outerB) ⊓ (outerL 1 ⊔ outerB) = outerB := by
  have h0 : outerL 0 ⊔ outerB = l₁.map intoExtension ⊔ Subgroup.zpowers outerElement := by
    change l₁.map intoExtension ⊔ (B.map intoExtension ⊔ _) = _
    rw [← sup_assoc, sup_of_le_left (Subgroup.map_mono B_le_l₁)]
  have h1 : outerL 1 ⊔ outerB = p₂.map intoExtension ⊔ Subgroup.zpowers outerElement := by
    change l₂.map intoExtension ⊔ (B.map intoExtension ⊔ _) = _
    rw [← sup_assoc, ← Subgroup.map_sup, l₂_sup_B h₁ hP]
  rw [h0, h1]
  apply le_antisymm
  · intro x hx
    have hp : x ∈ (l₁.map intoExtension : Set Extension) * (Subgroup.zpowers outerElement : Set Extension) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left _ _
        (Subgroup.zpowers_le.mpr outerElement_normalizes_l₁)]
      exact hx.1
    obtain ⟨y, hy, t, ht, hyt⟩ := hp
    have hy2 : y ∈ p₂.map intoExtension ⊔ Subgroup.zpowers outerElement := by
      have hh := (p₂.map intoExtension ⊔ Subgroup.zpowers outerElement).mul_mem hx.2
        ((le_sup_right : Subgroup.zpowers outerElement ≤ _)
          ((Subgroup.zpowers outerElement).inv_mem ht))
      simpa only [← hyt, mul_inv_cancel_right] using hh
    have hyP : y ∈ p₂.map intoExtension := by
      rw [← sup_outer_inf_range p₂ outerElement_normalizes_p₂]
      exact ⟨hy2, (l₁.map_le_range intoExtension) hy⟩
    have hyB : y ∈ B.map intoExtension := by
      rw [← l₁_inf_p₂_eq_B hP, Subgroup.map_inf _ _ intoExtension intoExtension_injective]
      exact ⟨hy, hyP⟩
    rw [← hyt]
    exact Subgroup.mul_mem_sup hyB ht
  · exact le_inf (sup_le_sup_right (Subgroup.map_mono B_le_l₁) _)
      (sup_le_sup_right (Subgroup.map_mono B_le_p₂) _)

private theorem range_normalizes :
    (⊤ : Subgroup Extension) ≤ Subgroup.normalizer (intoExtension.range : Set Extension) := by
  apply Subgroup.le_normalizer_iff.mpr
  rintro g _ x ⟨y, rfl⟩
  exact ⟨extensionAction g y, extensionAction_into g y⟩

theorem range_sup_outer (h₁ : Nat.card l₁ = 1920) :
    intoExtension.range ⊔ Subgroup.zpowers outerElement = ⊤ := by
  apply Subgroup.eq_of_le_of_card_ge le_top
  have hc : Nat.card intoExtension.range = 604800 := by
    rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective intoExtension_injective]
    simpa using card_carrier h₁
  rw [Subgroup.card_sup_zpowers_of_normalizing_involution _ _ outerElement_sq
    outerElement_not_mem_range (range_normalizes (Subgroup.mem_top _)), hc]
  simpa using le_of_eq (card_extension h₁)

theorem outerL_generate (h₁ : Nat.card l₁ = 1920) (hP : Nat.card p₂ = 1152) :
    outerL 0 ⊔ outerL 1 ⊔ outerS = ⊤ := by
  change (L 0).map intoExtension ⊔ (L 1).map intoExtension ⊔
    (s.map intoExtension ⊔ Subgroup.zpowers outerElement) = ⊤
  rw [← sup_assoc, ← Subgroup.map_sup, ← Subgroup.map_sup, L_generate h₁ hP,
    ← MonoidHom.range_eq_map, range_sup_outer h₁]

end Sporadic.LeechRelated.J2.ExceptionalParabolics.SecondParabolic.Overlap
