module

public import Theory.GroupTheory.FourWreathTwoCores
public import Stellmacher.ElementaryAbelianMaxJMap
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# The Thompson subgroup of the Aut(M₁₂) wreath quotient

The base is elementary abelian of order sixteen. Every abelian subgroup
larger than eight lies in it, so it is the unique elementary abelian subgroup
of maximum order. Consequently the actual elementary Thompson subgroup of
`E₄ ≀ C₂` is its base.

Source: Aschbacher--Smith, Lemma 14.2.21, printed p.988 (PDF p.1005).
-/

namespace FourWreathTwo

open Stellmacher

/-- The maximum-order elementary family has just the base as a member. -/
public theorem max_elementary_family :
    elementaryAbelianMaxSubgroups (⊤ : Subgroup Wreath) = {base} := by
  ext A
  constructor
  · intro hA
    let : IsElementaryAbelian 2 A := hA.2.1
    have hcard : 16 ≤ Nat.card A := by
      simpa only [card_base] using hA.2.2 base le_top base_elementary
    have hAb : A ≤ base := large_abelian_le_base A (by omega)
    exact Subgroup.eq_of_le_of_card_ge hAb (by simpa only [card_base] using hcard)
  · rintro rfl
    refine ⟨le_top, base_elementary, ?_⟩
    intro B _ hB
    let : IsElementaryAbelian 2 B := hB
    by_cases hsmall : Nat.card B ≤ 8
    · rw [card_base]
      omega
    · exact Subgroup.card_le_of_le (large_abelian_le_base B (by omega))

/-- The elementary Thompson subgroup in the source wreath model. -/
public theorem elementary_thompson_eq_base :
    elementaryAbelianMaxJ (⊤ : Subgroup Wreath) = base := by
  rw [elementaryAbelianMaxJ, max_elementary_family, sSup_singleton]

/-- Transport the Thompson calculation to the literal central quotient,
identifying the answer with the image of the specified quaternion core. -/
public theorem elementary_thompson_quotient_eq_base_image
    {D : Type*} [Group D] (Z QK : Subgroup D) [Z.Normal]
    (e : D ⧸ Z ≃* Wreath)
    (hQK : QK = base.comap (e.toMonoidHom.comp (QuotientGroup.mk' Z))) :
    elementaryAbelianMaxJ (⊤ : Subgroup (D ⧸ Z)) =
      QK.map (QuotientGroup.mk' Z) := by
  have hQKmap : (QK.map (QuotientGroup.mk' Z)).map e.toMonoidHom = base := by
    rw [Subgroup.map_map, hQK, Subgroup.map_comap_eq_self_of_surjective
      (e.surjective.comp (QuotientGroup.mk'_surjective Z))]
  have hJ := elementaryAbelianMaxJ_map_injective e.toMonoidHom e.injective
    (⊤ : Subgroup (D ⧸ Z))
  rw [Subgroup.map_top_of_surjective _ e.surjective, elementary_thompson_eq_base] at hJ
  apply le_antisymm
  · apply (Subgroup.map_le_map_iff_of_injective (f := e.toMonoidHom) e.injective).mp
    rw [← hJ, hQKmap]
  · apply (Subgroup.map_le_map_iff_of_injective (f := e.toMonoidHom) e.injective).mp
    rw [← hJ, hQKmap]

end FourWreathTwo
