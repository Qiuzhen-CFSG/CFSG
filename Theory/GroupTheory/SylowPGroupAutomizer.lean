module

public import Theory.GroupTheory.NormalizerInnerAutomorphisms
public import Mathlib.GroupTheory.Sylow

/-!
# Sylow normalizers with a p-group automizer

If the normalizer action on a Sylow p-subgroup has p-group image, every
realized automorphism is inner. Indeed the image of the Sylow subgroup in
its normalizer is Sylow in the action image and hence is the whole image.
The preimage of the inner automorphisms is the product of the Sylow
subgroup and its centralizer.

This is the elementary automizer reduction used before applying coprime
automorphisms in MacWilliams, Trans. AMS 150 (1970),
DOI 10.1090/S0002-9947-1970-0276324-3.
-/

open Subgroup

namespace Sylow

/-- A p-group normalizer action is entirely inner. -/
public theorem normalizer_eq_sup_centralizer_of_isPGroup_action {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite G]
    (S : Sylow p G) (ha : IsPGroup p (S : Subgroup G).normalizerMonoidHom.range) :
    normalizer (S : Set G) = (S : Subgroup G) ⊔ centralizer (S : Set G) := by
  let N := normalizer (S : Set G)
  let P : Sylow p N := S.subtype le_normalizer
  let f := (S : Subgroup G).normalizerMonoidHom
  let Q := P.mapSurjective f.rangeRestrict_surjective
  have htop : (⊤ : Subgroup f.range) ≤ Q :=
    (ha.to_subgroup ⊤).le_sylow_of_normal Q
  apply le_antisymm ?_ (sup_le le_normalizer (centralizer_le_normalizer _))
  intro g hg
  have hmem : f.rangeRestrict ⟨g, hg⟩ ∈ (Q : Subgroup f.range) := htop (mem_top _)
  obtain ⟨s, hs, heq⟩ := hmem
  have hsS : (s : G) ∈ (S : Subgroup G) := hs
  have hinner : f ⟨g, hg⟩ ∈ (MulAut.conj : S →* MulAut S).range := by
    refine ⟨⟨s, hsS⟩, ?_⟩
    have hfeq := congrArg Subtype.val heq
    change f s = f ⟨g, hg⟩ at hfeq
    rw [← hfeq]
    ext t
    rfl
  have hh : (⟨g, hg⟩ : N) ∈
      ((MulAut.conj : S →* MulAut S).range.comap f) := hinner
  rw [normalizerMonoidHom_comap_conj_range] at hh
  exact hh

/-- A nontrivial outer normalizer action forces the full automorphism group
of the Sylow subgroup not to be a p-group. -/
public theorem not_isPGroup_mulAut_of_normalizer_ne_sup_centralizer
    {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite G]
    (S : Sylow p G)
    (hne : normalizer (S : Set G) ≠ (S : Subgroup G) ⊔ centralizer (S : Set G)) :
    ¬ IsPGroup p (MulAut S) := by
  intro h
  exact hne (S.normalizer_eq_sup_centralizer_of_isPGroup_action
    (h.to_subgroup _))

end Sylow
