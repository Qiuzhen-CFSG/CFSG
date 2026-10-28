module

public import Theory.SpecificGroups.Held.LocalPairs.Transport
public import Theory.GroupTheory.ThreeConjugateAutomorphisms
public import Theory.GroupAction.AutomorphismFixedTransport

/-!
# Transport of three-conjugate generation for Held

Map a generating triple from the literal permutation normalizer to its
induced automorphism group. Transport by any actual automorphism preserves
the inner subgroup and carries the two conjugators to actual Held elements.
These lemmas connect the checked representative words to the existing inner
and outer involution fusion theorems.

Source: Revin–Zavarnitsine, arXiv:2505.05173v2, Theorems 1–2.
-/

@[expose] public section
open Subgroup
namespace Held.ThreeConjugates
open LocalPairs

/-- The required generation condition for one specified automorphism. -/
def HasTriple (t : MulAut He) : Prop :=
  ∃ g h : He, (MulAut.conj : He →* MulAut He).range ≤
    zpowers t ⊔ zpowers (MulAut.conj g * t * (MulAut.conj g)⁻¹) ⊔
      zpowers (MulAut.conj h * t * (MulAut.conj h)⁻¹)

/-- Transport preserves actual inner generation and actual Held conjugators. -/
theorem hasTriple_congr {t : MulAut He} (ht : HasTriple t) (e : MulAut He) :
    HasTriple (MulAut.congr e t) := by
  obtain ⟨g, h, hgen⟩ := ht
  refine ⟨e g, e h, ?_⟩
  intro x hx
  obtain ⟨y, rfl⟩ := hx
  have hm := mem_map_of_mem (MulAut.congr e).toMonoidHom
    (hgen (show MulAut.conj (e.symm y) ∈ (MulAut.conj : He →* MulAut He).range
      from ⟨e.symm y, rfl⟩))
  simpa only [Subgroup.map_sup, MonoidHom.map_zpowers, MulEquiv.coe_toMonoidHom,
    map_mul, map_inv, MulAut.congr_conj, e.apply_symm_apply] using hm

/-- The normalizer action carries certified generator containment to automorphisms. -/
theorem hasTriple_of_normalizer (t : PermutationNormalizer) (g h : He)
    (hgen : innerEmbedding.range ≤
      zpowers t ⊔ zpowers (innerEmbedding g * t * (innerEmbedding g)⁻¹) ⊔
        zpowers (innerEmbedding h * t * (innerEmbedding h)⁻¹)) :
    HasTriple (permutationGroup.normalizerMonoidHom t) := by
  refine ⟨g, h, ?_⟩
  rintro x ⟨y, rfl⟩
  have hm := mem_map_of_mem permutationGroup.normalizerMonoidHom
    (hgen (show innerEmbedding y ∈ innerEmbedding.range from ⟨y, rfl⟩))
  simpa only [Subgroup.map_sup, MonoidHom.map_zpowers, map_mul, map_inv,
    normalizerAction_innerEmbedding] using hm

end Held.ThreeConjugates
