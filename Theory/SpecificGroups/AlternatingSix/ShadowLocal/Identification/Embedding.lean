module
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.Identification.Generators
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.Identification.Presentation

/-!
# The explicit holomorph inside Aut(A₆)

The marked automorphisms satisfy the presentation, giving an actual
injective homomorphism. Its image has order 32 and is Sylow. Every
Sylow subgroup is conjugate to this image by a permutation-induced
automorphism: a general conjugator can be multiplied by the exceptional
rotation in the image to place it in the index-two natural S₆.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
combined 1 March 2004 manuscript, printed pp.567–570.
-/

public section
open Subgroup
namespace AlternatingSix.ShadowLocal

@[expose] def sylowNatural (P : Sylow 2 AutA6) : Subgroup P :=
  natural.comap (P : Subgroup AutA6).subtype

theorem sylowNatural_card (P : Sylow 2 AutA6) : Nat.card (sylowNatural P) = 16 := by
  let : natural.Normal := Subgroup.normal_of_index_eq_two
    GLS3.Chapter5.naturalAlternatingAutomorphismSubgroup_index
  obtain ⟨D, hD⟩ := P.exists_subgroupOf_eq_of_normal natural
  let swap : sylowNatural P ≃* (P : Subgroup AutA6).subgroupOf natural := {
    toFun x := ⟨⟨x.1.1, x.2⟩, x.1.2⟩
    invFun x := ⟨⟨x.1.1, x.2⟩, x.1.2⟩
    left_inv _ := rfl
    right_inv _ := rfl
    map_mul' _ _ := rfl }
  rw [Nat.card_congr swap.toEquiv, ← hD]
  rw [D.card_eq_multiplicity, card_natural]
  rw [show 720 = 2 ^ 4 * 45 by decide,
    Nat.factorization_mul (by decide) (by decide), Finsupp.add_apply,
    Nat.prime_two.factorization_pow, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 45)]
  rfl

namespace Identification

private theorem embedding_exists :
    ∃ f : Holomorph.Model →* AutA6, Function.Injective f ∧
      f Holomorph.rotation = rotation ∧ f Holomorph.transposition = transposition ∧
      f Holomorph.reflection = reflection :=
  Holomorph.exists_injective_hom_of_relations rotation transposition reflection
    rotation_order transposition_sq reflection_sq transposition_reflection
    transposition_rotation reflection_rotation

noncomputable def embedding : Holomorph.Model →* AutA6 := Classical.choose embedding_exists

theorem embedding_injective : Function.Injective embedding :=
  (Classical.choose_spec embedding_exists).1

theorem embedding_rotation : embedding Holomorph.rotation = rotation :=
  (Classical.choose_spec embedding_exists).2.1

theorem embedding_transposition : embedding Holomorph.transposition = transposition :=
  (Classical.choose_spec embedding_exists).2.2.1

theorem embedding_reflection : embedding Holomorph.reflection = reflection :=
  (Classical.choose_spec embedding_exists).2.2.2

private theorem range_card : Nat.card embedding.range = 32 := by
  rw [← Nat.card_congr (MonoidHom.ofInjective embedding_injective).toEquiv,
    Holomorph.card_model]

/-- Every actual Sylow subgroup is a permutation conjugate of the explicit image. -/
theorem exists_permutation_conjugator (P : Sylow 2 AutA6) :
    ∃ σ : Equiv.Perm (Fin 6),
      embedding.range.map (MulAut.conj (permutationAction σ)).toMonoidHom =
        (P : Subgroup AutA6) := by
  have hp : IsPGroup 2 embedding.range :=
    IsPGroup.of_card (show Nat.card embedding.range = 2 ^ 5 from range_card)
  obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
  have he : embedding.range = (Q : Subgroup AutA6) :=
    Subgroup.eq_of_le_of_card_ge hQ (by rw [range_card, sylow_card])
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq AutA6 Q P
  have hrQ : rotation ∈ (Q : Subgroup AutA6) := hQ ⟨_, embedding_rotation⟩
  have hrfix : rotation • Q = Q :=
    Sylow.smul_eq_iff_mem_normalizer.mpr ((Q : Subgroup AutA6).le_normalizer hrQ)
  have hnat : ∃ n ∈ natural, n • Q = P := by
    by_cases hn : g ∈ natural
    · exact ⟨g, hn, hg⟩
    · refine ⟨g * rotation, ?_, ?_⟩
      · rw [Subgroup.mul_mem_iff_of_index_two
          GLS3.Chapter5.naturalAlternatingAutomorphismSubgroup_index]
        exact iff_of_false hn rotation_not_mem_natural
      · rw [mul_smul, hrfix, hg]
  obtain ⟨n, ⟨σ, hσ⟩, hn⟩ := hnat
  refine ⟨σ, ?_⟩
  rw [show permutationAction σ = n from hσ, he]
  exact congrArg Sylow.toSubgroup hn

end Identification
end AlternatingSix.ShadowLocal
