module

public import Theory.SpecificGroups.SymmetricFourSylow
public import Mathlib.GroupTheory.Perm.ViaEmbedding
public import Mathlib.GroupTheory.Perm.Fin

/-!
# The Sylow two-subgroups of S₅

Embed S₄ by fixing the fifth letter. Its dihedral subgroup of order eight
has the full two-part of 5!, so Sylow conjugacy identifies every Sylow
two-subgroup of S₅ with D₈. This is a group isomorphism, not a group-family tag.

Application: Aschbacher–Smith, proof of Lemma 16.4.7, printed p.1187.
-/

namespace Equiv.Perm

/-- Every Sylow two-subgroup of S₅ is dihedral of order eight. -/
public theorem sylow_two_equiv_dihedral_five (S : Sylow 2 (Equiv.Perm (Fin 5))) :
    Nonempty (S ≃* DihedralGroup 4) := by
  let P : Sylow 2 (Equiv.Perm (Fin 4)) := Sylow.nonempty.some
  let f : Equiv.Perm (Fin 4) →* Equiv.Perm (Fin 5) := viaEmbeddingHom Fin.castSuccEmb
  have hf : Function.Injective f := viaEmbeddingHom_injective _
  obtain ⟨e⟩ := sylow_two_equiv_dihedral_four P
  have hcard : Nat.card ((P : Subgroup (Equiv.Perm (Fin 4))).map f) = 8 := by
    rw [Subgroup.card_map_of_injective hf, Nat.card_congr e.toEquiv]
    exact DihedralGroup.nat_card
  have hfull : Nat.card (Equiv.Perm (Fin 5)) = 120 := by
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  let Q : Sylow 2 (Equiv.Perm (Fin 5)) := Sylow.ofCard
    ((P : Subgroup (Equiv.Perm (Fin 4))).map f) (by
      rw [hcard, hfull]
      rw [show 120 = 2 ^ 3 * 15 by norm_num,
        Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
        Nat.prime_two.factorization_pow, Finsupp.single_eq_same,
        Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 15)]
      rfl)
  exact ⟨(S.equiv Q).trans
    (((P : Subgroup (Equiv.Perm (Fin 4))).equivMapOfInjective f hf).symm.trans e)⟩

end Equiv.Perm
