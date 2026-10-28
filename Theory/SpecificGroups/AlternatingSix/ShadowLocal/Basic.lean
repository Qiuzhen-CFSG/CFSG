module

public import Theory.Alternating.theorem_5_2_1_2
public import Theory.GroupTheory.SylowNormalIntersection

/-!
# The actual automorphism carrier and Sylow orders for A₆

The permutation action embeds S₆ in Aut(A₆), and the inner action embeds
A₆ as a normal subgroup. The proved index-two theorem for the natural S₆
then gives |Aut(A₆)| = 1440. Sylow arithmetic gives |P| = 32 and
|P ∩ Inn(A₆)| = 8, with quotient of order four.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
combined 1 March 2004 manuscript, printed pp.567–570. This module proves
these orders; the dihedral and elementary-abelian identifications and the
finer local geometry require additional results.
-/

@[expose] public section

open Subgroup

namespace AlternatingSix.ShadowLocal

abbrev A6 := alternatingGroup (Fin 6)
abbrev AutA6 := MulAut A6

def permutationAction : Equiv.Perm (Fin 6) →* AutA6 := MulAut.conjNormal

abbrev natural : Subgroup AutA6 :=
  GLS3.Chapter5.naturalAlternatingAutomorphismSubgroup

def inner : Subgroup AutA6 := (MulAut.conj : A6 →* AutA6).range

theorem permutationAction_injective : Function.Injective permutationAction :=
  GLS3.Chapter5.alternatingConjHom_injective (by norm_num)

theorem permutationAction_coe (g : A6) :
    permutationAction (g : Equiv.Perm (Fin 6)) = MulAut.conj g :=
  MulAut.conjNormal_val

theorem inner_injective : Function.Injective (MulAut.conj : A6 →* AutA6) := by
  intro a b hab
  apply Subtype.ext
  apply permutationAction_injective
  simpa only [permutationAction_coe] using hab

noncomputable def innerEquiv : A6 ≃* inner :=
  MonoidHom.ofInjective inner_injective

theorem inner_le_natural : inner ≤ natural := by
  rintro _ ⟨a, rfl⟩
  exact ⟨(a : Equiv.Perm (Fin 6)), permutationAction_coe a⟩

instance inner_normal : inner.Normal where
  conj_mem := by
    rintro _ ⟨a, rfl⟩ b
    refine ⟨b a, ?_⟩
    ext x
    simp

theorem card_A6 : Nat.card A6 = 360 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  norm_num [Nat.factorial]

theorem card_inner : Nat.card inner = 360 := by
  rw [← Nat.card_congr innerEquiv.toEquiv, card_A6]

theorem card_natural : Nat.card natural = 720 := by
  rw [← Nat.card_congr
    GLS3.Chapter5.permSixMulEquivNaturalAlternatingAutomorphisms.toEquiv]
  norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]

theorem card_aut : Nat.card AutA6 = 1440 := by
  have h := natural.card_mul_index
  rw [card_natural, GLS3.Chapter5.naturalAlternatingAutomorphismSubgroup_index] at h
  exact h.symm

theorem inner_index : inner.index = 4 := by
  have h := inner.card_mul_index
  rw [card_inner, card_aut] at h
  omega

theorem sylow_card (P : Sylow 2 AutA6) : Nat.card P = 32 := by
  rw [P.card_eq_multiplicity, card_aut]
  rw [show 1440 = 2 ^ 5 * 45 by decide,
    Nat.factorization_mul (by decide) (by decide), Finsupp.add_apply,
    Nat.prime_two.factorization_pow, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 45)]
  rfl

def sylowInner (P : Sylow 2 AutA6) : Subgroup P :=
  inner.comap (P : Subgroup AutA6).subtype

instance sylowInner_normal (P : Sylow 2 AutA6) : (sylowInner P).Normal :=
  inferInstanceAs (inner.comap (P : Subgroup AutA6).subtype).Normal

private def intersectionSwap (P : Sylow 2 AutA6) :
    sylowInner P ≃* (P : Subgroup AutA6).subgroupOf inner where
  toFun x := ⟨⟨x.1.1, x.2⟩, x.1.2⟩
  invFun x := ⟨⟨x.1.1, x.2⟩, x.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem sylowInner_card (P : Sylow 2 AutA6) : Nat.card (sylowInner P) = 8 := by
  obtain ⟨D, hD⟩ := P.exists_subgroupOf_eq_of_normal inner
  rw [Nat.card_congr (intersectionSwap P).toEquiv, ← hD]
  rw [D.card_eq_multiplicity, card_inner]
  rw [show 360 = 2 ^ 3 * 45 by decide,
    Nat.factorization_mul (by decide) (by decide), Finsupp.add_apply,
    Nat.prime_two.factorization_pow, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 45)]
  rfl

theorem sylowInner_index (P : Sylow 2 AutA6) : (sylowInner P).index = 4 := by
  have h := (sylowInner P).card_mul_index
  rw [sylowInner_card, sylow_card] at h
  omega

theorem sylowInner_quotient_card (P : Sylow 2 AutA6) :
    Nat.card (P ⧸ sylowInner P) = 4 := sylowInner_index P

end AlternatingSix.ShadowLocal
