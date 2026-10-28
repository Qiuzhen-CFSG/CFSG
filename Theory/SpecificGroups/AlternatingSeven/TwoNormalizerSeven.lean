module
public import Theory.GroupTheory.Perm.SevenPointIndexTen
public import Theory.GroupAction.PrimitiveSimplicity
public import Theory.Alternating.Aut

/-!
# Seven does not divide a nontrivial two-subgroup normalizer in Aut(A7)

A seven-divisible permutation group on seven letters is transitive and
primitive. Any nontrivial normal two-subgroup would therefore be transitive,
forcing seven to divide its two-power order. Transport through the literal
conjugation isomorphism S7 = Aut(A7) gives the same obstruction for actual
automorphism subgroups, including outer two-elements.

Source application: Aschbacher--Smith C.4.5--8, pp.152--154. The permutation
argument uses the primitive normal-orbit criterion of Wielandt, Theorem 7.1.
-/

public noncomputable section
open Subgroup MulAction
namespace AlternatingSeven

/-- A nontrivial two-subgroup of S7 has a seven-free full normalizer. -/
theorem seven_not_dvd_two_normalizer
    (P : Subgroup (Equiv.Perm (Fin 7))) (hp : IsPGroup 2 P) (hne : P ≠ ⊥) :
    ¬ 7 ∣ Nat.card (normalizer (P : Set (Equiv.Perm (Fin 7)))) := by
  intro hseven
  let N := normalizer (P : Set (Equiv.Perm (Fin 7)))
  let U := P.subgroupOf N
  let : U.Normal := normal_in_normalizer
  let : IsPretransitive N (Fin 7) :=
    Theory.GroupTheory.SevenPoint.pretransitive_of_seven_dvd N hseven
  let : IsPreprimitive N (Fin 7) := IsPreprimitive.of_prime_card (by rw [Nat.card_fin]; decide)
  have hU : U ≠ ⊥ := by
    intro hb
    have hh := congrArg (map N.subtype) hb
    rw [map_subgroupOf_eq_of_le P.le_normalizer,Subgroup.map_bot] at hh
    exact hne hh
  have hd := card_dvd_card_normal_of_quasiprimitive (X := Fin 7) U hU
  rw [Nat.card_fin,Nat.card_congr (subgroupOfEquivOfLe P.le_normalizer).toEquiv] at hd
  obtain ⟨n,hn⟩ := hp.exists_card_eq
  rw [hn] at hd
  exact (by decide : ¬ 7 ∣ 2) ((Nat.prime_seven.dvd_of_dvd_pow hd))

/-- The full automorphism normalizer retains the same seven obstruction. -/
theorem seven_not_dvd_automorphism_two_normalizer
    (P : Subgroup (MulAut (alternatingGroup (Fin 7))))
    (hp : IsPGroup 2 P) (hne : P ≠ ⊥) :
    ¬ 7 ∣ Nat.card (normalizer (P : Set (MulAut (alternatingGroup (Fin 7))))) := by
  let e : Equiv.Perm (Fin 7) ≃* MulAut (alternatingGroup (Fin 7)) :=
    MulEquiv.ofBijective MulAut.conjNormal
      (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7 (by decide) (by decide))
  let U := P.map e.symm.toMonoidHom
  have hU : U ≠ ⊥ := fun hb => hne ((P.map_eq_bot_iff_of_injective e.symm.injective).mp hb)
  have he := Nat.card_congr ((normalizer (P : Set _)).equivMapOfInjective
    e.symm.toMonoidHom e.symm.injective).toEquiv
  rw [map_normalizer_eq_of_bijective _ e.symm.bijective] at he
  rw [he]
  exact seven_not_dvd_two_normalizer U (hp.map _) hU

end AlternatingSeven
