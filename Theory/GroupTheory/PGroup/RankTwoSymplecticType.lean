module

public import Theory.GroupTheory.PGroup.BinaryHallNoNormalFour
public import Theory.GroupTheory.PGroup.BinaryHallCore
public import Theory.GroupTheory.PGroup.BinaryHallTail

/-!
# Hall's binary symplectic-type theorem

A finite two-group whose characteristic abelian subgroups are cyclic is an
internal central product of a trivial or extraspecial subgroup and a cyclic,
generalized quaternion, dihedral, or semidihedral subgroup. This proves the
rank-two specialization, with no need for the rank restriction.

The critical-subgroup theorem extracts the extraspecial factor and leaves a
cyclic self-centralizer in its commuting supplement. The residual-factor
classification excludes the modular case by producing a noncyclic
characteristic abelian subgroup of the original group.

Sources: GLS2, Chapter C, Theorem 10.3 and Propositions 10.4–10.6;
Gorenstein, *Finite Groups*, Sections 5.4–5.5, especially Theorem 5.4.9.
-/

namespace Subgroup

/-- Hall's characteristic-abelian hypothesis in particular makes the center cyclic. -/
public theorem isCyclic_center_of_characteristic_abelian
    {P : Type*} [Group P]
    (hchar : ∀ A : Subgroup P, A.Characteristic → IsMulCommutative A → IsCyclic A) :
    IsCyclic (center P) :=
  hchar (center P) inferInstance inferInstance

/-- Hall's hypothesis excludes characteristic elementary four-groups. -/
public theorem no_characteristic_four_of_characteristic_abelian
    {P : Type*} [Group P] [Finite P]
    (hchar : ∀ A : Subgroup P, A.Characteristic → IsMulCommutative A → IsCyclic A) :
    ¬ ∃ U : Subgroup P, U.Characteristic ∧ IsElementaryAbelian 2 U ∧ Nat.card U = 4 := by
  rintro ⟨U, hUc, hUe, hcard⟩
  let : IsElementaryAbelian 2 U := hUe
  exact IsElementaryAbelian.not_isCyclic_of_card_eq_prime_sq (p := 2)
    (by simpa using hcard) (hchar U hUc inferInstance)

end Subgroup

namespace IsPGroup

/-- Philip Hall's symplectic-type theorem for finite two-groups, in internal
central-product form. In particular it applies under the rank-two hypotheses. -/
public theorem isBinarySymplecticType_of_characteristic_abelian
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hchar : ∀ A : Subgroup P, A.Characteristic → IsMulCommutative A → IsCyclic A) :
    IsBinarySymplecticType P := by
  obtain ⟨E, D, Z, hcore⟩ := hP.exists_binaryHallCore hchar
  exact hcore.isBinarySymplecticType (hcore.isBinaryHallFactor hP hchar)

/-- The embedded Hall factors are normal, commute elementwise, and generate
the ambient group. The residual alternatives use actual models or the exact
semidihedral presentation recorded in `IsBinaryHallFactor`. -/
public theorem exists_normal_binaryHallFactors
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hchar : ∀ A : Subgroup P, A.Characteristic → IsMulCommutative A → IsCyclic A) :
    ∃ E D : Subgroup P, E.Normal ∧ D.Normal ∧
      (E = ⊥ ∨ IsExtraspecial 2 E) ∧ IsBinaryHallFactor D ∧
      D ≤ Subgroup.centralizer (E : Set P) ∧ E ⊔ D = ⊤ :=
  (hP.isBinarySymplecticType_of_characteristic_abelian hchar).exists_normal_factors

end IsPGroup
