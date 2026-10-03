module

public import Theory.GroupTheory.PGroup.NormalEightAbelianReduction
public import Theory.GroupTheory.PGroup.NormalEightHomocyclicAction
public import Theory.GroupTheory.PGroup.NormalEightUnequalAction

/-!+# Elementary order from the normal abelian action bound

The absence of normal elementary eights bounds the first omega subgroup of
a normal abelian subgroup by four. For a self-centralizing such subgroup,
an elementary subgroup's action kernel embeds in that omega subgroup.
Consequently an action image of order at most four gives order at most sixteen.

This is the cardinality assembly for the elementary consequence of the
MacWilliams–Sah four-generator theorem, Janko–Thompson, Math. Z. 113 (1970),
1.1, printed p.385. The structural action-image bound is an explicit premise
here and must be discharged to obtain the unconditional consequence.
-/

namespace IsPGroup

/-- The normal abelian action-image bound implies the elementary order bound. -/
public theorem elementary_card_le_sixteen_of_no_normal_eight_of_conj_image_le_four
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (D : Subgroup P) [D.Normal] [IsMulCommutative D]
    (hD : Subgroup.centralizer (D : Set P) ≤ D)
    (A : Subgroup P) [IsElementaryAbelian 2 A]
    (himage : Nat.card ((MulAut.conjNormal : P →* MulAut D).comp A.subtype).range ≤ 4) :
    Nat.card A ≤ 16 := by
  have hkernel := hP.card_omega_one_normal_abelian_le_four_of_no_normal_eight hno D
  have hcard := Subgroup.card_le_omega_one_mul_conj_image_of_elementary D hD A
  exact hcard.trans (by simpa using Nat.mul_le_mul hkernel himage)

/-- The central-omega-four case of the MacWilliams--Sah elementary order bound. -/
public theorem elementary_card_le_sixteen_of_no_normal_eight_of_center_four
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (hZ : Nat.card (omega₁ (Subgroup.center P) (p := 2)) = 4) :
    ∀ A : Subgroup P, IsElementaryAbelian 2 A → Nat.card A ≤ 16 := by
  obtain ⟨D, hDn, hDa, hD, -, ⟨n, m, hn, hm, ⟨e⟩⟩⟩ :=
    hP.exists_normal_abelian_two_cyclic_factors_of_no_normal_eight_of_center_four hno hZ
  let : D.Normal := hDn
  let : IsMulCommutative D := hDa
  intro A hA
  let : IsElementaryAbelian 2 A := hA
  by_cases hnm : n = m
  · subst m
    apply elementary_card_le_sixteen_of_no_normal_eight_of_conj_image_le_four
      hP hno D hD A
    exact conj_image_card_le_four_of_homocyclic_factors_of_no_normal_eight
      hP hno hZ D hD n hn e A
  · apply elementary_card_le_sixteen_of_no_normal_eight_of_conj_image_le_four
      hP hno D hD A
    exact card_conj_image_le_four_of_unequal_factors
      hP hno hZ D hD n m hn hm hnm e A

end IsPGroup
