module

public import Theory.GroupTheory.PGroup.CriticalSubgroup
public import Theory.GroupTheory.PGroup.CentralInvolutionRoots

/-!
# A maximal characteristic abelian center

If the center of a finite p-group is maximal among characteristic abelian
subgroups, the group has class at most two. Indeed, the center of a critical
subgroup is characteristic and abelian and contains the ambient center, so
maximality identifies the two. The three-subgroups lemma then puts the
ambient derived subgroup in that center. For a two-group with elementary
center, every fourth power is consequently trivial.

Source: the critical-subgroup argument in Gorenstein, *Finite Groups*,
Theorem 5.3.11, pp.185–186, and the three-subgroups lemma.
-/

open Subgroup

namespace IsPGroup

/-- A maximal characteristic abelian center contains the derived subgroup. -/
public theorem commutator_le_center_of_maximal_characteristic_abelian_center
    {p : ℕ} [Fact p.Prime] {P : Type*} [Group P] [Finite P]
    (hP : IsPGroup p P)
    (hmax : ∀ A : Subgroup P, A.Characteristic → IsMulCommutative A →
      center P ≤ A → A = center P) :
    commutator P ≤ center P := by
  obtain ⟨K, hK⟩ := hP.exists_criticalPSubgroup
  let : K.Characteristic := hK.characteristic
  let Z := (center K).map K.subtype
  have hCZ : center P ≤ Z := by
    rw [show Z = centralizer (K : Set P) from hK.centralizer_eq.symm]
    exact center_le_centralizer _
  have hZ : Z = center P := hmax Z inferInstance inferInstance hCZ
  have hrotate : ⁅⁅(⊤ : Subgroup P), K⁆, ⊤⁆ = ⊥ :=
    commutator_top_right_eq_bot_iff_le_center.mpr
      (hK.commutator_le.trans hZ.le)
  have hcomm : ⁅⁅(⊤ : Subgroup P), ⊤⁆, K⁆ = ⊥ :=
    commutator_commutator_eq_bot_of_rotate hrotate (by
      rwa [commutator_comm K ⊤])
  have hh : commutator P ≤ centralizer (K : Set P) :=
    commutator_eq_bot_iff_le_centralizer.mp hcomm
  rw [hK.centralizer_eq] at hh
  exact hh.trans hZ.le

/-- An elementary center that is maximal characteristic abelian forces
exponent at most four. -/
public theorem exponent_four_of_maximal_characteristic_abelian_center
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    [IsElementaryAbelian 2 (center P)]
    (hmax : ∀ A : Subgroup P, A.Characteristic → IsMulCommutative A →
      center P ≤ A → A = center P) :
    ∀ x : P, x ^ 4 = 1 := by
  apply exponent_four_of_class_two_of_center_exponent_two
    (hP.commutator_le_center_of_maximal_characteristic_abelian_center hmax)
  intro z hz
  exact elemPow_eq_one_of_isElementaryAbelian z hz

end IsPGroup
