module

public import Theory.GroupTheory.PGroup.CriticalSubgroupOverAbelian
public import Theory.GroupTheory.PGroup.UniqueNormalFourCritical
public import Theory.GroupTheory.PGroup.RankTwoNormalFour

/-!
# Choosing a critical subgroup whose center contains the unique normal four

A characteristic abelian subgroup can be extended to a maximal characteristic
abelian subgroup. Thompson's construction makes this overgroup the center of
a critical subgroup. In particular, the unique normal elementary four is
characteristic and can be included in the critical center. If normal elementary
eights are absent, the first omega of this center maps exactly onto that four.

This is an existence argument; it does not assert the same center size for an
arbitrary critical subgroup. No bound on nonnormal elementary subgroups is used.

Sources: Gorenstein, *Finite Groups*, Theorem 5.3.11, pp.185–186;
Janko–Thompson, Math. Z. 113 (1970), Theorem 1.3, printed p.386.
-/

open Subgroup

namespace IsPGroup

/-- Any characteristic abelian subgroup is contained in the center of some
critical subgroup. -/
public theorem exists_criticalPSubgroup_center_ge
    {p : ℕ} [Fact p.Prime] {P : Type*} [Group P] [Finite P]
    (hP : IsPGroup p P) (A : Subgroup P) [A.Characteristic] [IsMulCommutative A] :
    ∃ C : Subgroup P, IsCriticalPSubgroup p C ∧ A ≤ (center C).map C.subtype := by
  let good : Subgroup P → Prop := fun D => D.Characteristic ∧ IsMulCommutative D
  obtain ⟨D, hAD, hmax⟩ := Finite.exists_le_maximal (p := good)
    (a := A) ⟨inferInstance, inferInstance⟩
  let : D.Characteristic := hmax.1.1
  let : IsMulCommutative D := hmax.1.2
  obtain ⟨C, hC, hCD⟩ := hP.exists_criticalPSubgroup_with_center D
    (fun E hEchar hEcomm hDE => le_antisymm (hmax.2 ⟨hEchar, hEcomm⟩ hDE) hDE)
  exact ⟨C, hC, hCD.symm ▸ hAD⟩

/-- In the unique-normal-four case without normal elementary eights, one can
choose a critical subgroup whose center omega maps onto the unique four. -/
public theorem exists_criticalPSubgroup_omega_center_eq_unique_four
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup P) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hunique : ∀ F : Subgroup P, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = W) :
    ∃ C : Subgroup P, IsCriticalPSubgroup 2 C ∧
      ((omega₁ (center C) (p := 2)).map (center C).subtype).map C.subtype = W := by
  let : W.Characteristic := characteristic_of_unique_normal_four W hW hunique
  obtain ⟨C, hC, hWC⟩ := hP.exists_criticalPSubgroup_center_ge W
  let : C.Characteristic := hC.characteristic
  let O := omega₁ (center C) (p := 2)
  let : O.Characteristic := omega₁_characteristic _
  let : IsElementaryAbelian 2 O := IsElementaryAbelian.omega₁_of_isMulCommutative _
  let Z := O.map (center C).subtype
  let : IsElementaryAbelian 2 Z := IsElementaryAbelian.map_subtype
  let E := Z.map C.subtype
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map_subtype
  refine ⟨C, hC, le_antisymm
    (normal_elementary_le_unique_four hno W hW hunique E) ?_⟩
  intro w hw
  obtain ⟨c, hc, rfl⟩ := hWC hw
  refine ⟨c, ⟨⟨c, hc⟩, subset_closure ?_, rfl⟩, rfl⟩
  apply Subtype.ext
  apply Subtype.ext
  exact elemPow_eq_one_of_isElementaryAbelian _ hw

/-- A critical subgroup with center omega of order four exists under the
unique-normal-four and no-normal-eight hypotheses. -/
public theorem exists_criticalPSubgroup_card_omega_center_four
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup P) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hunique : ∀ F : Subgroup P, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = W) :
    ∃ C : Subgroup P, IsCriticalPSubgroup 2 C ∧
      Nat.card (omega₁ (center C) (p := 2)) = 4 := by
  obtain ⟨C, hC, heq⟩ :=
    hP.exists_criticalPSubgroup_omega_center_eq_unique_four hno W hW hunique
  refine ⟨C, hC, ?_⟩
  have hc := congrArg (fun E : Subgroup P => Nat.card E) heq
  simpa only [card_map_of_injective C.subtype_injective,
    card_map_of_injective (center C).subtype_injective, hW] using hc

end IsPGroup
