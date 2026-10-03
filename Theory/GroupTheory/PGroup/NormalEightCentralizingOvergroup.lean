module

public import Theory.GroupTheory.PGroup.NormalEightFour

/-!
# Central fours in normal overgroups without normal elementary eights

An elementary four central in a normal subgroup is normal if the ambient
finite group has no normal elementary subgroup of order at least eight.
Indeed it lies in the image of the central first omega of that normal
subgroup. This image is normal and elementary, so it has order four and
coincides with the given four.

This replaces the stronger elementary-rank hypothesis in
`normal_four_of_normal_centralizing_overgroup`. It is the intrinsic step
needed for the Sylow transport in Janko–Thompson, Math. Z. 113 (1970),
§6, printed p.395, under the original no-normal-eight hypothesis.
-/

namespace Subgroup

/-- A four central in a normal overgroup is normal when there are no normal
elementary eights. No bound on nonnormal elementary subgroups is required. -/
public theorem normal_four_of_normal_centralizing_overgroup_of_no_normal_eight
    {P : Type*} [Group P] [Finite P]
    (hno : ¬ ∃ A : Subgroup P, A.Normal ∧ IsElementaryAbelian 2 A ∧ 8 ≤ Nat.card A)
    (E C : Subgroup P) [IsElementaryAbelian 2 E] [C.Normal]
    (hE : Nat.card E = 4) (hEC : E ≤ C)
    (hCE : C ≤ centralizer (E : Set P)) : E.Normal := by
  let O := omega₁ (center C) (p := 2)
  let : O.Characteristic := omega₁_characteristic _
  let : IsElementaryAbelian 2 O := IsElementaryAbelian.omega₁_of_isMulCommutative _
  let Z := O.map (center C).subtype
  let : Z.Characteristic := characteristic_of_characteristic_of_characteristic
  let : IsElementaryAbelian 2 Z := IsElementaryAbelian.map_subtype
  let F := Z.map C.subtype
  let : F.Normal := ConjAct.normal_of_characteristic_of_normal
  let : IsElementaryAbelian 2 F := IsElementaryAbelian.map_subtype
  have hEF : E ≤ F := by
    intro e he
    have heC : (⟨e, hEC he⟩ : C) ∈ center C := by
      apply mem_center_iff.mpr
      intro c
      exact Subtype.ext (hCE c.property e he).symm
    refine mem_map.mpr ⟨⟨e, hEC he⟩, ?_, rfl⟩
    refine mem_map.mpr ⟨⟨⟨e, hEC he⟩, heC⟩, ?_, rfl⟩
    apply subset_closure
    apply Subtype.ext
    apply Subtype.ext
    simpa using elemPow_eq_one_of_isElementaryAbelian (p := 2) e he
  have hlt : Nat.card F < 8 := by
    by_contra! h
    exact hno ⟨F, inferInstance, inferInstance, h⟩
  have hdiv : 4 ∣ Nat.card F := hE ▸ card_dvd_of_le hEF
  have hge : 4 ≤ Nat.card F := hE ▸ card_le_of_le hEF
  have heq : E = F := eq_of_le_of_card_ge hEF (by omega)
  exact heq ▸ inferInstance

end Subgroup
