module

public import Theory.GroupTheory.PGroup.NormalEightFour
public import Theory.GroupTheory.PGroup.DihedralCentralFactor
public import Theory.GroupTheory.PGroup.BinaryHallNoNormalFour

/-!
# The centralizer of a dihedral join without a normal eight

Let two distinct normal elementary four-groups generate a dihedral subgroup
of a finite two-group with no normal elementary eight. The dihedral subgroup
and its centralizer generate the whole group. A normal four in the centralizer
would therefore be normal in the whole group. Since it commutes with either
original four, it would lie in that four and hence in the order-two intersection
of the dihedral subgroup with its centralizer, a contradiction.

Thus the centralizer has no normal four, and the Hall-factor classification
applies. This retains the dihedral and semidihedral alternatives: the stronger
classification as cyclic or quaternion requires a bound on all elementary
subgroups, which is not assumed here.

Source: the intrinsic reduction toward Janko–Thompson, Math. Z. 113 (1970),
result 1.2, printed pp.385–386. The ambient exclusions are separate.
-/

namespace Subgroup

private theorem normal_map_of_centralizer_sup_eq_top
    {P : Type*} [Group P] (D : Subgroup P)
    (hgen : D ⊔ centralizer (D : Set P) = ⊤)
    (U : Subgroup (centralizer (D : Set P))) [U.Normal] :
    (U.map (centralizer (D : Set P)).subtype).Normal := by
  let C := centralizer (D : Set P)
  let V := U.map C.subtype
  have hsub : V.subgroupOf C = U := by
    change (U.map C.subtype).comap C.subtype = U
    rw [comap_map_eq]
    simp
  let : (V.subgroupOf C).Normal := hsub.symm ▸ inferInstanceAs U.Normal
  have hCN : C ≤ normalizer (V : Set P) :=
    le_normalizer_of_normal_subgroupOf (map_subtype_le U)
  have hDC : D ≤ centralizer (C : Set P) := le_centralizer_iff.mp le_rfl
  have hDN : D ≤ normalizer (V : Set P) :=
    (hDC.trans (centralizer_le (show (V : Set P) ⊆ C from map_subtype_le U))).trans
      (centralizer_le_normalizer _)
  apply normalizer_eq_top_iff.mp
  apply top_unique
  rw [← hgen]
  exact sup_le hDN hCN

/-- A normal four cannot occur in the centralizer of the dihedral join. -/
public theorem no_normal_four_centralizer_of_distinct_normal_fours_of_no_normal_eight
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hno : ¬ ∃ A : Subgroup P, A.Normal ∧ IsElementaryAbelian 2 A ∧ 8 ≤ Nat.card A)
    (E F : Subgroup P) [E.Normal] [F.Normal]
    [IsElementaryAbelian 2 E] [IsElementaryAbelian 2 F]
    (hE : Nat.card E = 4) (hF : Nat.card F = 4) (hne : E ≠ F) :
    ¬ ∃ U : Subgroup (centralizer ((E ⊔ F : Subgroup P) : Set P)),
      U.Normal ∧ IsElementaryAbelian 2 U ∧ Nat.card U = 4 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let D := E ⊔ F
  let C := centralizer (D : Set P)
  obtain ⟨e⟩ := sup_dihedral_of_distinct_normal_fours_of_no_normal_eight hno E F hE hF hne
  have hgen := sup_centralizer_eq_top_of_distinct_normal_fours_of_no_normal_eight
    hP hno E F hE hF hne
  rintro ⟨U, hUn, hUe, hU⟩
  let : U.Normal := hUn
  let : IsElementaryAbelian 2 U := hUe
  let V := U.map C.subtype
  let : V.Normal := normal_map_of_centralizer_sup_eq_top D hgen U
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.map_subtype
  have hVC : V ≤ C := map_subtype_le U
  have hVE : V ≤ E := normal_elementary_le_four_of_no_normal_eight hno E V hE
    (hVC.trans (centralizer_le (show (E : Set P) ⊆ D from
      (show E ≤ E ⊔ F from le_sup_left))))
  have hVI : V ≤ D ⊓ C := le_inf (hVE.trans le_sup_left) hVC
  have hbound := card_le_of_le hVI
  have hV : Nat.card V = 4 := (card_map_of_injective C.subtype_injective).trans hU
  have hI := card_inf_centralizer_of_dihedral D e
  change Nat.card V ≤ Nat.card (D ⊓ centralizer (D : Set P) : Subgroup P) at hbound
  omega

/-- The correct classification under no-normal-eight retains all four Hall alternatives. -/
public theorem centralizer_isBinaryHallFactor_of_distinct_normal_fours_of_no_normal_eight
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hno : ¬ ∃ A : Subgroup P, A.Normal ∧ IsElementaryAbelian 2 A ∧ 8 ≤ Nat.card A)
    (E F : Subgroup P) [E.Normal] [F.Normal]
    [IsElementaryAbelian 2 E] [IsElementaryAbelian 2 F]
    (hE : Nat.card E = 4) (hF : Nat.card F = 4) (hne : E ≠ F) :
    IsBinaryHallFactor (centralizer ((E ⊔ F : Subgroup P) : Set P)) :=
  (hP.to_subgroup _).isBinaryHallFactor_of_no_normal_four
    (no_normal_four_centralizer_of_distinct_normal_fours_of_no_normal_eight
      hP hno E F hE hF hne)

end Subgroup
