module

public import Theory.GroupTheory.PGroup.MultipleNormalFourSylow
public import Theory.GroupTheory.PGroup.NormalEightReduction

/-!
# Normal fours in the absence of a normal elementary eight

A normal elementary four is maximal among normal elementary subgroups when
there is no normal elementary eight. Consequently it contains central omega,
and distinct normal fours cannot commute. Their join is dihedral of order
eight and, in a two-group, generates the group together with its centralizer.

The join arguments refine `MultipleNormalFourSylow`: only normal elementary
subgroups are bounded here. No bound on arbitrary elementary subgroups is used.
The product and centralizer calculations follow that module. This is the
intrinsic part of Janko–Thompson (1970), 1.2, printed pp.385–386; the ambient
simple-group exclusion of a proper dihedral central factor remains separate.
-/

namespace Subgroup

variable {P : Type*} [Group P] [Finite P]

/-- A commuting normal elementary subgroup lies in a normal four if there is
no normal elementary eight. -/
public theorem normal_elementary_le_four_of_no_normal_eight
    (hno : ¬ ∃ A : Subgroup P, A.Normal ∧ IsElementaryAbelian 2 A ∧ 8 ≤ Nat.card A)
    (E F : Subgroup P) [E.Normal] [F.Normal]
    [IsElementaryAbelian 2 E] [IsElementaryAbelian 2 F]
    (hE : Nat.card E = 4) (hFE : F ≤ centralizer (E : Set P)) : F ≤ E := by
  let : IsElementaryAbelian 2 (E ⊔ F : Subgroup P) :=
    IsElementaryAbelian.sup_of_le_centralizer hFE
  have hlt : Nat.card (E ⊔ F : Subgroup P) < 8 := by
    by_contra! h
    exact hno ⟨E ⊔ F, inferInstance, inferInstance, h⟩
  have hdiv : 4 ∣ Nat.card (E ⊔ F : Subgroup P) := by
    rw [← hE]
    exact card_dvd_of_le le_sup_left
  have hge := card_le_of_le (le_sup_left : E ≤ E ⊔ F)
  have heq : E = E ⊔ F := eq_of_le_of_card_ge le_sup_left (by omega)
  rw [heq]
  exact le_sup_right

/-- Commuting normal fours coincide in the absence of a normal elementary eight. -/
public theorem normal_four_eq_of_le_centralizer_of_no_normal_eight
    (hno : ¬ ∃ A : Subgroup P, A.Normal ∧ IsElementaryAbelian 2 A ∧ 8 ≤ Nat.card A)
    (E F : Subgroup P) [E.Normal] [F.Normal]
    [IsElementaryAbelian 2 E] [IsElementaryAbelian 2 F]
    (hE : Nat.card E = 4) (hF : Nat.card F = 4)
    (hFE : F ≤ centralizer (E : Set P)) : F = E :=
  eq_of_le_of_card_ge
    (normal_elementary_le_four_of_no_normal_eight hno E F hE hFE) (by omega)

/-- Central omega is contained in every normal four without assuming a bound
on nonnormal elementary subgroups. -/
public theorem omega_one_center_le_normal_four_of_no_normal_eight
    (hno : ¬ ∃ A : Subgroup P, A.Normal ∧ IsElementaryAbelian 2 A ∧ 8 ≤ Nat.card A)
    (E : Subgroup P) [E.Normal] [IsElementaryAbelian 2 E] (hE : Nat.card E = 4) :
    (omega₁ (center P) (p := 2)).map (center P).subtype ≤ E := by
  let O := omega₁ (center P) (p := 2)
  let : O.Characteristic := omega₁_characteristic _
  let : IsElementaryAbelian 2 O := IsElementaryAbelian.omega₁_of_isMulCommutative _
  let Z := O.map (center P).subtype
  let : Z.Normal := ConjAct.normal_of_characteristic_of_normal
  let : IsElementaryAbelian 2 Z := IsElementaryAbelian.map_subtype
  exact normal_elementary_le_four_of_no_normal_eight hno E Z hE
    ((map_subtype_le O).trans (center_le_centralizer _))

/-- Distinct normal elementary fours intersect in order two when there is no normal elementary eight. -/
public theorem inf_card_two_of_distinct_normal_fours_of_no_normal_eight
    (hno : ¬ ∃ A : Subgroup P, A.Normal ∧ IsElementaryAbelian 2 A ∧ 8 ≤ Nat.card A)
    (E F : Subgroup P) [E.Normal] [F.Normal]
    [IsElementaryAbelian 2 E] [IsElementaryAbelian 2 F]
    (hE : Nat.card E = 4) (hF : Nat.card F = 4) (hne : E ≠ F) :
    Nat.card (E ⊓ F : Subgroup P) = 2 := by
  have hnc : ¬ E ≤ centralizer (F : Set P) := by
    intro h
    exact hne (normal_four_eq_of_le_centralizer_of_no_normal_eight hno F E hF hE h)
  have hnb : E ⊓ F ≠ ⊥ := by
    intro h
    exact hnc (commutator_eq_bot_iff_le_centralizer.mp
      (le_bot_iff.mp (h ▸ (commutator_le_inf (H₁ := E) (H₂ := F)))))
  have hdiv : Nat.card (E ⊓ F : Subgroup P) ∣ 4 := hE ▸ card_dvd_of_le inf_le_left
  have hlt : Nat.card (E ⊓ F : Subgroup P) < 4 := by
    have hle := card_le_of_le (inf_le_left : E ⊓ F ≤ E)
    have hneq : Nat.card (E ⊓ F : Subgroup P) ≠ 4 := by
      intro hc
      have heq : E ⊓ F = E := eq_of_le_of_card_ge inf_le_left (by omega)
      exact hne (eq_of_le_of_card_ge (heq ▸ inf_le_right) (by omega))
    omega
  have hpos := Nat.card_pos (α := ↥(E ⊓ F))
  have hone : Nat.card (E ⊓ F : Subgroup P) ≠ 1 := fun h => hnb (card_eq_one.mp h)
  interval_cases h : Nat.card (E ⊓ F : Subgroup P) <;> norm_num at *

/-- The join of distinct normal elementary fours is dihedral of order eight. -/
public theorem sup_dihedral_of_distinct_normal_fours_of_no_normal_eight
    (hno : ¬ ∃ A : Subgroup P, A.Normal ∧ IsElementaryAbelian 2 A ∧ 8 ≤ Nat.card A)
    (E F : Subgroup P) [E.Normal] [F.Normal]
    [IsElementaryAbelian 2 E] [IsElementaryAbelian 2 F]
    (hE : Nat.card E = 4) (hF : Nat.card F = 4) (hne : E ≠ F) :
    Nonempty (↥(E ⊔ F) ≃* DihedralGroup 4) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hi := inf_card_two_of_distinct_normal_fours_of_no_normal_eight hno E F hE hF hne
  have hh := card_mul_eq_card_inf_mul_card_sup_of_normalizes E F le_normalizer_of_normal
  have hD : Nat.card (E ⊔ F : Subgroup P) = 8 := by rw [hE, hF, hi] at hh; omega
  let : IsElementaryAbelian 2 (E.subgroupOf (E ⊔ F)) :=
    IsElementaryAbelian.subgroupOf le_sup_left
  apply dihedral_eight_of_noncentral_elementary_four hD (E.subgroupOf (E ⊔ F))
  · rwa [Nat.card_congr (subgroupOfEquivOfLe (le_sup_left : E ≤ E ⊔ F)).toEquiv]
  · intro hcentral
    apply hne
    apply normal_four_eq_of_le_centralizer_of_no_normal_eight hno F E hF hE
    intro e he f hf
    exact congrArg Subtype.val (mem_center_iff.mp
      (hcentral (show (⟨e, (le_sup_left : E ≤ E ⊔ F) he⟩ : ↥(E ⊔ F)) ∈ E.subgroupOf (E ⊔ F) from he))
      (⟨f, (le_sup_right : F ≤ E ⊔ F) hf⟩ : ↥(E ⊔ F)))

/-- In a two-group, the dihedral join and its centralizer generate the whole group. -/
public theorem sup_centralizer_eq_top_of_distinct_normal_fours_of_no_normal_eight
    (hP : IsPGroup 2 P)
    (hno : ¬ ∃ A : Subgroup P, A.Normal ∧ IsElementaryAbelian 2 A ∧ 8 ≤ Nat.card A)
    (E F : Subgroup P) [E.Normal] [F.Normal]
    [IsElementaryAbelian 2 E] [IsElementaryAbelian 2 F]
    (hE : Nat.card E = 4) (hF : Nat.card F = 4) (hne : E ≠ F) :
    (E ⊔ F) ⊔ centralizer ((E ⊔ F : Subgroup P) : Set P) = ⊤ := by
  let D := E ⊔ F
  let C := centralizer (D : Set P)
  obtain ⟨e⟩ := sup_dihedral_of_distinct_normal_fours_of_no_normal_eight hno E F hE hF hne
  have hD : Nat.card D = 8 := by
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  have hCeq : C = centralizer (E : Set P) ⊓ centralizer (F : Set P) := by
    apply le_antisymm
    · exact le_inf (centralizer_le (show (E : Set P) ⊆ (D : Set P) from (le_sup_left : E ≤ D)))
        (centralizer_le (show (F : Set P) ⊆ (D : Set P) from (le_sup_right : F ≤ D)))
    · apply le_centralizer_iff.mpr
      exact sup_le (le_centralizer_iff.mp inf_le_left) (le_centralizer_iff.mp inf_le_right)
  have hCi : C.index ≤ 4 := by
    rw [hCeq]
    have h := index_inf_le (H := centralizer (E : Set P)) (K := centralizer (F : Set P))
    have he := centralizer_index_le_two_of_normal_four hP E hE
    have hf := centralizer_index_le_two_of_normal_four hP F hF
    exact h.trans (by nlinarith)
  have hDC : Nat.card (D ⊓ C : Subgroup P) = 2 := by
    have hcenter : C.subgroupOf D = center D := by
      ext x
      simp only [mem_subgroupOf, mem_center_iff]
      constructor
      · intro h y
        exact Subtype.ext (h y y.property)
      · intro h y hy
        exact congrArg Subtype.val (h ⟨y, hy⟩)
    rw [inf_comm, ← Nat.card_congr (subgroupOfEquivOfLe (inf_le_right : C ⊓ D ≤ D)).toEquiv]
    have heq : (C ⊓ D).subgroupOf D = C.subgroupOf D := by ext x; simp
    rw [heq, hcenter, Nat.card_congr (centerCongr e).toEquiv, Nat.card_eq_fintype_card]
    decide
  have hprod := card_mul_eq_card_inf_mul_card_sup_of_normalizes D C
    (centralizer_le_normalizer (D : Set P))
  rw [hD, hDC] at hprod
  have hc := C.card_mul_index
  have hbound : Nat.card P ≤ 4 * Nat.card C := by nlinarith
  apply (D ⊔ C).eq_top_of_card_eq
  have hle := (D ⊔ C).card_le_card_group
  nlinarith
end Subgroup
