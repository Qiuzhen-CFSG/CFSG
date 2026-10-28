module
public import Theory.GroupTheory.PGroup.ExtraspecialThirtyTwoQuaternion
import all Theory.GroupTheory.PGroup.ExtraspecialThirtyTwoQuaternion

/-!
# Retaining an elementary subgroup under dihedral splitting

A noncentral element of a center-containing elementary subgroup lies in a
dihedral central factor. The centralizer is again extraspecial when the
ambient order exceeds eight. The elementary subgroup meets this centralizer
in at least half its order: its join with the centralizer centralizes the
chosen noncentral involution, hence is proper, and the product-order formula
provides the bound. This argument avoids an assumed quadratic-space type.

The `import all` is an intentional internal companion dependency on the
marked dihedral splitting construction in `ExtraspecialThirtyTwoQuaternion`;
its private helpers remain private. No shared foundation is changed.
Source: the elementary-subgroup recognition used in Aschbacher–Smith
15.3.58(2), printed pp.1148–1149.
-/

open Subgroup
namespace DihedralCentralProductThree

private theorem elementary_restrict {P : Type*} [Group P]
    (A C : Subgroup P) [IsElementaryAbelian 2 A] :
    IsElementaryAbelian 2 (A.subgroupOf C) := by
  refine {
    toIsMulCommutative := Subgroup.subgroupOf_isMulCommutative C A
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_ }
  intro x
  apply Subtype.ext
  apply Subtype.ext
  exact elemPow_eq_one_of_isElementaryAbelian (p := 2) _ x.property

/-- Splitting off a dihedral factor retains at least half of a given elementary subgroup. -/
public theorem exists_dihedral_split
    {P : Type*} [Group P] [Finite P] [IsExtraspecial 2 P]
    (A : Subgroup P) [IsElementaryAbelian 2 A]
    (hZA : center P ≤ A) (hA : 2 < Nat.card A) (hP : 8 < Nat.card P) :
    ∃ D : Subgroup P, Nonempty (D ≃* DihedralGroup 4) ∧
      D ⊔ centralizer (D : Set P) = ⊤ ∧
      IsExtraspecial 2 (centralizer (D : Set P)) ∧
      IsElementaryAbelian 2 (A.subgroupOf (centralizer (D : Set P))) ∧
      center (centralizer (D : Set P)) ≤ A.subgroupOf (centralizer (D : Set P)) ∧
      Nat.card P = 4 * Nat.card (centralizer (D : Set P)) ∧
      Nat.card A ≤ 2 * Nat.card (A.subgroupOf (centralizer (D : Set P))) := by
  have hnot : ¬ A ≤ center P := by
    intro h
    have hc := card_le_of_le h
    rw [IsExtraspecial.center_order_p 2 P] at hc
    omega
  obtain ⟨t, htA, htZ⟩ := SetLike.not_le_iff_exists.mp hnot
  obtain ⟨D, ⟨eD⟩, _, hgen, htD⟩ :=
    exists_dihedral_factor_of_noncentral_involution_mem t
      (elemPow_eq_one_of_isElementaryAbelian (p := 2) t htA) htZ
  let C := centralizer (D : Set P)
  have hcard : Nat.card P = 4 * Nat.card C :=
    card_eq_four_mul_card_centralizer_of_dihedral_factor D eD hgen
  have hcenterC_to_P : ∀ x : C, x ∈ center C → (x : P) ∈ center P := by
    intro x hx
    apply mem_center_iff.mpr
    intro g
    have hle : D ⊔ C ≤ centralizer ({(x : P)} : Set P) := by
      apply sup_le
      · intro d hd
        exact mem_centralizer_singleton_iff.mpr (x.property d hd)
      · intro d hd
        exact mem_centralizer_singleton_iff.mpr
          (congrArg Subtype.val (mem_center_iff.mp hx ⟨d, hd⟩))
    rw [hgen] at hle
    exact mem_centralizer_singleton_iff.mp (hle (mem_top g))
  have hcenterC : (center C).map C.subtype = center P := by
    apply le_antisymm
    · rintro x ⟨y, hy, rfl⟩
      exact hcenterC_to_P y hy
    · intro x hx
      refine ⟨⟨x, center_le_centralizer _ hx⟩, ?_, rfl⟩
      exact mem_center_iff.mpr (fun y => Subtype.ext (mem_center_iff.mp hx y))
  have hZCcard : Nat.card (center C) = 2 := by
    rw [← card_map_of_injective C.subtype_injective, hcenterC,
      IsExtraspecial.center_order_p 2 P]
  have hCextra : IsExtraspecial 2 C := {
    center_order_p := hZCcard
    quotient_elementary_abelian :=
      (IsExtraspecial.quotient_elementary_abelian 2 P).central_quotient_subgroup C
    quotient_nontrivial := QuotientGroup.nontrivial_iff.mpr (by
      intro h
      have hh : Nat.card (center C) = Nat.card C := by
        rw [h, Nat.card_congr topEquiv.toEquiv]
      omega) }
  refine ⟨D, ⟨eD⟩, hgen, hCextra, elementary_restrict A C,
    (fun x hx => hZA (hcenterC_to_P x hx)), hcard, ?_⟩
  let : A.Normal := normalizer_eq_top_iff.mp (top_unique (by
    apply le_normalizer_iff_commutator_le_right.mpr
    exact (commutator_mono le_rfl le_top).trans
      ((IsExtraspecial.quotient_elementary_abelian 2 P).commutator_le_center_of_central_quotient.trans hZA)))
  have hproper : A ⊔ C ≠ ⊤ := by
    intro he
    have hle : A ⊔ C ≤ centralizer ({t} : Set P) := by
      apply sup_le
      · intro a ha
        exact mem_centralizer_singleton_iff.mpr
          (congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : A) ⟨t, htA⟩))
      · intro c hc
        exact mem_centralizer_singleton_iff.mpr (hc t htD).symm
    rw [he] at hle
    exact htZ (mem_center_iff.mpr (fun g =>
      mem_centralizer_singleton_iff.mp (hle (mem_top g))))
  have hi := (A ⊔ C).one_lt_index_of_ne_top hproper
  have hiCard := (A ⊔ C).card_mul_index
  have hprod := card_mul_eq_card_inf_mul_card_sup_of_normalizes A C
    (by rw [A.normalizer_eq_top]; exact le_top)
  have hhalf : 2 * Nat.card (A ⊔ C : Subgroup P) ≤ Nat.card P := by
    nlinarith [Nat.mul_le_mul_left (Nat.card (A ⊔ C : Subgroup P)) hi]
  have hI : Nat.card (A.subgroupOf C) = Nat.card (A ⊓ C : Subgroup P) := by
    rw [← inf_subgroupOf_right A C,
      Nat.card_congr (subgroupOfEquivOfLe (inf_le_right : A ⊓ C ≤ C)).toEquiv]
  change Nat.card A ≤ 2 * Nat.card (A.subgroupOf C)
  rw [hI]
  have hCpos : 0 < Nat.card C := Nat.card_pos
  nlinarith [Nat.mul_le_mul_left (Nat.card (A ⊓ C : Subgroup P)) hhalf]

/-- An extraspecial group of order eight with an elementary four is dihedral. -/
public theorem dihedral_of_elementary_four
    {P : Type*} [Group P] [Finite P] [IsExtraspecial 2 P]
    (hP : Nat.card P = 8) (A : Subgroup P) [IsElementaryAbelian 2 A]
    (hA : Nat.card A = 4) : Nonempty (P ≃* DihedralGroup 4) := by
  have hnot : ¬ A ≤ center P := by
    intro h
    have hc := card_le_of_le h
    rw [hA, IsExtraspecial.center_order_p 2 P] at hc
    omega
  obtain ⟨t, htA, htZ⟩ := SetLike.not_le_iff_exists.mp hnot
  obtain ⟨D, ⟨eD⟩, _, _⟩ :=
    IsExtraspecial.exists_dihedral_factor_of_noncentral_involution t
      (elemPow_eq_one_of_isElementaryAbelian (p := 2) t htA) htZ
  have hD : D = ⊤ := D.eq_top_of_card_eq (by
    rw [Nat.card_congr eD.toEquiv, DihedralGroup.nat_card, hP])
  subst D
  exact ⟨topEquiv.symm.trans eD⟩

end DihedralCentralProductThree
