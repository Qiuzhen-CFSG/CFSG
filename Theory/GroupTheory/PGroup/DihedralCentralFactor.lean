module

public import Theory.GroupTheory.PGroup.RankTwoExtraspecial
public import Theory.GroupTheory.PGroup.UniqueInvolutionClassification

/-!
# The centralizer of a dihedral central factor

In a finite two-group of elementary rank at most two, the centralizer of an
embedded dihedral group of order eight is cyclic or generalized quaternion.
A reflection is an involution outside this centralizer commuting with it;
an elementary four in the centralizer would therefore give an elementary eight.

When the dihedral subgroup and its centralizer generate the group, their
intersection has order two, and the ambient order is four times the
centralizer order. The cyclic centralizer is exactly the ambient center.
Thus a proper dihedral central factor leaves either a cyclic center of order
greater than two or a generalized quaternion centralizer.

These are intrinsic reductions for MacWilliams's result cited in
Janko–Thompson, Math. Z. 113 (1970), 1.2, pp.385–386 and reference [12], p.397.
They do not assert the ambient simple-group exclusion of either alternative.
-/

namespace Subgroup

open Subgroup

/-- A dihedral reflection excludes elementary fours in its centralizer. -/
public theorem no_elementary_four_centralizer_of_dihedral
    {P : Type*} [Group P] [Finite P]
    (hrank : ∀ E : Subgroup P, IsElementaryAbelian 2 E → Nat.card E < 8)
    (D : Subgroup P) (e : D ≃* DihedralGroup 4) :
    ∀ E : Subgroup (centralizer (D : Set P)),
      IsElementaryAbelian 2 E → Nat.card E ≠ 4 := by
  let C := centralizer (D : Set P)
  let t : D := e.symm (DihedralGroup.sr 0)
  have ht : (t : P) ^ 2 = 1 := by
    have h : t ^ 2 = 1 := by
      apply e.injective
      simp only [map_pow, map_one, t, e.apply_symm_apply]
      decide
    exact congrArg Subtype.val h
  have htout : (t : P) ∉ C := by
    intro h
    have heq : (e.symm (DihedralGroup.r 1)) * t = t * (e.symm (DihedralGroup.r 1)) :=
      Subtype.ext (h _ (e.symm (DihedralGroup.r 1)).property)
    have hm := congrArg e heq
    simp only [map_mul, e.apply_symm_apply, t] at hm
    exact (by decide : (DihedralGroup.r 1 : DihedralGroup 4) * DihedralGroup.sr 0 ≠
      DihedralGroup.sr 0 * DihedralGroup.r 1) hm
  have hDC : D ≤ centralizer (C : Set P) := le_centralizer_iff.mp le_rfl
  exact no_elementary_four_of_external_involution hrank C t ht htout (hDC t.property)

/-- The rank-one classification applies to the centralizer of a dihedral subgroup. -/
public theorem centralizer_cyclic_or_quaternion_of_dihedral
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hrank : ∀ E : Subgroup P, IsElementaryAbelian 2 E → Nat.card E < 8)
    (D : Subgroup P) (e : D ≃* DihedralGroup 4) :
    IsCyclic (centralizer (D : Set P)) ∨
      ∃ n : ℕ, 3 ≤ n ∧
        Nonempty (centralizer (D : Set P) ≃* QuaternionGroup (2 ^ (n - 2))) :=
  (hP.to_subgroup _).isCyclic_or_quaternion_of_no_elementary_four
    (no_elementary_four_centralizer_of_dihedral hrank D e)

/-- The intersection with the centralizer is the order-two dihedral center. -/
public theorem card_inf_centralizer_of_dihedral
    {P : Type*} [Group P] [Finite P]
    (D : Subgroup P) (e : D ≃* DihedralGroup 4) :
    Nat.card (D ⊓ centralizer (D : Set P) : Subgroup P) = 2 := by
  let C := centralizer (D : Set P)
  have hcenter : C.subgroupOf D = center D := by
    ext x
    simp only [mem_subgroupOf, mem_center_iff]
    constructor
    · intro h y
      exact Subtype.ext (h y y.property)
    · intro h y hy
      exact congrArg Subtype.val (h ⟨y, hy⟩)
  change Nat.card (D ⊓ C : Subgroup P) = 2
  rw [inf_comm, ← Nat.card_congr (subgroupOfEquivOfLe (inf_le_right : C ⊓ D ≤ D)).toEquiv]
  have heq : (C ⊓ D).subgroupOf D = C.subgroupOf D := by ext x; simp
  rw [heq, hcenter, Nat.card_congr (centerCongr e).toEquiv, Nat.card_eq_fintype_card]
  decide

/-- A dihedral central factor gives the ambient order from its centralizer order. -/
public theorem card_eq_four_mul_card_centralizer_of_dihedral_factor
    {P : Type*} [Group P] [Finite P]
    (D : Subgroup P) (e : D ≃* DihedralGroup 4)
    (hgen : D ⊔ centralizer (D : Set P) = ⊤) :
    Nat.card P = 4 * Nat.card (centralizer (D : Set P)) := by
  have hD : Nat.card D = 8 := by
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  have hprod := card_mul_eq_card_inf_mul_card_sup_of_normalizes D
    (centralizer (D : Set P)) (centralizer_le_normalizer (D : Set P))
  rw [hD, card_inf_centralizer_of_dihedral D e, hgen,
    Nat.card_congr Subgroup.topEquiv.toEquiv] at hprod
  omega

/-- The dihedral factor is the whole group exactly when its centralizer has order two. -/
public theorem dihedral_factor_eq_top_iff_card_centralizer
    {P : Type*} [Group P] [Finite P]
    (D : Subgroup P) (e : D ≃* DihedralGroup 4)
    (hgen : D ⊔ centralizer (D : Set P) = ⊤) :
    D = ⊤ ↔ Nat.card (centralizer (D : Set P)) = 2 := by
  have hcard := card_eq_four_mul_card_centralizer_of_dihedral_factor D e hgen
  have hD : Nat.card D = 8 := by
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  constructor
  · intro htop
    rw [htop, Nat.card_congr Subgroup.topEquiv.toEquiv] at hD
    omega
  · intro hC
    apply D.eq_top_of_card_eq
    omega

/-- An abelian centralizer supplement is precisely the ambient center. -/
public theorem centralizer_eq_center_of_dihedral_factor_of_isCyclic
    {P : Type*} [Group P]
    (D : Subgroup P) (hgen : D ⊔ centralizer (D : Set P) = ⊤)
    [IsCyclic (centralizer (D : Set P))] :
    centralizer (D : Set P) = center P := by
  let C := centralizer (D : Set P)
  apply le_antisymm ?_ (center_le_centralizer _)
  have hDC : D ≤ centralizer (C : Set P) := le_centralizer_iff.mp le_rfl
  have hh : (⊤ : Subgroup P) ≤ centralizer (C : Set P) := by
    rw [← hgen]
    exact sup_le hDC (le_centralizer C)
  simpa only [coe_top, centralizer_univ] using (le_centralizer_iff.mp hh)

/-- The two possible proper centralizers of a dihedral central factor. -/
public theorem proper_dihedral_factor_centralizer_cases
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hrank : ∀ E : Subgroup P, IsElementaryAbelian 2 E → Nat.card E < 8)
    (D : Subgroup P) (e : D ≃* DihedralGroup 4)
    (hgen : D ⊔ centralizer (D : Set P) = ⊤) (hproper : D ≠ ⊤) :
    (IsCyclic (centralizer (D : Set P)) ∧
      centralizer (D : Set P) = center P ∧ 2 < Nat.card (center P)) ∨
      ∃ n : ℕ, 3 ≤ n ∧
        Nonempty (centralizer (D : Set P) ≃* QuaternionGroup (2 ^ (n - 2))) := by
  rcases centralizer_cyclic_or_quaternion_of_dihedral hP hrank D e with hcyc | hquat
  · let : IsCyclic (centralizer (D : Set P)) := hcyc
    have hcenter := centralizer_eq_center_of_dihedral_factor_of_isCyclic D hgen
    refine Or.inl ⟨hcyc, hcenter, ?_⟩
    have hbound := card_le_of_le (inf_le_right :
      D ⊓ centralizer (D : Set P) ≤ centralizer (D : Set P))
    rw [card_inf_centralizer_of_dihedral D e] at hbound
    have hne := (dihedral_factor_eq_top_iff_card_centralizer D e hgen).not.mp hproper
    rw [hcenter] at hbound hne
    omega
  · exact Or.inr hquat

end Subgroup
