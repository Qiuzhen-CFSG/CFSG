module

public import Theory.GroupTheory.PGroup.RankTwoNormalFour
public import Theory.GroupTheory.PGroup.DihedralCentralFactorSylow
public import Theory.GroupTheory.SpecificGroups.DihedralEightRecognition
public import Theory.GroupTheory.NormalizedSupCard
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Sylow two-subgroups with distinct normal four-groups

Two distinct normal elementary four-groups in a finite group of elementary
binary rank at most two intersect in order two and generate a dihedral group
of order eight. If the ambient group is a two-group, it is the product of this
dihedral subgroup and its centralizer.
If it is a Sylow subgroup of a finite simple group, the ambient central-factor
exclusion shows that the whole Sylow subgroup is dihedral of order eight.

The intersection is nontrivial because a trivial intersection would force the
normal factors to commute, contradicting the rank bound. The product-order
formula and noncentral-four recognition identify their join. Each four-group
has centralizer of index at most two, so the centralizer of the join has index
at most four. Its intersection with the join is the dihedral center of order
two; the product-order formula then proves generation of the whole group.

This proves the multiple-normal-four case of MacWilliams's theorem quoted in
Janko–Thompson, Math. Z. 113 (1970), 1.2, printed pp.385–386,
`refs/original/n-group-global/odd-core-rank-two-source/janko-thompson-1970-gdz.pdf`.
The ambient simple-group exclusion of a proper dihedral central factor is
provided by `DihedralCentralFactorSylow`; simplicity is essential to this step.
-/

open Subgroup
namespace Subgroup
variable {P : Type*} [Group P] [Finite P]

/-- Distinct normal elementary fours intersect in order two under the rank bound. -/
public theorem inf_card_two_of_distinct_normal_fours
    (hrank : ∀ A : Subgroup P, IsElementaryAbelian 2 A → Nat.card A < 8)
    (E F : Subgroup P) [E.Normal] [F.Normal]
    [IsElementaryAbelian 2 E] [IsElementaryAbelian 2 F]
    (hE : Nat.card E = 4) (hF : Nat.card F = 4) (hne : E ≠ F) :
    Nat.card (E ⊓ F : Subgroup P) = 2 := by
  have hnc : ¬ E ≤ centralizer (F : Set P) := by
    intro h
    exact hne (four_eq_of_le_centralizer_of_elementary_card_lt_eight hrank F E hF hE h)
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
public theorem sup_dihedral_of_distinct_normal_fours
    (hrank : ∀ A : Subgroup P, IsElementaryAbelian 2 A → Nat.card A < 8)
    (E F : Subgroup P) [E.Normal] [F.Normal]
    [IsElementaryAbelian 2 E] [IsElementaryAbelian 2 F]
    (hE : Nat.card E = 4) (hF : Nat.card F = 4) (hne : E ≠ F) :
    Nonempty (↥(E ⊔ F) ≃* DihedralGroup 4) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hi := inf_card_two_of_distinct_normal_fours hrank E F hE hF hne
  have hh := card_mul_eq_card_inf_mul_card_sup_of_normalizes E F le_normalizer_of_normal
  have hD : Nat.card (E ⊔ F : Subgroup P) = 8 := by rw [hE, hF, hi] at hh; omega
  let : IsElementaryAbelian 2 (E.subgroupOf (E ⊔ F)) :=
    IsElementaryAbelian.subgroupOf le_sup_left
  apply dihedral_eight_of_noncentral_elementary_four hD (E.subgroupOf (E ⊔ F))
  · rwa [Nat.card_congr (subgroupOfEquivOfLe (le_sup_left : E ≤ E ⊔ F)).toEquiv]
  · intro hcentral
    apply hne
    apply four_eq_of_le_centralizer_of_elementary_card_lt_eight hrank F E hF hE
    intro e he f hf
    exact congrArg Subtype.val (mem_center_iff.mp
      (hcentral (show (⟨e, (le_sup_left : E ≤ E ⊔ F) he⟩ : ↥(E ⊔ F)) ∈ E.subgroupOf (E ⊔ F) from he))
      (⟨f, (le_sup_right : F ≤ E ⊔ F) hf⟩ : ↥(E ⊔ F)))

/-- In a two-group, the dihedral join and its centralizer generate the whole group. -/
public theorem sup_centralizer_eq_top_of_distinct_normal_fours
    (hP : IsPGroup 2 P)
    (hrank : ∀ A : Subgroup P, IsElementaryAbelian 2 A → Nat.card A < 8)
    (E F : Subgroup P) [E.Normal] [F.Normal]
    [IsElementaryAbelian 2 E] [IsElementaryAbelian 2 F]
    (hE : Nat.card E = 4) (hF : Nat.card F = 4) (hne : E ≠ F) :
    (E ⊔ F) ⊔ centralizer ((E ⊔ F : Subgroup P) : Set P) = ⊤ := by
  let D := E ⊔ F
  let C := centralizer (D : Set P)
  obtain ⟨e⟩ := sup_dihedral_of_distinct_normal_fours hrank E F hE hF hne
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

namespace Sylow

/-- Distinct normal fours in a Sylow two-subgroup produce a normal dihedral
central factor. Ambient simplicity is not needed for this local reduction. -/
public theorem exists_dihedral_factor_of_distinct_normal_fours
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    (hrank : ∀ A : Subgroup G, IsElementaryAbelian 2 A → Nat.card A < 8)
    (E F : Subgroup S) [E.Normal] [F.Normal]
    [IsElementaryAbelian 2 E] [IsElementaryAbelian 2 F]
    (hE : Nat.card E = 4) (hF : Nat.card F = 4) (hne : E ≠ F) :
    ∃ D : Subgroup S, D.Normal ∧ Nonempty (D ≃* DihedralGroup 4) ∧
      D ⊔ centralizer (D : Set S) = ⊤ := by
  have hlocal := elementary_card_lt_eight_of_subgroup hrank (S : Subgroup G)
  exact ⟨E ⊔ F, inferInstance,
    sup_dihedral_of_distinct_normal_fours hlocal E F hE hF hne,
    sup_centralizer_eq_top_of_distinct_normal_fours S.isPGroup' hlocal E F hE hF hne⟩

/-- In a finite simple group, a Sylow two-subgroup of elementary rank at most
two with distinct normal elementary fours is dihedral of order eight. -/
public theorem dihedral_of_distinct_normal_fours_of_sylow_rank
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G] (S : Sylow 2 G)
    (hrank : ∀ A : Subgroup S, IsElementaryAbelian 2 A → Nat.card A < 8)
    (E F : Subgroup S) [E.Normal] [F.Normal]
    [IsElementaryAbelian 2 E] [IsElementaryAbelian 2 F]
    (hE : Nat.card E = 4) (hF : Nat.card F = 4) (hne : E ≠ F) :
    Nonempty (S ≃* DihedralGroup 4) := by
  obtain ⟨e⟩ := sup_dihedral_of_distinct_normal_fours hrank E F hE hF hne
  have htop : E ⊔ F = ⊤ := S.dihedral_central_factor_eq_top_of_sylow_rank
    hrank (E ⊔ F) ⟨e⟩
    (sup_centralizer_eq_top_of_distinct_normal_fours S.isPGroup' hrank E F hE hF hne)
  exact ⟨Subgroup.topEquiv.symm.trans ((MulEquiv.subgroupCongr htop.symm).trans e)⟩

/-- MacWilliams's multiple-normal-four theorem under the ambient elementary
rank bound, as used in Janko–Thompson (1970), 1.2. -/
public theorem dihedral_of_distinct_normal_fours
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G] (S : Sylow 2 G)
    (hrank : ∀ A : Subgroup G, IsElementaryAbelian 2 A → Nat.card A < 8)
    (E F : Subgroup S) [E.Normal] [F.Normal]
    [IsElementaryAbelian 2 E] [IsElementaryAbelian 2 F]
    (hE : Nat.card E = 4) (hF : Nat.card F = 4) (hne : E ≠ F) :
    Nonempty (S ≃* DihedralGroup 4) :=
  S.dihedral_of_distinct_normal_fours_of_sylow_rank
    (elementary_card_lt_eight_of_subgroup hrank (S : Subgroup G)) E F hE hF hne

end Sylow
