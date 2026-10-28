module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.PrimeGeometry.Inner.SymmetricNormalizers.Recognition
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.PrimeGeometry.Inner.SymmetricNormalizers.FourGroups
public import Theory.SpecificGroups.SymmetricFourSylow
import Mathlib.Tactic

/-!
# Pairing actors using their symmetric normalizers

Assuming the four-group normalizers are S₄, enlarge an actor A to an
order-eight subgroup D of T. It is a Sylow subgroup of N(A), hence D₈.
Select its other four-group B. The distinct four-groups generate D, and
index two gives D ≤ N(B). Uniqueness of the normal four-group in N(B)
then shows that A is nonnormal there. No containment T ≤ N(B) is used.

This conditional reduction is consumed by `SymmetricNormalizers.lean`.
Source: Aschbacher--Smith E.1.2 and E.1.14(6), printed pp.209--210 and 214,
citing Asc82a 4.10.
-/

public section

open Subgroup GorensteinWalter
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.PrimeGeometry.Inner.SymmetricNormalizers
variable {G : Type*} [Group G] [Finite G]
theorem eight_equiv_of_symmetric (D H : Subgroup G) (hDH : D ≤ H)
    (hD : Nat.card D = 8) (eH : H ≃* Equiv.Perm (Fin 4)) :
    Nonempty (D ≃* DihedralGroup 4) := by
  have hH : Nat.card H = 24 := by
    rw [Nat.card_congr eH.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm]
    norm_num
  let R := D.subgroupOf H
  have hR : Nat.card R = 2 ^ 3 := (Nat.card_congr (subgroupOfEquivOfLe hDH).toEquiv).trans hD
  have hi : R.index = 3 := by
    have h := R.card_mul_index
    rw [hR, hH] at h
    omega
  let S := (IsPGroup.of_card hR).toSylow (by rw [hi]; decide)
  obtain ⟨eS⟩ := Equiv.Perm.sylow_two_equiv_dihedral_four (S.mapSurjective (f := eH.toMonoidHom) eH.surjective)
  exact ⟨(subgroupOfEquivOfLe hDH).symm.trans ((eH.subgroupMap R).trans eS)⟩

omit [Finite G] in
theorem normalizes_four_of_card_eight (A D : Subgroup G) [IsKleinFour A]
    (hAD : A ≤ D) (hD : Nat.card D = 8) : D ≤ normalizer (A : Set G) := by
  have hi : (A.subgroupOf D).index = 2 := by
    have h := (A.subgroupOf D).index_mul_card
    rw [Nat.card_congr (subgroupOfEquivOfLe hAD).toEquiv, IsKleinFour.card_four, hD] at h
    omega
  exact (normal_subgroupOf_iff_le_normalizer hAD).mp (normal_of_index_eq_two hi)

theorem sup_eq_eight_of_distinct_four (A B D : Subgroup G) [IsKleinFour A] [IsKleinFour B]
    (hAD : A ≤ D) (hBD : B ≤ D) (hD : Nat.card D = 8) (hne : A ≠ B) : A ⊔ B = D := by
  have hle : A ⊔ B ≤ D := sup_le hAD hBD
  have hd : Nat.card (A ⊔ B : Subgroup G) ∣ 8 := by simpa only [hD] using card_dvd_of_le hle
  have hlow : 4 ≤ Nat.card (A ⊔ B : Subgroup G) := by
    simpa only [IsKleinFour.card_four] using card_le_of_le (le_sup_left : A ≤ A ⊔ B)
  have hn4 : Nat.card (A ⊔ B : Subgroup G) ≠ 4 := by
    intro hh
    have he : A = A ⊔ B := eq_of_le_of_card_ge le_sup_left (by rw [hh, IsKleinFour.card_four])
    have hBA : B ≤ A := he ▸ le_sup_right
    exact hne (eq_of_le_of_card_ge hBA (by simp only [IsKleinFour.card_four, le_refl])).symm
  have hh : Nat.card (A ⊔ B : Subgroup G) = 8 := by
    have hc : ∀ d ∈ Nat.divisors 8, d = 1 ∨ d = 2 ∨ d = 4 ∨ d = 8 := by decide
    have := hc _ (Nat.mem_divisors.mpr ⟨hd, by decide⟩)
    omega
  exact eq_of_le_of_card_ge hle (by rw [hh, hD])

theorem paired_four_of_normalizers (T : Sylow 2 G) (hT : 8 ≤ Nat.card T)
    (hnorm : ∀ B : Subgroup G, B ≤ T → IsKleinFour B →
      Nonempty (normalizer (B : Set G) ≃* Equiv.Perm (Fin 4)))
    (A : Subgroup G) [IsKleinFour A] (hAT : A ≤ T) :
    ∃ B : Subgroup G, B ≤ T ∧ IsKleinFour B ∧ B ≠ A ∧
      Nat.card (A ⊔ B : Subgroup G) = 8 ∧
      A ⊔ B ≤ normalizer (B : Set G) ∧
      ¬ (A.subgroupOf (normalizer (B : Set G))).Normal := by
  obtain ⟨D, hAD, hDT, hD, hDN⟩ := exists_eight_overgroup T hT A hAT
  obtain ⟨eA⟩ := hnorm A hAT inferInstance
  obtain ⟨eD⟩ := eight_equiv_of_symmetric D _ hDN hD eA
  obtain ⟨U, V, hUD, hVD, hU, hV, hUV, hcases⟩ := dihedral_four_four_groups D eD
  have hpair : ∃ B : Subgroup G, B ≤ D ∧ IsKleinFour B ∧ B ≠ A := by
    rcases hcases A hAD inferInstance with rfl | rfl
    · exact ⟨V, hVD, hV, hUV.symm⟩
    · exact ⟨U, hUD, hU, hUV⟩
  obtain ⟨B, hBD, hB, hBA⟩ := hpair
  let : IsKleinFour B := hB
  have hsup : A ⊔ B = D := sup_eq_eight_of_distinct_four A B D hAD hBD hD hBA.symm
  have hDN' := normalizes_four_of_card_eight B D hBD hD
  have hAN : A ≤ normalizer (B : Set G) := hAD.trans hDN'
  have hBN : B ≤ normalizer (B : Set G) := le_normalizer
  refine ⟨B, hBD.trans hDT, hB, hBA, hsup ▸ hD, hsup ▸ hDN', ?_⟩
  intro hnormal
  obtain ⟨eB⟩ := hnorm B (hBD.trans hDT) hB
  let : IsKleinFour (A.subgroupOf (normalizer (B : Set G))) := klein_subgroupOf _ _ hAN
  let : IsKleinFour (B.subgroupOf (normalizer (B : Set G))) := klein_subgroupOf _ _ hBN
  let := hnormal
  have he := (normal_four_eq_core eB (A.subgroupOf (normalizer (B : Set G)))).trans
    (normal_four_eq_core eB (B.subgroupOf (normalizer (B : Set G)))).symm
  have he' := congrArg (fun K => K.map (normalizer (B : Set G)).subtype) he
  rw [map_subgroupOf_eq_of_le hAN, map_subgroupOf_eq_of_le hBN] at he'
  exact hBA he'.symm
end CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.PrimeGeometry.Inner.SymmetricNormalizers
