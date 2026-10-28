module
public import Theory.Representation.BinaryPermutation.EightOrthogonalActors
public import Theory.Representation.BinaryConjugationSection.ImageDimensions
public import Theory.Representation.BinaryConjugationSection.tensorChief

/-!
# Orthogonal movement cannot be confined to one binary line

A nonidentity even involution moves at least a plane on the binary orthogonal
six-space. If its commutators on a literal section lie in the denominator
extended by a subgroup of order two, their coordinate image has at most two
elements. This contradicts the displacement bound. Normality is relative
to the actor, and the extra line need not lie in the section numerator.

Source application: Aschbacher–Smith, The Classification of Quasithin Groups,
13.8.11(1) and 13.8.32(3), printed pp.950 and 965.
-/

public noncomputable section
open Subgroup
namespace Representation.BinaryConjugationSection
variable {G : Type*} [Group G] [Finite G]

private theorem line_sup_index_bound (H U A : Subgroup G)
    (hUH : U ≤ H) (hAH : A ≤ H) (hn : H ≤ normalizer (U:Set G))
    (hA : Nat.card A = 2) : U.relIndex (U ⊔ A) ≤ 2 := by
  let J := U ⊔ A
  let : (U.subgroupOf J).Normal :=
    normal_subgroupOf_of_le_normalizer ((sup_le hUH hAH).trans hn)
  have he := relIndex_sup_left (A.subgroupOf J) (U.subgroupOf J)
  rw [←subgroupOf_sup (show U ≤ J from le_sup_left) (show A ≤ J from le_sup_right),
    relIndex_subgroupOf le_rfl,relIndex_subgroupOf (show A ≤ J from le_sup_right)] at he
  rw [he]
  exact hA ▸ Nat.le_of_dvd Nat.card_pos (relIndex_dvd_card U A)

/-- A nontrivial elementary actor on the binary orthogonal six-section cannot
have all its commutators in the denominator extended by one order-two line.
The line need not lie in the numerator. -/
theorem orthogonal_commutator_not_le_line
    (H VH UH QH B A : Subgroup G) [IsElementaryAbelian 2 B]
    (π : H →* Equiv.Perm (Fin 8)) (heven : π.range ≤ alternatingGroup (Fin 8))
    (hker : π.ker = QH.subgroupOf H)
    (d : BinaryConjugationSection H VH UH
      ((BinaryPermutation.naturalRepresentation (Fin 8)).comp π))
    (hBH : B ≤ H) (houtside : ¬ B ≤ QH) (hAH : A ≤ H)
    (hA : Nat.card A = 2) : ¬ ⁅B,VH⁆ ≤ UH ⊔ A := by
  intro hc
  let C := VH ⊓ (UH ⊔ A)
  have hcomm : ⁅B,VH⁆ ≤ C := le_inf
    (le_normalizer_iff_commutator_le_right.mp (hBH.trans d.normalized)) hc
  have hn : H ≤ normalizer (UH:Set G) :=
    (normal_subgroupOf_iff_le_normalizer (d.kernel_le.trans d.section_le)).mp d.kernel_normal_actor
  have hcard : Nat.card (d.imageSpace C) ≤ 2 := by
    rw [d.imageSpace_card_eq_relIndex C inf_le_left]
    exact (relIndex_le_of_le_right inf_le_right index_ne_zero_of_finite).trans
      (line_sup_index_bound H UH A (d.kernel_le.trans d.section_le) hAH hn hA)
  obtain ⟨a,ha,hna⟩ := SetLike.not_le_iff_exists.mp houtside
  let aH : H := ⟨a,hBH ha⟩
  have hne : π aH ≠ 1 := by
    intro hh
    have hm : aH ∈ π.ker := hh
    rw [hker] at hm
    exact hna hm
  have ha2 : (π aH)^2 = 1 := by
    rw [←map_pow]
    have hh : aH^2 = 1 := Subtype.ext (elemPow_eq_one_of_isElementaryAbelian a ha)
    rw [hh,map_one]
  have hlower := BinaryPermutation.EightOrthogonalActors.two_le_displacement
    (π aH) (heven ⟨aH,rfl⟩) hne ha2
  have hm := d.displacement_range_le_imageSpace_of_commutator_le B C hcomm aH ha
  have hd := hlower.trans (Submodule.finrank_mono hm)
  have hp : 4 ≤ Nat.card (d.imageSpace C) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
    exact Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) hd
  omega

end Representation.BinaryConjugationSection
