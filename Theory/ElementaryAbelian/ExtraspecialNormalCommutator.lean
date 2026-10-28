module

public import Theory.GroupTheory.PGroup.CharacteristicCenterReduction
public import Theory.GroupTheory.PGroup.ClassTwoCyclicCenter

/-!
# The central line in a normalized extraspecial commutator

A nontrivial normal subgroup of a finite extraspecial two-group contains its
center: its central intersection is nontrivial, and the center has order two.
If U normalizes X and P lies between Z(U) and U, then U normalizes [P,X]. A
nontrivial image of that commutator in any quotient of U consequently forces
the central line into the commutator itself.

This justifies the central factor in the moved-space order calculation in
Aschbacher--Smith, Lemma 14.4.12, printed p.1012 (1 March 2004 manuscript).
-/

public section

namespace Subgroup
variable {G Q : Type*} [Group G] [Group Q]

/-- A nontrivial normal subgroup contains the unique central line. -/
theorem extraspecial_center_le_of_normal_ne_bot [Finite G] [IsExtraspecial 2 G]
    (A : Subgroup G) [A.Normal] (hne : A ≠ ⊥) : center G ≤ A := by
  have hi := center_inf_ne_bot_of_normal (IsExtraspecial.isPGroup 2 G) A hne
  have hc := (one_lt_card_iff_ne_bot (H := center G ⊓ A)).mpr hi
  have hz := IsExtraspecial.center_order_p 2 G
  have he : center G ⊓ A = center G := eq_of_le_of_card_ge inf_le_left (by omega)
  exact he ▸ inf_le_right

/-- A subgroup between the center and U is normalized by U, relative to the
original ambient group. -/
theorem extraspecial_le_normalizer_of_center_le (U P : Subgroup G) [IsExtraspecial 2 U]
    (hPU : P ≤ U) (hZP : center U ≤ P.subgroupOf U) : U ≤ normalizer (P : Set G) := by
  let K := P.subgroupOf U
  have hKn : K.Normal := by
    apply normalizer_eq_top_iff.mp
    apply top_unique
    apply le_normalizer_iff_commutator_le_right.mpr
    exact (commutator_mono le_top le_top).trans
      ((IsExtraspecial.quotient_elementary_abelian 2 U).commutator_le_center_of_central_quotient.trans hZP)
  let : K.Normal := hKn
  have hh := K.le_normalizer_map U.subtype
  simpa only [K, normalizer_eq_top, ← MonoidHom.range_eq_map, U.range_subtype,
    map_subgroupOf_eq_of_le hPU] using hh

/-- Nontriviality of the actual quotient image supplies the central kernel
needed to count the full moved subgroup. -/
theorem extraspecial_center_le_commutator_of_image_ne_bot [Finite G]
    (U P X : Subgroup G) [IsExtraspecial 2 U]
    (hPU : P ≤ U) (hZP : center U ≤ P.subgroupOf U)
    (hUX : U ≤ normalizer (X : Set G))
    (q : U →* Q) (hne : ((⁅P, X⁆).subgroupOf U).map q ≠ ⊥) :
    center U ≤ (⁅P, X⁆).subgroupOf U := by
  have hUP := extraspecial_le_normalizer_of_center_le U P hPU hZP
  have hUD : U ≤ normalizer (⁅P, X⁆ : Subgroup G) := by
    intro u hu
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [map_commutator, mem_normalizer_iff_map_conj_eq.mp (hUP hu),
      mem_normalizer_iff_map_conj_eq.mp (hUX hu)]
  let : ((⁅P, X⁆).subgroupOf U).Normal := normal_subgroupOf_of_le_normalizer hUD
  exact extraspecial_center_le_of_normal_ne_bot _
    (fun hb => hne (by rw [hb, Subgroup.map_bot]))

end Subgroup
