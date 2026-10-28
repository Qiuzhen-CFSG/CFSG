module

public import ABG.ChapterII.Section5.ASevenNormalizedOddSubgroup
public import Theory.GroupTheory.NormalizedSupCard
import Mathlib.Tactic

/-!
# Sylow signalizers in alternating seven

ABG Chapter II §5 Lemma 9(i), article p49 (PDF page50), states that a
maximal member of the invariant/disjoint subgroup family for an actual
Sylow two-subgroup of a group isomorphic to A₇ has order three and
centralizes a four subgroup of that Sylow subgroup. The family is written
explicitly using normalization and disjointness, as in the notation on
article p7; maximality is not maximality among all subgroups.

The normalized disjoint product shows that every member has odd order:
its order divides the odd Sylow index. An isomorphism followed by Sylow
conjugacy takes the prescribed Sylow to the concrete subgroup `a7S`.
The imported `aSeven_normalized_odd_subgroup_le` puts its signalizer image
inside the canonical order-three subgroup `a7U`. Direct computations show
that `a7U` itself belongs to the family and centralizes the Klein four
subgroup `a7V` inside `a7S`. Pulling this candidate back and applying
maximality gives equality, then transports its order and four-subgroup
witness to the original group. The finite containment calculation is
proved separately by kernel-checked permutation certificates; neither
semilinear classification nor a stronger four-group signalizer assertion
is assumed.
-/

namespace ABG

open GorensteinWalter
open scoped Pointwise

private instance (element : A7) : Decidable (element ∈ a7U) := by
  change Decidable (element = 1 ∨ element = a7a ∨ element = a7a ^ 2)
  infer_instance

private instance (element : A7) : Decidable (element ∈ a7S) := by
  change Decidable (element = 1 ∨ element = a7v ∨ element = a7v ^ 2 ∨ element = a7v ^ 3 ∨
    element = a7s ∨ element = a7s * a7v ∨ element = a7s * a7v ^ 2 ∨ element = a7s * a7v ^ 3)
  infer_instance

private theorem standard_card : Nat.card a7S = 8 := by
  let members : Finset A7 := {1, a7v, a7v ^ 2, a7v ^ 3, a7s,
    a7s * a7v, a7s * a7v ^ 2, a7s * a7v ^ 3}
  have heq : a7S = (members : Set A7) := by ext element; simp [a7S, members]
  have hcard : Nat.card a7S = members.card := by
    calc
      Nat.card a7S = Nat.card (members : Set A7) :=
        Nat.card_congr (Equiv.setCongr heq)
      _ = members.card := by simp
  rw [hcard]
  decide

private def standardSylow : Sylow 2 A7 := Sylow.ofCard a7S (by
  rw [standard_card, nat_card_alternatingGroup, Nat.card_eq_fintype_card]
  norm_num
  rw [show 2520 = 2 ^ 3 * 315 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Nat.factorization_pow]
  simp [Nat.prime_two.factorization_self,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 315)])

private theorem signalizer_odd {GroupType : Type*} [Group GroupType] [Finite GroupType]
    (sylow : Sylow 2 GroupType) (signalizer : Subgroup GroupType)
    (hn : (sylow : Subgroup GroupType) ≤ Subgroup.normalizer (signalizer : Set GroupType))
    (hd : Disjoint signalizer (sylow : Subgroup GroupType)) : Odd (Nat.card signalizer) := by
  have hdiv := (signalizer ⊔ (sylow : Subgroup GroupType)).card_subgroup_dvd_card
  rw [Subgroup.card_sup_eq_mul_of_normalizes_of_disjoint signalizer _ hn hd,
    ← (sylow : Subgroup GroupType).card_mul_index, Nat.mul_comm (Nat.card signalizer)] at hdiv
  have hki : Nat.card signalizer ∣ (sylow : Subgroup GroupType).index :=
    Nat.dvd_of_mul_dvd_mul_left Nat.card_pos hdiv
  apply Odd.of_dvd_nat _ hki
  exact Nat.not_even_iff_odd.mp (fun heven => sylow.not_dvd_index (even_iff_two_dvd.mp heven))

private theorem standard_witness :
    Nat.card a7U = 3 ∧
      a7S ≤ Subgroup.normalizer (a7U : Set A7) ∧
      Disjoint a7U a7S ∧ a7V ≤ a7S ∧
      IsKleinFour a7V ∧ a7U ≤ Subgroup.centralizer (a7V : Set A7) := by
  refine ⟨aSeven_structure_fact_1_8_ii_centralizer.1, ?_, ?_, ?_,
    aSeven_structure_fact_1_8_ii_centralizer.2.2.2, ?_⟩
  · rw [Subgroup.le_normalizer_iff]
    intro actor hactor element hx
    change actor = 1 ∨ actor = a7v ∨ actor = a7v ^ 2 ∨ actor = a7v ^ 3 ∨
      actor = a7s ∨ actor = a7s * a7v ∨ actor = a7s * a7v ^ 2 ∨
      actor = a7s * a7v ^ 3 at hactor
    change element = 1 ∨ element = a7a ∨ element = a7a ^ 2 at hx
    rcases hactor with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hx with rfl | rfl | rfl <;> decide
  · rw [Subgroup.disjoint_def]
    intro element hxU hxS
    change element = 1 ∨ element = a7a ∨ element = a7a ^ 2 at hxU
    rcases hxU with rfl | rfl | rfl
    · rfl
    · exact False.elim ((by decide : a7a ∉ a7S) hxS)
    · exact False.elim ((by decide : a7a ^ 2 ∉ a7S) hxS)
  · intro element hx
    change element = 1 ∨ element = a7t ∨ element = a7u ∨ element = a7t * a7u at hx
    rcases hx with rfl | rfl | rfl | rfl <;> decide
  · intro element hx
    rw [Subgroup.mem_centralizer_iff]
    intro other hy
    change element = 1 ∨ element = a7a ∨ element = a7a ^ 2 at hx
    change other = 1 ∨ other = a7t ∨ other = a7u ∨ other = a7t * a7u at hy
    rcases hx with rfl | rfl | rfl <;>
      rcases hy with rfl | rfl | rfl | rfl <;> decide

private theorem normalized_sylow_equiv {GroupType : Type*} [Group GroupType] [Finite GroupType]
    (sylow : Sylow 2 GroupType) (modelEquiv : GroupType ≃* A7) :
    ∃ equiv : GroupType ≃* A7, (sylow : Subgroup GroupType).map equiv.toMonoidHom = a7S := by
  classical
  let image : Sylow 2 A7 := sylow.mapSurjective (f := modelEquiv.toMonoidHom) modelEquiv.surjective
  obtain ⟨actor, hactor⟩ := MulAction.exists_smul_eq A7 image standardSylow
  refine ⟨modelEquiv.trans (MulAut.conj actor), ?_⟩
  have mappedEquality := congrArg (fun P : Sylow 2 A7 => (P : Subgroup A7)) hactor
  change ((sylow : Subgroup GroupType).map modelEquiv.toMonoidHom).map
    (MulAut.conj actor).toMonoidHom = a7S at mappedEquality
  simpa [Subgroup.map_map, MulEquiv.coe_monoidHom_trans] using mappedEquality

/-- ABG II.5 Lemma 9(i), for the prescribed actual Sylow subgroup. -/
public theorem aSeven_sylow_signalizers
    {GroupType : Type*} [Group GroupType] [Finite GroupType]
    (hH : Nonempty (GroupType ≃* A7)) (sylow : Sylow 2 GroupType) (signalizer : Subgroup GroupType)
    (hK : Maximal (fun candidate : Subgroup GroupType =>
      Disjoint candidate (sylow : Subgroup GroupType) ∧
        (sylow : Subgroup GroupType) ≤ Subgroup.normalizer (candidate : Set GroupType)) signalizer) :
    Nat.card signalizer = 3 ∧ ∃ four : Subgroup GroupType,
      four ≤ (sylow : Subgroup GroupType) ∧ IsKleinFour four ∧
        signalizer ≤ Subgroup.centralizer (four : Set GroupType) := by
  classical
  obtain ⟨equiv, hf⟩ := normalized_sylow_equiv sylow hH.some
  let image : Subgroup A7 := signalizer.map equiv.toMonoidHom
  have hnorm : a7S ≤ Subgroup.normalizer (image : Set A7) := by
    rw [← hf, ← signalizer.map_equiv_normalizer_eq equiv]
    exact Subgroup.map_mono hK.prop.2
  have hodd : Odd (Nat.card image) := by
    rw [Subgroup.card_map_of_injective equiv.injective]
    exact signalizer_odd sylow signalizer hK.prop.2 hK.prop.1
  have hle : image ≤ a7U := aSeven_normalized_odd_subgroup_le image hodd hnorm
  let upper : Subgroup GroupType := a7U.map equiv.symm.toMonoidHom
  have huS : a7S.map equiv.symm.toMonoidHom = (sylow : Subgroup GroupType) := by
    rw [← hf]
    simp [Subgroup.map_map]
  have hupper : Disjoint upper (sylow : Subgroup GroupType) ∧
      (sylow : Subgroup GroupType) ≤ Subgroup.normalizer (upper : Set GroupType) := by
    constructor
    · rw [← huS]
      exact Subgroup.disjoint_map equiv.symm.injective standard_witness.2.2.1
    · rw [← huS, ← a7U.map_equiv_normalizer_eq equiv.symm]
      exact Subgroup.map_mono standard_witness.2.1
  have hKup : signalizer ≤ upper := by
    have hh := Subgroup.map_mono (f := equiv.symm.toMonoidHom) hle
    simpa [image, upper, Subgroup.map_map] using hh
  have hKeq : signalizer = upper := le_antisymm hKup (hK.2 hupper hKup)
  constructor
  · rw [hKeq, Subgroup.card_map_of_injective equiv.symm.injective]
    exact standard_witness.1
  · let four : Subgroup GroupType := a7V.map equiv.symm.toMonoidHom
    have hV : IsKleinFour four := by
      let modelEquiv := a7V.equivMapOfInjective equiv.symm.toMonoidHom equiv.symm.injective
      exact ⟨(Nat.card_congr modelEquiv.toEquiv).symm.trans
          standard_witness.2.2.2.2.1.card_four,
        (Monoid.exponent_eq_of_mulEquiv modelEquiv).symm.trans
          standard_witness.2.2.2.2.1.exponent_two⟩
    refine ⟨four, ?_, hV, ?_⟩
    · rw [← huS]
      exact Subgroup.map_mono standard_witness.2.2.2.1
    · rw [hKeq]
      intro element hx
      obtain ⟨preimage, hpreimage, rfl⟩ := hx
      rw [Subgroup.mem_centralizer_iff]
      intro other hy
      obtain ⟨other, hother, rfl⟩ := hy
      simpa only [MulEquiv.coe_toMonoidHom, map_mul] using congrArg equiv.symm
        ((Subgroup.mem_centralizer_iff.mp
          (standard_witness.2.2.2.2.2 hpreimage)) other hother)


end ABG
