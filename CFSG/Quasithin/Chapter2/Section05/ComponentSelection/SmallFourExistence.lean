module
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.SmallFourFacts
public import Theory.GroupTheory.SemidihedralFourSubgroup
public import GorensteinWalter.DihedralCore
/-!
# An actual symmetric-four normalizer in every remaining component

The proved dihedral or semidihedral Sylow model contains an elementary
four-group. Its actual normalizer is S₄ by 2.5.8(5), so each remaining
component has order divisible by three. The four-group is constructed,
not added to the original source hypotheses.

Source: Aschbacher--Smith 2.5.8(3),(5), used in 2.5.20, printed pp.556,564.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection

private theorem four_transport {P Q : Type*} [Group P] [Group Q]
    (e : P ≃* Q) (W : Subgroup Q) (hW : IsKleinFour W) :
    ∃ F : Subgroup P, IsKleinFour F := by
  let F := W.map e.symm.toMonoidHom
  let f := W.equivMapOfInjective e.symm.toMonoidHom e.symm.injective
  exact ⟨F, {
    card_four := (Nat.card_congr f.toEquiv).symm.trans hW.card_four
    exponent_two := (Monoid.exponent_eq_of_mulEquiv f).symm.trans hW.exponent_two }⟩

/-- Each source Sylow model contains a literal elementary four-group. -/
theorem SourceSylowTwoShape.exists_four {P : Type*} [Group P] [Finite P]
    (h : SourceSylowTwoShape P) : ∃ F : Subgroup P, IsKleinFour F := by
  unfold SourceSylowTwoShape at h
  rcases h with h | h
  · obtain ⟨m, hm, ⟨e⟩⟩ := h
    obtain ⟨W, hW⟩ := GorensteinWalter.exists_kleinFour_subgroup_dihedral (by omega : 1 ≤ m)
    exact four_transport e W hW
  · obtain ⟨e⟩ := h
    let a := Semidihedral.standardRotation 4 (by omega)
    let b := Semidihedral.standardReflection 4 (by omega)
    obtain ⟨hE, hcard⟩ := Semidihedral.canonical_four (by omega : 4 ≤ 4) a b
      (Semidihedral.standardRotation_order 4 (by omega))
      (Semidihedral.standardReflection_order 4 (by omega))
      (Semidihedral.standard_conjugation 4 (by omega))
      (Semidihedral.standard_generators 4 (by omega))
    let E := closure {a ^ (2 ^ (4 - 2)), b}
    let : IsElementaryAbelian 2 E := hE
    let : Nontrivial E := (nontrivial_iff_ne_bot E).mpr (by
      intro he
      change Nat.card E = 4 at hcard
      rw [he, card_bot] at hcard
      omega)
    exact four_transport e E ⟨hcard, IsElementaryAbelian.exponent_eq_prime⟩

/-- The four-group and its S₄ normalizer in the original group. -/
theorem IsSmallRemainingComponent.exists_symmetric_four
    {K : Type*} [Group K] [Finite K] (h : IsSmallRemainingComponent K) :
    ∃ F : Subgroup K, IsKleinFour F ∧
      Nonempty (normalizer (F : Set K) ≃* Equiv.Perm (Fin 4)) := by
  let P : Sylow 2 K := default
  obtain ⟨E, hE⟩ := (h.sylowTwoShape P).exists_four
  let F := E.map (P : Subgroup K).subtype
  let eF := E.equivMapOfInjective (P : Subgroup K).subtype Subtype.coe_injective
  let : IsKleinFour F := {
    card_four := (Nat.card_congr eF.toEquiv).symm.trans hE.card_four
    exponent_two := (Monoid.exponent_eq_of_mulEquiv eF).symm.trans hE.exponent_two }
  exact ⟨F, inferInstance, h.four_normalizer F⟩

/-- The actual S₄ subgroup makes the component order divisible by three. -/
theorem IsSmallRemainingComponent.three_dvd_card
    {K : Type*} [Group K] [Finite K] (h : IsSmallRemainingComponent K) :
    3 ∣ Nat.card K := by
  obtain ⟨F, hF, ⟨e⟩⟩ := h.exists_symmetric_four
  have hthree : 3 ∣ Nat.card (normalizer (F : Set K)) := by
    rw [Nat.card_congr e.toEquiv]
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm]
  exact hthree.trans (normalizer (F : Set K)).card_subgroup_dvd_card

end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
