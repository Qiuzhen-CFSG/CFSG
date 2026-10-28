module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.LinearThree.Descent
public import Theory.GroupTheory.PrimeRankNormalIntersection
public import Theory.SpecificGroups.FFLinearPrimeCore

/-!
# The cubic intersection in the original linear-three branch

An elementary plane in K = O²(H) normalizes X. Since SL₃ has an element
of order three and m₃(I) ≤ 2, the normal-intersection rank theorem forces
three to divide |K ∩ X|. The original K centralizes ZS, so this is also
the literal intersection K ∩ C_X(ZS) used in the nonbinary argument.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of
15.2.23, printed p.1116; refs/quasithin.pdf.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section02.PlaneUniquenessPreceding.LinearThree

variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS I : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)

include d in
private theorem residual_intersection_three_dvd
    (hI : PlaneEscapes Mc ZS I) {A : Subgroup G} (hAI : A ≤ I)
    (hKA : (pResidual 2 H).map H.subtype ≤ normalizer (A : Set G))
    (hthree : 3 ∣ Nat.card A) :
    3 ∣ Nat.card ((pResidual 2 H).map H.subtype ⊓ A : Subgroup G) := by
  let K := (pResidual 2 H).map H.subtype
  have hKI : K ≤ I :=
    (le_sup_left.trans (d.residual_sup_planeSylow_le hI)).trans inf_le_right
  obtain ⟨E,hE,hcard⟩ := exists_elementaryAbelian_card_primeRank (G := K) (p := 3)
  let := hE
  let EI := E.map (inclusion hKI)
  let e : E ≃* EI := E.equivMapOfInjective (inclusion hKI) (inclusion_injective hKI)
  let : IsElementaryAbelian 3 EI := IsElementaryAbelian.of_injective e.symm.toMonoidHom e.symm.injective
  have hEI : Nat.card EI = 3 ^ 2 := by
    rw [← Nat.card_congr e.toEquiv, hcard, residual_rank_two d]
  have hnorm : EI ≤ normalizer (A.subgroupOf I : Set I) := by
    rw [← subgroupOf_normalizer_eq hAI]
    rintro _ ⟨x,hx,rfl⟩
    exact hKA x.property
  have hAIcard : 3 ∣ Nat.card (A.subgroupOf I) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hAI).toEquiv]
    exact hthree
  have hr : primeRank 3 I ≤ 2 :=
    (Chapter1.RadicalExclusions.sqtk_of_mem_H hsource.ambient hI.1).stronglyQuasithin
      3 Nat.prime_three (by decide)
  have hne := Subgroup.inf_ne_bot_of_elementary_plane EI (A.subgroupOf I)
    hnorm hAIcard hEI hr
  have hp : IsPGroup 3 (EI ⊓ A.subgroupOf I : Subgroup I) :=
    (IsElementaryAbelian.isPGroup 3 EI).to_le inf_le_left
  have hd : 3 ∣ Nat.card (EI ⊓ A.subgroupOf I : Subgroup I) := by
    rcases hp.card_eq_or_dvd with h | h
    · exact (hne (card_eq_one.mp h)).elim
    · exact h
  let j : (EI ⊓ A.subgroupOf I : Subgroup I) →* (K ⊓ A : Subgroup G) := {
    toFun := fun x => ⟨x.val.val, by
      obtain ⟨k,hk,he⟩ := x.property.1
      exact ⟨(congrArg Subtype.val he) ▸ k.property,x.property.2⟩⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  have hj : Function.Injective j := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : (K ⊓ A : Subgroup G) => (z : G)) h
  exact hd.trans (card_dvd_of_injective j hj)

include d in
/-- The original rank-two residual meets X in a subgroup of order divisible by three. -/
theorem Branch.residual_component_intersection_three_dvd
    {X : Subgroup G} {n : ℕ} {F : Type} [Field F] [Finite F]
    (b : Branch M I X n F) (hI : PlaneEscapes Mc ZS I) :
    3 ∣ Nat.card ((pResidual 2 H).map H.subtype ⊓ X : Subgroup G) := by
  have hKX : (pResidual 2 H).map H.subtype ≤ normalizer (X : Set G) := by
    have hh := d.residual_normalizes_component hI b.input.component.2
    rwa [map_subgroupOf_eq_of_le b.input.component.1] at hh
  apply residual_intersection_three_dvd d hI b.input.component.1 hKX
  obtain ⟨e⟩ := b.ms.1.model
  have hd : 3 ∣ Nat.card (X ⧸ pCore 2 X) := by
    rw [Nat.card_congr e.toEquiv]
    let := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow
      (by simpa only [Nat.card_eq_fintype_card] using b.field_card)
    exact Theory.SpecificGroups.three_dvd_card_sl_three F
  exact hd.trans (by simpa only [index_eq_card] using (pCore 2 X).index_dvd_card)

include d in
/-- The same cubic intersection lies in the actual C_X(ZS). -/
theorem Branch.residual_centralizer_intersection_three_dvd
    {X : Subgroup G} {n : ℕ} {F : Type} [Field F] [Finite F]
    (b : Branch M I X n F) (hI : PlaneEscapes Mc ZS I) :
    3 ∣ Nat.card ((pResidual 2 H).map H.subtype ⊓
      (X ⊓ centralizer (ZS : Set G)) : Subgroup G) := by
  have he : (pResidual 2 H).map H.subtype ⊓ (X ⊓ centralizer (ZS : Set G)) =
      (pResidual 2 H).map H.subtype ⊓ X := by
    apply le_antisymm (inf_le_inf_left _ inf_le_left)
    exact le_inf inf_le_left (le_inf inf_le_right (inf_le_left.trans d.residual_centralizes))
  rw [he]
  exact b.residual_component_intersection_three_dvd d hI

end CFSG.Quasithin.Chapter15.Section02.PlaneUniquenessPreceding.LinearThree
