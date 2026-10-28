module

public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.ExceptionalAction.HSWitnesses.QuotientSelection.Product
public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.ExceptionalAction.HSWitnesses.FixedImage
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSInner
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismPointStabilizers
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismNormalizerIndex
public import Theory.GroupTheory.DoubleCoverCentralizer.Action


/-!
# Selecting the two HS quotient-centralizer rows in the given four-group

The faithful quotient action has a nonidentity inner actor because the outer
automorphism index of the actual HS carrier is at most two. The projected
component has type A₆ or A₈ by the universal earlier component clause, so
its order is divisible by nine. Its containment in every fixed subgroup
excludes the inner core-extension row and the outer elementary-extension row
by their orders 7680 and 1920.

If all four actors were inner, their unique lifts would commute with the
selected inner actor and with the projected component. Inside its product
centralizer C₂ × Aut(A₆), the actual embedded perfect component has order
at least 360 and therefore has centralizer of order at most two. Faithfulness
would embed a four-group in that centralizer, a contradiction. An outer actor
therefore exists and has fixed subgroup S₈.

The universal statements `h15` and `h17` below are the earlier HS table and
component clauses, not selection or embedding assumptions. Their model-table
proofs remain with the 16.1 owners. This module proves the quotient selection;
it makes no assertion about layers in a covering group.

Source: Aschbacher–Smith, 16.3.5, printed p.1179 / PDF p.1196, using
16.1.5(10) and 16.1.7(3h), printed pp.1172–1173.
-/

public section

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter16.FourGroupTransfer.ExceptionalAction.HSWitnesses
open OtherPreliminaries.JankoTwoHigmanSims
open Sporadic.LeechRelated.HS
namespace QuotientSelection

private theorem outer_index_le_two : (MulAut.conj : Carrier →* MulAut Carrier).range.index ≤ 2 := by
  have hc := Nat.card_le_card_of_surjective _
    (generated.normalizerOuterHom_surjective
      (normalizer_surjective_of_pointStabilizer_map pointStabilizer_map))
  exact hc.trans (Nat.le_of_dvd (by decide) normalizer_relIndex_dvd_two)

private theorem elementaryExtension_card {C : Type*} [Group C] [Finite C]
    (h : IsHSElementaryExtension C) : Nat.card C = 1920 := by
  obtain ⟨Q, hn, ⟨eQ⟩, ⟨eR⟩⟩ := h
  let := hn
  have hQ : Nat.card Q = 16 := by
    rw [Nat.card_congr eQ.toEquiv]
    simp [E16, C2]
  have hR : Q.index = 120 := by
    rw [index_eq_card, Nat.card_congr eR.toEquiv, Nat.card_perm, Nat.card_fin]
    rfl
  have hc := Q.card_mul_index
  rw [hQ, hR] at hc
  exact hc.symm

private theorem not_all_inner {A : Type*} [Group A] [Finite A] [IsMulCommutative A]
    [IsSimpleGroup Carrier] [Group.IsPerfect Carrier]
    (α : A →* MulAut Carrier) (hα : Function.Injective α) (hA : Nat.card A = 4)
    (J : Subgroup Carrier) [Group.IsPerfect J] (hJ : 360 ≤ Nat.card J)
    (hfix : ∀ a : A, ∀ j ∈ J, α a j = j)
    (t : A) (e : (α t).fixedSubgroup ≃* C2 × MulAut A6)
    (hall : ∀ a : A, ∃ g : Carrier, α a = MulAut.conj g) : False := by
  classical
  choose f hf using hall
  have hfinj : Function.Injective f := by
    intro x y hxy
    apply hα
    rw [hf x, hf y, hxy]
  have hft (x : A) : α t (f x) = f x := by
    apply HSInner.conj_injective
    calc
      MulAut.conj (α t (f x)) = α t * MulAut.conj (f x) * (α t)⁻¹ := by
        apply MulEquiv.ext
        intro y
        simp
      _ = MulAut.conj (f x) := by
        rw [← hf x, ← map_mul, mul_comm t x, map_mul]
        simp [mul_assoc]
  let C := (α t).fixedSubgroup
  have hJC : J ≤ C := fun j hj => (MulAut.mem_fixedSubgroup _ _).mpr (hfix t j hj)
  let K := J.subgroupOf C
  let M := K.map e.toMonoidHom
  let eJ : J ≃* M := (subgroupOfEquivOfLe hJC).symm.trans (e.subgroupMap K)
  let : Group.IsPerfect M := Group.IsPerfect.ofSurjective (f := eJ.toMonoidHom) eJ.surjective
  have hM : 360 ≤ Nat.card M := by rwa [← Nat.card_congr eJ.toEquiv]
  let g : A → C := fun x => ⟨f x, (MulAut.mem_fixedSubgroup _ _).mpr (hft x)⟩
  let F : A → centralizer (M : Set (C2 × MulAut A6)) := fun x => ⟨e (g x), by
    rintro z ⟨y, hy, rfl⟩
    change e y * e (g x) = e (g x) * e y
    rw [← map_mul, ← map_mul]
    apply congrArg e
    apply Subtype.ext
    have hj := hfix x y.val hy
    rw [hf x] at hj
    change f x * y.val * (f x)⁻¹ = y.val at hj
    exact ((mul_inv_eq_iff_eq_mul).mp hj).symm⟩
  have hF : Function.Injective F := by
    intro x y hxy
    apply hfinj
    exact congrArg Subtype.val (e.injective (congrArg Subtype.val hxy))
  have hb := (Nat.card_le_card_of_injective F hF).trans (product_centralizer_card_le_two M hM)
  omega

private theorem model_card {J : Type*} [Group J] (hJ : IsHSCentralizerComponent J) :
    Nat.card J = 360 ∨ Nat.card J = 20160 := by
  change Nonempty (J ≃* A6) ∨ Nonempty (J ≃* A8) at hJ
  rcases hJ with hJ | hJ
  · obtain ⟨e⟩ := hJ
    exact Or.inl ((Nat.card_congr e.toEquiv).trans AlternatingSix.ShadowLocal.card_A6)
  · obtain ⟨e⟩ := hJ
    apply Or.inr
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    rfl

/-- A faithful four-group centralizing an actual perfect HS subgroup of
one of the two source component types contains actors in both specified rows.
The model type is used through the order of the embedded subgroup; its
placement in the product row is proved in `not_all_inner`. -/
theorem select_rows {A : Type*} [Group A] [Finite A] [IsElementaryAbelian 2 A]
    [IsSimpleGroup Carrier] [Group.IsPerfect Carrier]
    (htable : ∀ r : MulAut Carrier, orderOf r = 2 → HSInvolutionAlternative r)
    (α : A →* MulAut Carrier) (hα : Function.Injective α) (hA : Nat.card A = 4)
    (J : Subgroup Carrier) [Group.IsPerfect J] (hJ : IsHSCentralizerComponent J)
    (hfix : ∀ a : A, ∀ j ∈ J, α a j = j) :
    ∃ s t : A, orderOf s = 2 ∧ orderOf t = 2 ∧
      Nonempty ((α s).fixedSubgroup ≃* S8) ∧
      Nonempty ((α t).fixedSubgroup ≃* C2 × MulAut A6) := by
  have horder (a : A) (ha : a ≠ 1) : orderOf a = 2 :=
    orderOf_eq_prime
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 A) a) ha
  have hcard := model_card hJ
  have hJ9 : 9 ∣ Nat.card J := by rcases hcard with h | h <;> rw [h] <;> decide
  have hJlarge : 360 ≤ Nat.card J := by rcases hcard with h | h <;> omega
  have hfixed9 (a : A) : 9 ∣ Nat.card (α a).fixedSubgroup :=
    hJ9.trans (card_dvd_of_le (fun j hj => (MulAut.mem_fixedSubgroup _ _).mpr (hfix a j hj)))
  obtain ⟨t, ht, hti⟩ := DoubleCoverCentralizer.exists_inner_actor α hA
    (DoubleCoverCentralizer.innerActors_index_le_outer α outer_index_le_two)
  have htorder := horder t ht
  have hta : orderOf (α t) = 2 := (orderOf_injective α hα t).trans htorder
  have htprod : Nonempty ((α t).fixedSubgroup ≃* C2 × MulAut A6) := by
    rcases htable (α t) hta with ⟨_, hc | hp⟩ | ⟨ho, _⟩
    · have hd := hfixed9 t
      rw [HSInner.coreExtension_card hc] at hd
      norm_num at hd
    · exact hp
    · exact (ho hti).elim
  have hs : ∃ s : A, ¬ ∃ g : Carrier, α s = MulAut.conj g := by
    by_contra! hall
    exact not_all_inner α hα hA J hJlarge hfix t htprod.some hall
  obtain ⟨s, hs⟩ := hs
  have hsne : s ≠ 1 := by
    rintro rfl
    exact hs ⟨1, by simp⟩
  have hsorder := horder s hsne
  have hsa : orderOf (α s) = 2 := (orderOf_injective α hα s).trans hsorder
  refine ⟨s, t, hsorder, htorder, ?_, htprod⟩
  rcases htable (α s) hsa with ⟨hi, _⟩ | ⟨_, hs8 | he⟩
  · exact (hs hi).elim
  · exact hs8
  · have hd := hfixed9 s
    rw [elementaryExtension_card he] at hd
    norm_num at hd

end QuotientSelection

universe u
variable {G : Type u} [Group G]
/-- Select the two quotient rows from the actual configuration, using only
the universal HS clauses of 16.1.5(10) and 16.1.7(3h) as earlier source inputs.
The component clause is applied to the component constructed by
`exists_projected_component`, whose image is the actual projection of L.
Neither a selected actor nor any embedding conclusion is an input. -/
theorem Configuration.quotientFixedTypes_of_source_clauses [Finite G] {𝒦 : GroupClass.{u}}
    {E L I : Subgroup G} {a i : G} (h : Configuration 𝒦 E L I a i)
    (e : (I ⧸ pCore 2 I) ≃* Carrier)
    (h15 : ∀ r : MulAut Carrier, orderOf r = 2 → HSInvolutionAlternative r)
    (h17 : ∀ (r : MulAut Carrier), orderOf r = 2 →
      ∀ J : Subgroup r.fixedSubgroup, IsComponent r.fixedSubgroup J →
        IsHSCentralizerComponent J) : QuotientFixedTypes E I h.normalizes e := by
  let := h.model_simple e
  let := h.model_perfect e
  let := h.elementary
  let α := quotientAction E I h.normalizes e
  let seed : E := ⟨a, h.actor_mem⟩
  have hseedorder : orderOf (α seed) = 2 :=
    (orderOf_injective α (h.quotient_faithful e) seed).trans
      ((orderOf_injective E.subtype Subtype.val_injective seed).symm.trans h.setup.involution_t)
  obtain ⟨J, hJ, himage⟩ := h.exists_projected_component e
  have hm := h17 (α seed) hseedorder J hJ
  let P := J.map (α seed).fixedSubgroup.subtype
  let eP : J ≃* P := J.equivMapOfInjective _ Subtype.val_injective
  have hPmodel : IsHSCentralizerComponent P := by
    change Nonempty (J ≃* A6) ∨ Nonempty (J ≃* A8) at hm
    change Nonempty (P ≃* A6) ∨ Nonempty (P ≃* A8)
    rcases hm with hm | hm
    · obtain ⟨f⟩ := hm
      exact Or.inl ⟨eP.symm.trans f⟩
    · obtain ⟨f⟩ := hm
      exact Or.inr ⟨eP.symm.trans f⟩
  let := hJ.2
  let : Group.IsPerfect P := Group.IsPerfect.map _
  apply QuotientSelection.select_rows h15 α (h.quotient_faithful e) h.card P hPmodel
  intro x j hj
  change j ∈ J.map (α seed).fixedSubgroup.subtype at hj
  rw [himage] at hj
  obtain ⟨l, hl, rfl⟩ := hj
  exact quotientAction_fixes_component h.proper.le h.normalizes h.centralizes e x ⟨l.val, hl⟩

end CFSG.Quasithin.Chapter16.FourGroupTransfer.ExceptionalAction.HSWitnesses
