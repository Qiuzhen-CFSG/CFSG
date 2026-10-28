module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.ActorGeometry
public import Theory.SpecificGroups.PSL3.OddInvolutionFixed.Inner
public import Theory.SpecificGroups.SL3.InvolutionConjugacy
public import Theory.GroupTheory.FourActorSylowPosition
public import Theory.ElementaryAbelian.Join

/-!
# Positioning the original outer actor

All involutions of the actual inner PSL₃ are conjugate. An outer four-group
can therefore be conjugated, as a whole family member, into the chosen Sylow
subgroup with its inner involution central in that Sylow. An eight-group
already contains every Sylow-central involution, by the ambient rank bound.
Its inner four-group supplies such a central involution by normality.

These are preparations for the local constructions in Aschbacher--Smith,
E.1.14(7), printed p.214, using A.3.21(a), p.55. They do not assert that an
arbitrary centralizer intersection is Sylow or that a centralizer is an E-member.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
open Matrix.PSL3.OddPrimeGraphExtension
open Matrix.PSL3.OddPrimeGraphExtension.GraphLargeStructure
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies
variable (F : Type*) [Field F] [Finite F] [IsSimpleGroup PSL(3,F)]

/-- The single involution class in SL₃ descends to the literal inner part. -/
theorem inner_involutions_isConj {p : ℕ} (ho : Odd p) (hF : Nat.card F = p)
    (x y : innerPart F) (hx : orderOf x = 2) (hy : orderOf y = 2) : IsConj x y := by
  let e := (innerPartEquiv F).symm
  obtain ⟨u, hu, hue⟩ := Matrix.PSL3.OddInvolutionFixed.involution_lift (e x)
    ((e.orderOf_eq x).trans hx)
  obtain ⟨v, hv, hve⟩ := Matrix.PSL3.OddInvolutionFixed.involution_lift (e y)
    ((e.orderOf_eq y).trans hy)
  have h2 : (2 : F) ≠ 0 := Theory.SpecificGroups.OddThreeRank.two_ne_zero_of_odd_card
    ho (by simpa only [pow_one] using hF : Nat.card F = p ^ 1)
  have hc := (Matrix.PSL3.projection F).map_isConj (Matrix.SL3.involutions_isConj F u v hu hv h2)
  rw [hue, hve] at hc
  simpa only [MulEquiv.coe_toMonoidHom, e.symm_apply_apply] using e.symm.toMonoidHom.map_isConj hc

/-- Conjugate the entire four-group actor, retaining its membership in Ω. -/
theorem exists_positioned_four_actor {p : ℕ} (ho : Odd p) (hF : Nat.card F = p)
    (T : Sylow 2 (graphExtension F)) {Ω : Set (Subgroup (graphExtension F))}
    (hΩ : IsElementaryFamily Ω) {A : Subgroup (graphExtension F)} (hA : A ∈ Ω)
    (hfour : Nat.card A = 4) (hinner : Nat.card (A ⊓ innerPart F : Subgroup _) = 2) :
    ∃ B ∈ Ω, B ≤ (T : Subgroup _) ∧ Nat.card B = 4 ∧
      Nat.card (B ⊓ innerPart F : Subgroup _) = 2 ∧
      ∃ z : graphExtension F, orderOf z = 2 ∧ z ∈ innerPart F ∧ z ∈ B ∧
        (T : Subgroup _) ≤ centralizer ({z} : Set _) := by
  let := hΩ.1 A hA
  obtain ⟨g, z, hz, hzL, hzB, hBT, hTz⟩ :=
    exists_conjugate_actor_with_sylow_central_involution (innerPart F) T
      (inner_involutions_isConj F ho hF) A hinner
  let f := (MulAut.conj g).toMonoidHom
  let B := A.map f
  have hcardB : Nat.card B = 4 :=
    (card_map_of_injective (MulAut.conj g).injective).trans hfour
  have hmapL : (innerPart F).map f = innerPart F := Normal.conj_smul_eq_self g _
  have hmapinf : (A ⊓ innerPart F).map f = B ⊓ innerPart F := by
    rw [map_inf _ _ f (MulAut.conj g).injective, hmapL]
  have hcardBL : Nat.card (B ⊓ innerPart F : Subgroup _) = 2 := by
    rw [← hmapinf, card_map_of_injective (MulAut.conj g).injective, hinner]
  exact ⟨B, hΩ.2 g A hA, hBT, hcardB, hcardBL, z, hz, hzL, hzB, hTz⟩

/-- A rank-three actor contains every involution centralizing its Sylow. -/
theorem eight_actor_contains_central_involution {p : ℕ}
    (hp : p.Prime) (ho : Odd p) (hF : Nat.card F = p)
    {T : Sylow 2 (graphExtension F)} {A : Subgroup (graphExtension F)}
    [IsElementaryAbelian 2 A] (hAT : A ≤ (T : Subgroup _)) (hcard : Nat.card A = 8)
    {z : graphExtension F} (hz : z ^ 2 = 1)
    (hTz : (T : Subgroup _) ≤ centralizer ({z} : Set _)) : z ∈ A := by
  let : IsElementaryAbelian 2 (zpowers z) := IsElementaryAbelian.zpowers_of_pow_eq_one hz
  have hzC : z ∈ centralizer (A : Set _) := by
    rw [mem_centralizer_iff]
    intro a ha
    exact mem_centralizer_singleton_iff.mp (hTz (hAT ha))
  let : IsElementaryAbelian 2 (A ⊔ zpowers z : Subgroup _) :=
    IsElementaryAbelian.sup_of_le_centralizer (zpowers_le.mpr hzC)
  have hc : Nat.card (A ⊔ zpowers z : Subgroup _) ≤ 8 :=
    (primeRank_le_iff_elementary_card_le _).mp
      (ambient_primeRank_le_three F hp ho hF) _ inferInstance
  have he : A = A ⊔ zpowers z := eq_of_le_of_card_ge le_sup_left (hcard.symm ▸ hc)
  rw [he]
  exact (show zpowers z ≤ A ⊔ zpowers z from le_sup_right) (mem_zpowers z)

/-- An outer eight-group contains an inner involution central in the Sylow. -/
theorem exists_central_inner_involution_of_eight {p : ℕ}
    (hp : p.Prime) (ho : Odd p) (hF : Nat.card F = p)
    {T : Sylow 2 (graphExtension F)} {A : Subgroup (graphExtension F)}
    [IsElementaryAbelian 2 A] (hAT : A ≤ (T : Subgroup _)) (hcard : Nat.card A = 8)
    (hinner : Nat.card (A ⊓ innerPart F : Subgroup _) = 4) :
    ∃ z : graphExtension F, orderOf z = 2 ∧ z ∈ innerPart F ∧ z ∈ A ∧
      (T : Subgroup _) ≤ centralizer ({z} : Set _) := by
  have hd : 2 ∣ Nat.card (innerPart F) := by
    have hh := card_dvd_of_le (show A ⊓ innerPart F ≤ innerPart F from inf_le_right)
    rw [hinner] at hh
    exact dvd_trans (by decide : 2 ∣ 4) hh
  obtain ⟨x, hxC, hx1, hxL⟩ := T.exists_ne_one_mem_center_of_normal (innerPart F) hd
  let n := orderOf x / 2
  have hx2 : orderOf (x ^ n) = 2 :=
    orderOf_pow_orderOf_div (orderOf_pos x).ne' (T.isPGroup'.dvd_orderOf hx1)
  let z : graphExtension F := (x ^ n : T)
  have hz2 : orderOf z = 2 := by simpa only [z, orderOf_coe] using hx2
  have hTz : (T : Subgroup _) ≤ centralizer ({z} : Set _) := by
    intro t ht
    apply mem_centralizer_singleton_iff.mpr
    exact congrArg Subtype.val (mem_center_iff.mp ((center T).pow_mem hxC n) ⟨t, ht⟩)
  exact ⟨z, hz2, (innerPart F).pow_mem hxL n,
    eight_actor_contains_central_involution F hp ho hF hAT hcard
      (hz2 ▸ pow_orderOf_eq_one z) hTz, hTz⟩

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies
