module

public import ABG.ChapterII.Section1.RegularWreathHeightTwo
public import ABG.ChapterII.Section1.WreathedCenter
public import ABG.ChapterII.Section2.SylowShapeTransport
public import Theory.GroupTheory.SylowCoprimeEquivalence
public import Theory.GroupTheory.DihedralEightSections

/-!
# Concrete invariants of C₄ wreath C₂

The regular wreath model has order 32, center of order four, and every
element has eighth power one. Its center calculation also proves that it
is noncommutative. These invariants pass through a section using the full
ambient two-part: the Sylow inclusion and quotient maps are then bijective.
This supplies structural tests for the degree-three branch of F.6.18.
-/

public noncomputable section
open Subgroup
namespace Theory.GroupTheory

abbrev WreathedThirtyTwo := RegularWreathProduct
  (Multiplicative (ZMod 4)) (Multiplicative (ZMod 2))

theorem wreathedThirtyTwo_card : Nat.card WreathedThirtyTwo = 32 := by
  rw [RegularWreathProduct.card]
  norm_num

theorem wreathedThirtyTwo_pow_eight (g : WreathedThirtyTwo) : g ^ 8 = 1 := by
  rcases g with ⟨f, b⟩
  ext q
  · revert q b f
    decide
  · revert b f
    decide

theorem wreathedThirtyTwo_center_card : Nat.card (center WreathedThirtyTwo) = 4 := by
  obtain ⟨P⟩ := ABG.Wreathed.nonempty_presentation ABG.RegularWreathHeightTwo.isWreathedOfHeight
  exact P.card_center

theorem wreathedThirtyTwo_not_commutative : ¬ IsMulCommutative WreathedThirtyTwo := by
  intro h
  have hc := center_eq_top_iff.mpr h
  have hh := wreathedThirtyTwo_center_card
  rw [hc, Nat.card_congr (topEquiv : (⊤ : Subgroup WreathedThirtyTwo) ≃*
    WreathedThirtyTwo).toEquiv, wreathedThirtyTwo_card] at hh
  norm_num at hh

/-- Full use of the ambient Sylow order makes both section maps bijective. -/
theorem sylow_equiv_of_section_card_eq
    {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]
    (T : Sylow 2 G) (K : Subgroup G) (f : K →* H) (hf : Function.Surjective f)
    (P : Sylow 2 H) (hcard : Nat.card P = Nat.card T) : Nonempty (T ≃* P) := by
  obtain ⟨S, hS⟩ := Sylow.mapSurjective_surjective hf 2 P
  let eQ : ((S : Subgroup K).map f) ≃* P :=
    MulEquiv.subgroupCongr (congrArg Sylow.toSubgroup hS)
  let q : S →* P := eQ.toMonoidHom.comp (f.subgroupMap (S : Subgroup K))
  have hq : Function.Surjective q :=
    eQ.surjective.comp (f.subgroupMap_surjective (S : Subgroup K))
  obtain ⟨U, hU⟩ := (S.isPGroup'.map K.subtype).exists_le_sylow
  let i : S →* U := (Subgroup.inclusion hU).comp
    (K.subtype.subgroupMap (S : Subgroup K))
  have hi : Function.Injective i := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun u : U => (u : G)) h
  have hUc : Nat.card U = Nat.card T := Nat.card_congr (U.equiv T).toEquiv
  have hSc : Nat.card S = Nat.card T := by
    apply le_antisymm
    · exact (Nat.card_le_card_of_injective i hi).trans_eq hUc
    · exact hcard ▸ Nat.card_le_card_of_surjective q hq
  let eq : S ≃* P := MulEquiv.ofBijective q
    ((Nat.bijective_iff_surjective_and_card q).mpr ⟨hq, hSc.trans hcard.symm⟩)
  let ei : S ≃* U := MulEquiv.ofBijective i
    ((Nat.bijective_iff_injective_and_card i).mpr ⟨hi, hSc.trans hUc.symm⟩)
  exact ⟨((T.equiv U).trans ei.symm).trans eq⟩

/-- The genuine section inherits the wreathed invariants when it retains
all 32 elements of a Sylow subgroup. -/
theorem wreathedThirtyTwo_section_invariants
    {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]
    (T : Sylow 2 G) (eT : T ≃* WreathedThirtyTwo)
    (K : Subgroup G) (f : K →* H) (hf : Function.Surjective f)
    (P : Sylow 2 H) (hP : Nat.card P = 32) :
    (∀ x : P, x ^ 8 = 1) ∧ ¬ IsMulCommutative P := by
  have hT : Nat.card T = 32 := (Nat.card_congr eT.toEquiv).trans wreathedThirtyTwo_card
  obtain ⟨e⟩ := sylow_equiv_of_section_card_eq T K f hf P (hP.trans hT.symm)
  let a : P ≃* WreathedThirtyTwo := e.symm.trans eT
  refine ⟨fun x => a.injective ?_, ?_⟩
  · simpa only [map_pow, map_one] using wreathedThirtyTwo_pow_eight (a x)
  · intro h
    apply wreathedThirtyTwo_not_commutative
    exact isMulCommutative_iff.mpr fun x y => a.symm.injective (by
      simpa only [map_mul] using (isMulCommutative_iff.mp h) (a.symm x) (a.symm y))

end Theory.GroupTheory
