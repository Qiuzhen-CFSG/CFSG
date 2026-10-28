module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.PureTwoA.NativePairApplication
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.Mathieu.NormalFour
public import Theory.GroupTheory.QuasithinBasic
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.PureTwoA.MathieuPureNormal

/-!
# Eliminating the marked pair at maximal TWO-local level

The native pair has order four and its whole normalizer lies in max1. A
normal elementary subgroup of max1 cannot have order four. More generally,
the trivial-image extension cannot be a maximal TWO-local normalizer when
the extension is pure first-class: the certified binary-kernel orbits exclude
such a nontrivial normal subgroup of max1. The same exclusion holds under
literal ambient conjugation. If a larger maximal pure normalizer actually
normalizes a four-subgroup, the same exclusion leaves only census row two
for that four-subgroup, with its full centralizer and normalizer transported
by the same conjugator.

This is a local branch of Kleidman--Wilson (1988), Section 2.1,
pp.488--489. It does not assert that an arbitrary larger pure group has a
normalized four-subgroup, nor identify the native row with a printed MOG type.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Janko4.LocalStructure.ElementaryNormalizerCover.PureTwoA.NativePair
open LinearFive InvolutionCentralizers.Second
attribute [local irreducible] modelGroup matrixA matrixB Cardinality.max1Subgroup Cardinality.localKernel
set_option backward.isDefEq.respectTransparency true

theorem nativePair_card : Nat.card nativePair = 4 := by
  have hx : orderOf (kernelValue 818 : Model) = 2 :=
    by
      obtain ⟨g,hg⟩ := isConj_iff.mp first_is_first
      rw [← hg]
      exact ((MulAut.conj g).orderOf_eq a).trans orderOf_a
  have hy : orderOf (kernelValue 1449 : Model) = 2 :=
    by
      obtain ⟨g,hg⟩ := isConj_iff.mp second_is_first
      rw [← hg]
      exact ((MulAut.conj g).orderOf_eq a).trans orderOf_a
  have hne : (kernelValue 818 : Model) ≠ (kernelValue 1449 : Model) := by
    intro he
    have h := kernelValue_injective (by decide : 818 < 2048) (by decide : 1449 < 2048)
      (Subtype.ext he)
    omega
  exact (isKleinFour_closure_pair_of_orderOf _ _ hx hy hne
    ((kernelValue_commute 818 1449).map M.subtype)).card_four

theorem normalizer_not_maximal : ¬ IsMaximalTwoLocal (normalizer (nativePair : Set Model)) := by
  intro hmax
  have he : normalizer (nativePair : Set Model) = max1 :=
    hmax.eq_of_le embedded_localKernel_isTwoLocal normalizer_le_max1
  let : (nativePair.subgroupOf M).Normal :=
    (normal_subgroupOf_iff_le_normalizer nativePair_le_max1).mpr he.ge
  apply max1_normal_card_ne_four (nativePair.subgroupOf M)
  rw [Nat.card_congr (subgroupOfEquivOfLe nativePair_le_max1).toEquiv, nativePair_card]

theorem row_seven_not_maximal :
    ¬ IsMaximalTwoLocal (normalizer (firstFourGroup 7 : Set Model)) := by
  intro hmax
  obtain ⟨g,_,_,hn⟩ := row_seven_geometry
  apply normalizer_not_maximal
  rw [hn]
  exact isMaximalTwoLocal_map (MulAut.conj g) hmax

/-- At maximal TWO-local level the literal Mathieu image of a pure extension is nontrivial. -/
theorem maximal_pure_extension_image_ne_bot (X : Subgroup Model)
    [IsElementaryAbelian 2 X] (hpair : nativePair ≤ X)
    (hpure : ∀ x ∈ X, x ≠ 1 → IsConj a x)
    (hmax : IsMaximalTwoLocal (normalizer (X : Set Model))) :
    (X.subgroupOf M).map starHom ≠ ⊥ := by
  intro himage
  have hne : X ≠ ⊥ := by
    intro hbot
    have hP : nativePair = ⊥ := le_bot_iff.mp (hbot ▸ hpair)
    have hc := nativePair_card
    rw [hP,card_bot] at hc
    omega
  exact pure_normalizer_not_maximal_of_le_max1 X hne hpure
    (trivial_image_normalizer X hpair himage) hmax

/-- Conjugated kernel extensions cannot be maximal pure-first normalizers. -/
theorem marked_kernel_pure_extension_not_maximal (X : Subgroup Model)
    [IsElementaryAbelian 2 X] (g : Model)
    (hpair : nativePair.map (MulAut.conj g).toMonoidHom ≤ X)
    (hkernel : X ≤ embeddedKernel.map (MulAut.conj g).toMonoidHom)
    (hpure : ∀ x ∈ X, x ≠ 1 → IsConj a x) :
    ¬ IsMaximalTwoLocal (normalizer (X : Set Model)) := by
  have hne : X ≠ ⊥ := by
    intro hbot
    have hP0 : nativePair.map (MulAut.conj g).toMonoidHom = ⊥ :=
      le_bot_iff.mp (hbot ▸ hpair)
    have hP := (map_eq_bot_iff_of_injective nativePair (MulAut.conj g).injective).mp hP0
    have hc := nativePair_card
    rw [hP,card_bot] at hc
    omega
  exact pure_normalizer_not_maximal_of_mathieu_containment X hne hpure g
    (marked_kernel_extension_normalizer X g hpair hkernel)

private theorem map_conj_mul (A : Subgroup Model) (g k : Model) :
    (A.map (MulAut.conj k).toMonoidHom).map (MulAut.conj g).toMonoidHom =
      A.map (MulAut.conj (g*k)).toMonoidHom := by
  rw [map_map]
  congr 1
  ext x
  simp [mul_assoc]

/-- Whole-normalizer placement for row seven, with a literal ambient conjugator. -/
theorem row_seven_normalizer_placement :
    ∃ k : Model, normalizer (firstFourGroup 7 : Set Model) ≤
      max1.map (MulAut.conj k).toMonoidHom := by
  obtain ⟨g,_,_,hn⟩ := row_seven_geometry
  refine ⟨g⁻¹,?_⟩
  have ht := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) normalizer_le_max1
  rw [hn,map_conj_mul,inv_mul_cancel] at ht
  have h1 : (MulAut.conj (1 : Model)).toMonoidHom = MonoidHom.id Model := by
    ext x; simp
  rwa [h1,map_id] at ht

/-- A pure maximal TWO-local normalizer cannot normalize a row-seven four-group. -/
theorem maximal_pure_not_normalize_row_seven (X : Subgroup Model)
    [IsElementaryAbelian 2 X] (hne : X ≠ ⊥)
    (hpure : ∀ x ∈ X, x ≠ 1 → IsConj a x)
    (hmax : IsMaximalTwoLocal (normalizer (X : Set Model))) (g : Model) :
    ¬ normalizer (X : Set Model) ≤
      (normalizer (firstFourGroup 7 : Set Model)).map (MulAut.conj g).toMonoidHom := by
  intro hN
  obtain ⟨k,hk⟩ := row_seven_normalizer_placement
  have ht := map_mono (f := (MulAut.conj g).toMonoidHom) hk
  rw [map_conj_mul] at ht
  exact pure_normalizer_not_maximal_of_mathieu_containment X hne hpure (g*k)
    (hN.trans ht) hmax

/-- If a maximal pure normalizer actually normalizes a pure four-subgroup,
only census row two survives. No existence of such a four-subgroup is assumed. -/
theorem normalized_four_row_two (X Y : Subgroup Model)
    [IsElementaryAbelian 2 X] [IsElementaryAbelian 2 Y]
    (hcard : Nat.card Y = 4) (hYX : Y ≤ X)
    (hpure : ∀ x ∈ X, x ≠ 1 → IsConj a x)
    (hmax : IsMaximalTwoLocal (normalizer (X : Set Model)))
    (hN : normalizer (X : Set Model) ≤ normalizer (Y : Set Model)) :
    ∃ g : Model,
      Y = (firstFourGroup 2).map (MulAut.conj g).toMonoidHom ∧
      centralizer (Y : Set Model) =
        (centralizer (firstFourGroup 2 : Set Model)).map (MulAut.conj g).toMonoidHom ∧
      normalizer (Y : Set Model) =
        (normalizer (firstFourGroup 2 : Set Model)).map (MulAut.conj g).toMonoidHom := by
  have hne : X ≠ ⊥ := by
    intro hbot
    have hYbot : Y = ⊥ := le_bot_iff.mp (hbot ▸ hYX)
    rw [hYbot,card_bot] at hcard
    omega
  obtain ⟨i,g,hi,hY,hC,hNY⟩ := pure_first_four_group_geometry Y hcard
    (fun y hy hy1 => hpure y (hYX hy) hy1)
  rcases hi with rfl | rfl
  · exact ⟨g,hY,hC,hNY⟩
  · exact (maximal_pure_not_normalize_row_seven X hne hpure hmax g
      (hNY ▸ hN)).elim


end Janko4.LocalStructure.ElementaryNormalizerCover.PureTwoA.NativePair
