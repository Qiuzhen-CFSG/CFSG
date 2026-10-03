module

public import Theory.GroupTheory.PGroup.NormalEightFour
public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import Theory.ElementaryAbelian.Join

/-!
# Normalizer growth around two commuting elementary subgroups

Let `A` be normal in a finite two-group and commute with an elementary
subgroup `B`. If their join is the first omega of its centralizer, and is
too large to be normal, the normalizer condition supplies a conjugate of
`B` which normalizes the join but does not centralize it. It still
centralizes `A`, since `A` is normal. Centrality of `A` is not required.

This is the normalizer-growth step in Janko–Thompson, Math. Z. 113 (1970),
Lemma 5.1, printed p.394, in the form needed for its reuse on p.395.
The local omega identity is explicit; no inheritance of the absence of
normal elementary eights to arbitrary subgroups is asserted.
-/

namespace Subgroup

open scoped Pointwise

/-- A normalizer-tower step produces a conjugate acting nontrivially on the
join, while continuing to centralize its normal factor. -/
public theorem exists_conjugate_normalizing_sup_not_centralizing
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hno : ¬ ∃ D : Subgroup P, D.Normal ∧ IsElementaryAbelian 2 D ∧ 8 ≤ Nat.card D)
    (A B : Subgroup P) [A.Normal]
    [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 B]
    (hBA : B ≤ centralizer (A : Set P)) (hlarge : 8 ≤ Nat.card (A ⊔ B : Subgroup P))
    (hOmega : (omega₁ (centralizer ((A ⊔ B : Subgroup P) : Set P)) (p := 2)).map
      (centralizer ((A ⊔ B : Subgroup P) : Set P)).subtype = A ⊔ B) :
    ∃ s : P,
      B.map (MulAut.conj s).toMonoidHom ≤ normalizer ((A ⊔ B : Subgroup P) : Set P) ∧
      B.map (MulAut.conj s).toMonoidHom ≤ centralizer (A : Set P) ∧
      ¬ B.map (MulAut.conj s).toMonoidHom ≤
        centralizer ((A ⊔ B : Subgroup P) : Set P) := by
  let E := A ⊔ B
  let Y := centralizer (E : Set P)
  let N := normalizer (Y : Set P)
  change (omega₁ Y (p := 2)).map Y.subtype = E at hOmega
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.sup_of_le_centralizer hBA
  have hEY : E ≤ Y := E.le_centralizer
  have hNY : N = normalizer (E : Set P) := by
    apply le_antisymm
    · let : (omega₁ Y (p := 2)).Characteristic := omega₁_characteristic Y
      have hn := normalizer_le_normalizer_characteristic_image Y (omega₁ Y (p := 2))
      rwa [hOmega] at hn
    · exact normalizer_le_normalizer_centralizer E
  have hNproper : N < ⊤ := by
    apply lt_top_iff_ne_top.mpr
    intro hN
    exact hno ⟨E, normalizer_eq_top_iff.mp (hNY.symm.trans hN), inferInstance, hlarge⟩
  let : Group.IsNilpotent P := hP.isNilpotent
  obtain ⟨s, hs, hsN⟩ :=
    SetLike.exists_of_lt (Group.normalizerCondition_of_isNilpotent N hNproper)
  let f := (MulAut.conj s).toMonoidHom
  have hAf : A.map f = A :=
    mem_normalizer_iff_map_conj_eq.mp (A.normalizer_eq_top ▸ mem_top s)
  have hBN : B ≤ N := (le_sup_right.trans hEY).trans Y.le_normalizer
  have hVN : B.map f ≤ N := by
    rintro _ ⟨b, hb, rfl⟩
    exact (mem_normalizer_iff.mp hs b).mp (hBN hb)
  refine ⟨s, hNY ▸ hVN, ?_, ?_⟩
  · rintro _ ⟨b, hb, rfl⟩ a ha
    obtain ⟨a', ha', rfl⟩ := show a ∈ A.map f from hAf.symm ▸ ha
    simpa only [map_mul] using congrArg f (hBA hb a' ha')
  · intro hVY
    have hVE : B.map f ≤ E := by
      intro v hv
      rw [← hOmega]
      refine ⟨⟨v, hVY hv⟩, subset_closure ?_, rfl⟩
      apply Subtype.ext
      change v ^ (2 ^ 1) = 1
      let : IsElementaryAbelian 2 (B.map f) := IsElementaryAbelian.map _
      simpa using elemPow_eq_one_of_isElementaryAbelian (p := 2) v hv
    have hEf : E.map f ≤ E := by
      change (A ⊔ B).map f ≤ E
      rw [Subgroup.map_sup, hAf]
      exact sup_le le_sup_left hVE
    have heq : E.map f = E := eq_of_le_of_card_ge hEf (by
      rw [card_map_of_injective (MulAut.conj s).injective])
    exact hsN (hNY ▸ mem_normalizer_iff_map_conj_eq.mpr heq)

end Subgroup
