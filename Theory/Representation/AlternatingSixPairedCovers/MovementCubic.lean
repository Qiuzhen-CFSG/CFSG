module
public import Theory.Representation.BinaryAlternatingSixModels
public import Theory.Representation.BinaryPermutation.SixPolar
public import Theory.Representation.BinaryOffender.CommutatorRank

/-!
# Cubic separation of the two marked A₆ covers

A three-cycle fixes a three-space in the augmentation core, so its movement
has dimension two. Its exceptional image is a product of two three-cycles;
that permutation fixes no duad and hence no nonzero vector of the natural
four-space. Conjugation by the alignment in diagramAut preserves this rank.
The finite certificate counts only the 64 binary six-tuples in the core
calculation; the natural calculation uses the existing duad bijection.

Source: Aschbacher–Smith 14.6.22(1) and 14.6.24(2), printed pp.1038,1041.
This separates the actual covers without assuming their intersection is zero.
-/

public section
open Representation Representation.BinaryOffender BinaryPermutation Subgroup
open Theory.SpecificGroups.SymmetricSix
namespace AlternatingSixPairedCovers

private noncomputable def coreFixedEquiv :
    fixedSpace (coreRepresentation (Fin 6)) (zpowers GLS3.Chapter5.threeCyclePerm) ≃
      {v : Fin 6 → ZMod 2 // (∑ i, v i) = 0 ∧
        representation (Fin 6) GLS3.Chapter5.threeCyclePerm v = v} where
  toFun v := ⟨v.val.val, v.val.property,
    congrArg Subtype.val ((mem_fixedSpace_zpowers_iff _ _ _).mp v.property)⟩
  invFun v := ⟨⟨v.val,v.property.1⟩,
    (mem_fixedSpace_zpowers_iff _ _ _).mpr (Subtype.ext v.property.2)⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- A three-cycle moves two dimensions of the five-dimensional cover. -/
theorem core_threeCycle_fixedCodim :
    fixedCodim (coreRepresentation (Fin 6)) (zpowers GLS3.Chapter5.threeCyclePerm) = 2 := by
  have hc : Nat.card (fixedSpace (coreRepresentation (Fin 6))
      (zpowers GLS3.Chapter5.threeCyclePerm)) = 8 := by
    rw [Nat.card_congr coreFixedEquiv, Nat.card_eq_fintype_card]
    decide +kernel
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod] at hc
  have hf : Module.finrank (ZMod 2) (fixedSpace (coreRepresentation (Fin 6))
      (zpowers GLS3.Chapter5.threeCyclePerm)) = 3 :=
    Nat.pow_right_injective (by decide : 1 < (2 : ℕ)) hc
  have h := fixedCodim_add_finrank (coreRepresentation (Fin 6))
    (zpowers GLS3.Chapter5.threeCyclePerm)
  rw [hf, finrank_core] at h
  norm_num at h
  omega

private def doubleCycle : Equiv.Perm (Fin 6) :=
  (Equiv.swap 0 3 * Equiv.swap 0 4) * (Equiv.swap 1 5 * Equiv.swap 1 2)

private theorem doubleThree_no_fixed (v : NaturalModule)
    (hv : polarAction doubleCycle v = v) : v = 0 := by
  by_contra hn
  obtain ⟨d,hd⟩ := polarVector_bijective.2 ⟨v,hn⟩
  have he : (polarVector d).val = v := congrArg Subtype.val hd
  rw [←he, polarAction_vector] at hv
  have hd' : doubleCycle • d = d :=
    polarVector_injective (Subtype.ext hv)
  have hh := congrArg duadSet hd'
  rw [duadSet_smul] at hh
  have hne : ∀ d : Duad,
      (duadSet d).image doubleCycle ≠ duadSet d := by
    decide +kernel
  exact hne d hh

/-- The exceptional image of the same three-cycle has no natural fixed vector. -/
private theorem natural_doubleCycle_fixedCodim :
    fixedCodim (naturalRepresentation (Fin 6))
      (zpowers doubleCycle) = 4 := by
  have hz : fixedSpace (naturalRepresentation (Fin 6))
      (zpowers doubleCycle) = ⊥ := by
    apply le_antisymm _ bot_le
    intro v hv
    have he : polarAction doubleCycle
        (PolarNatural.equiv.symm v) = PolarNatural.equiv.symm v := by
      apply PolarNatural.equiv.injective
      rw [PolarNatural.equiv_action, PolarNatural.equiv.apply_symm_apply]
      exact (mem_fixedSpace_zpowers_iff _ _ _).mp hv
    have hh := doubleThree_no_fixed _ he
    exact PolarNatural.equiv.symm.map_eq_zero_iff.mp hh
  have h := fixedCodim_add_finrank (naturalRepresentation (Fin 6))
    (zpowers doubleCycle)
  rw [hz, finrank_bot, add_zero, finrank_natural_even (Fin 6) (by decide)] at h
  exact h

/-- Both three-cycles in the exceptional image act without natural fixed vectors. -/
theorem natural_doubleThree_fixedCodim :
    fixedCodim (naturalRepresentation (Fin 6))
      (zpowers GLS3.Chapter5.doubleThreeCyclePerm) = 4 := by
  have hc : IsConj GLS3.Chapter5.doubleThreeCyclePerm doubleCycle := by
    apply Equiv.Perm.isConj_iff_cycleType_eq.mpr
    rw [GLS3.Chapter5.doubleThreeCyclePerm_cycleType]
    decide +kernel
  obtain ⟨c,hc⟩ := isConj_iff.mp hc
  have hh := natural_doubleCycle_fixedCodim
  rw [←hc,fixedCodim_zpowers_conj] at hh
  exact hh

/-- The aligned diagram automorphism retains the four-dimensional movement. -/
theorem natural_diagram_threeCycle_fixedCodim :
    fixedCodim (naturalRepresentation (Fin 6))
      (zpowers (BinaryAlternatingSix.diagramAut GLS3.Chapter5.threeCyclePerm)) = 4 := by
  have he : BinaryAlternatingSix.diagramAut GLS3.Chapter5.threeCyclePerm =
      BinaryAlternatingSix.align * GLS3.Chapter5.doubleThreeCyclePerm *
        BinaryAlternatingSix.align⁻¹ := by
    change BinaryAlternatingSix.align * GLS3.Chapter5.outerHom
      GLS3.Chapter5.threeCyclePerm * BinaryAlternatingSix.align⁻¹ = _
    rw [GLS3.Chapter5.outerHom_threeCyclePerm_eq_doubleThreeCyclePerm]
  rw [he, fixedCodim_zpowers_conj, natural_doubleThree_fixedCodim]

end AlternatingSixPairedCovers
