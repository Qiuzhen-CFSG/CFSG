module
public import Theory.Representation.SL2FourNaturalOrbits.SelfDual
public import Theory.SpecificGroups.SL2.UpperUnipotent
public import Theory.Representation.BinaryOffender.CommutatorRank
public import Theory.Representation.BinaryOffender.PermutationConjugacy
import Mathlib.Tactic.FinCases

/-!
# Sylow elements on the binary natural SL₂(4) module

Sylow conjugacy reduces the element calculation to an upper unipotent. Each
nonidentity upper unipotent fixes the same F₄-line, of binary dimension two,
and squares to one. Conjugacy preserves both assertions. The only finite
checks involve the four explicit upper matrices.

This supplies the model input to the characteristic-two specialization of
Niles, *Pushing-up in finite groups* (1979), Lemma 3.4, printed pp.37–39.
-/

public section
noncomputable section
namespace Representation.SL2FourNaturalExtensions
open Subgroup Matrix.SpecialLinearGroup Representation.BinaryOffender SL2FourNatural

private theorem upper_eq_transvection (a : F) :
    upper a = transvection (i := (0 : Fin 2)) (j := 1) zero_ne_one a := by
  apply Subtype.ext
  funext i j
  fin_cases i <;> fin_cases j <;> simp [upper, transvection_coe]

private theorem upper_square : ∀ a : F, upper a ^ 2 = 1 := by decide +kernel

private theorem upper_zero : upper (0 : F) = 1 := by decide +kernel

private theorem upper_fixed_space {a : F} (ha : a ≠ 0) :
    fixedSpace naturalRepresentation (zpowers (upper a)) = upperFixed := by
  ext v
  rw [mem_fixedSpace_zpowers_iff, naturalRepresentation_apply, mem_upperFixed]
  constructor
  · intro h
    have he := congrFun h 0
    simpa [upper_action, ha] using he
  · intro hv
    rw [upper_action]
    funext i
    fin_cases i <;> simp [hv]

private theorem upper_fixedCodim {a : F} (ha : a ≠ 0) :
    fixedCodim naturalRepresentation (zpowers (upper a)) = 2 := by
  have hd : Module.finrank (ZMod 2) upperFixed = 2 := by
    have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := upperFixed)
    rw [card_upperFixed, Nat.card_eq_fintype_card, ZMod.card] at hc
    exact (Nat.pow_right_injective (by decide : 1 < (2 : ℕ)) hc).symm
  have hh := fixedCodim_add_finrank naturalRepresentation (zpowers (upper a))
  rw [upper_fixed_space ha, hd, finrank_vector] at hh
  omega

/-- Every element of a natural Sylow two-subgroup squares to one, and each
nonidentity element moves exactly two binary dimensions. -/
theorem sylow_element_natural (P : Sylow 2 SL) {g : SL} (hg : g ∈ P) :
    g ^ 2 = 1 ∧ (g ≠ 1 → fixedCodim naturalRepresentation (zpowers g) = 2) := by
  obtain ⟨c, rfl⟩ := MulAction.exists_smul_eq SL (upperUnipotentSylow F 2) P
  have hm : ∃ b ∈ upperUnipotent F, c * b * c⁻¹ = g := by
    change g ∈ ((c • upperUnipotentSylow F 2 : Sylow 2 SL) : Subgroup SL) at hg
    rw [Sylow.coe_subgroup_smul] at hg
    exact hg
  obtain ⟨b, hb, rfl⟩ := hm
  obtain ⟨a, rfl⟩ := (mem_upperUnipotent F b).mp hb
  rw [← upper_eq_transvection]
  refine ⟨?_, ?_⟩
  · simpa using congrArg (MulAut.conj c) (upper_square a)
  · intro hn
    have ha : a ≠ 0 := by
      intro h
      simp [h, upper_zero] at hn
    have hc := fixedCodim_map_conj naturalRepresentation (zpowers (upper a)) c
    rw [MonoidHom.map_zpowers] at hc
    exact hc.trans (upper_fixedCodim ha)

end Representation.SL2FourNaturalExtensions
