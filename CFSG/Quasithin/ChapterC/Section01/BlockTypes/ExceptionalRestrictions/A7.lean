module
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.ExceptionalRestrictions.Conjugation
public import Theory.Representation.BinaryAlternatingSevenCohomology
public import Theory.Representation.FactorDegreeFiltration.FiniteDual
public import Theory.Representation.Quotient
public import Theory.Representation.SpecialLinearRestriction

/-!
# The exceptional A₇ natural restriction

The literal projection U → U/C_U(L) is a central cover. Its kernel is bounded
by H¹ of the contragredient four-dimensional irreducible module. I.1.6(8)
applies to every such A₇ module, so the kernel vanishes. Coordinates on U then
produce the faithful SL₄(F₂) restriction asserted after Definition C.1.22,
Aschbacher--Smith, printed p.129.
-/

public section
open Subgroup Representation Representation.OneCohomology
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC
open ExceptionalRestrictions
variable {L : Type*} [Group L]

/-- The actual quotient module has binary dimension four. -/
theorem IsExceptionalA7Block.module_finrank (h : IsExceptionalA7Block L) :
    letI := h.1.module_elementary
    Module.finrank (ZMod 2) (Additive (BlockModule L)) = 4 := by
  let := h.1.finite
  let := h.1.module_elementary
  apply Nat.pow_right_injective (by decide : 1 < 2)
  calc
    2 ^ Module.finrank (ZMod 2) (Additive (BlockModule L)) =
        Nat.card (Additive (BlockModule L)) := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
    _ = 2 ^ 4 := h.2.2

/-- I.1.6(8) applies to the dual of the genuine quotient representation. -/
theorem IsExceptionalA7Block.dual_H1_eq_zero (h : IsExceptionalA7Block L) :
    letI := h.1.elementary
    letI := h.1.module_elementary
    Module.finrank (ZMod 2) (H1 (moduleRepresentation h.1).dual) = 0 := by
  let := h.1.finite
  let := h.1.elementary
  let := h.1.module_elementary
  let ρ := moduleRepresentation h.1
  let := moduleRepresentation_irreducible h.1
  let : IsIrreducible ρ.dual := Representation.isIrreducible_dual
  obtain ⟨e⟩ := h.2.1
  let σ := ρ.dual.comp e.symm.toMonoidHom
  let : IsIrreducible σ :=
    (irreducible_comp_surjective_iff e.symm.toMonoidHom e.symm.surjective ρ.dual).mpr
      inferInstance
  have hd : Module.finrank (ZMod 2) (Module.Dual (ZMod 2) (Additive (BlockModule L))) = 4 := by
    rw [Subspace.dual_finrank_eq, h.module_finrank]
  have hz := binaryAlternatingSeven_finrank_H1_eq_zero_of_irreducible_four σ hd
  have he := H1Congr ρ.dual σ e (LinearEquiv.refl (ZMod 2) _) (by
    intro g v
    change ρ.dual g v = ρ.dual (e.symm (e g)) v
    rw [e.symm_apply_apply])
  exact he.finrank_eq.trans hz

/-- The fixed layer vanishes; this is a consequence, not a defining assumption. -/
theorem IsExceptionalA7Block.fixed_eq_bot (h : IsExceptionalA7Block L) : blockFixed L = ⊥ := by
  let := h.1.finite
  let := h.1.elementary
  let := h.1.module_elementary
  have hb := finrank_ker_le_H1_of_cover (projection h.1) (projection_isCover h.1)
  rw [h.dual_H1_eq_zero] at hb
  have hk : (moduleProjection (L := L)).ker = ⊥ :=
    Submodule.finrank_eq_zero.mp (Nat.eq_zero_of_le_zero hb)
  apply le_bot_iff.mp
  intro u hu
  have hv : Additive.ofMul u ∈ (moduleProjection (L := L)).ker :=
    (QuotientGroup.eq_one_iff _).mpr hu
  rw [hk] at hv
  exact hv

/-- The original U, as well as its central quotient, has order sixteen. -/
theorem IsExceptionalA7Block.u_card (h : IsExceptionalA7Block L) : Nat.card (blockU L) = 16 := by
  let e : BlockModule L ≃* blockU L :=
    (QuotientGroup.quotientMulEquivOfEq h.fixed_eq_bot).trans QuotientGroup.quotientBot
  exact (Nat.card_congr e.toEquiv).symm.trans h.module_card

/-- The actual quotient embeds in SL₄(F₂), and its restricted natural module is U. -/
theorem IsExceptionalA7Block.natural_restriction (h : IsExceptionalA7Block L) :
    letI := h.1.elementary
    ∃ (f : (L ⧸ pCore 2 L) →* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2))
      (e : Additive (blockU L) ≃ₗ[ZMod 2] (Fin 4 → ZMod 2)),
      Function.Injective f ∧ ∀ (l : L) (u : blockU L),
        e (Additive.ofMul (blockConjugate L l u)) =
          specialLinearNatural 4 (f (QuotientGroup.mk' (pCore 2 L) l)) (e (Additive.ofMul u)) := by
  let := h.1.finite
  let := h.1.elementary
  let := h.1.module_elementary
  obtain ⟨a⟩ := h.2.1
  let : Group.IsPerfect (alternatingGroup (Fin 7)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  let : Group.IsPerfect (L ⧸ pCore 2 L) := Group.IsPerfect.ofSurjective (f := a.symm.toMonoidHom) a.symm.surjective
  let σ := (moduleRepresentation h.1).comp a.symm.toMonoidHom
  let : IsIrreducible σ :=
    (irreducible_comp_surjective_iff a.symm.toMonoidHom a.symm.surjective _).mpr
      (moduleRepresentation_irreducible h.1)
  have hi := binaryAlternatingSeven_faithful_of_irreducible_four σ h.module_finrank
  have hf : Function.Injective (uRepresentation h.1) := by
    intro g j he
    apply a.injective
    apply hi
    apply LinearMap.ext
    intro w
    obtain ⟨v, rfl⟩ := moduleProjection_surjective w
    change moduleRepresentation h.1 (a.symm (a g)) (moduleProjection v) =
      moduleRepresentation h.1 (a.symm (a j)) (moduleProjection v)
    rw [a.symm_apply_apply, a.symm_apply_apply, ← moduleProjection_equivariant,
      ← moduleProjection_equivariant, he]
  have hd : Module.finrank (ZMod 2) (Additive (blockU L)) = 4 := by
    apply Nat.pow_right_injective (by decide : 1 < 2)
    calc
      2 ^ Module.finrank (ZMod 2) (Additive (blockU L)) = Nat.card (Additive (blockU L)) := by
        rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
      _ = Nat.card (blockU L) := Nat.card_congr Additive.toMul
      _ = 2 ^ 4 := h.u_card
  obtain ⟨f, e, hf, he⟩ := exists_specialLinear_restriction (uRepresentation h.1) hf
    (det_eq_one_of_perfect _) hd
  exact ⟨f, e, hf, fun l u => he (QuotientGroup.mk' (pCore 2 L) l) (Additive.ofMul u)⟩
end CFSG.Quasithin.ChapterC
