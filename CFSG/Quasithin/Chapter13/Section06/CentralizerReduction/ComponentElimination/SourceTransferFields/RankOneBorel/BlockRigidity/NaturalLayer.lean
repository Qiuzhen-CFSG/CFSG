module

public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Basic
public import Theory.Representation.HigherFieldBorelFixedSpaces.Natural

/-!
# Borel fixation on the actual block module

The equivariant quotient model makes the natural plane faithful. A nonidentity
Borel diagonal fixes only zero, so a Borel-fixed element of U(K) belongs to
C_U(K). Both arguments use the very same quotient and module isomorphisms.
The inverse image of the marked Borel has odd index when it contains O₂(K).

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, C.1.7 and
the final block-action step of 13.6.18, printed p.931 (PDF p.948).
-/

public section
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.BlockRigidity
open Subgroup ChapterC Matrix Matrix.SpecialLinearGroup
open Representation.HigherFieldBorelFixedSpaces
open scoped MatrixGroups

variable {K F : Type*} [Group K] [Field F] [Finite F]
variable (ρ : SL(2,F) →* MulAut (Multiplicative (Fin 2 → F)))
variable (model : BlockModuleModel K ρ)
variable (hρ : ∀ (g : SL(2,F)) (v : Multiplicative (Fin 2 → F)),
    Multiplicative.toAdd (ρ g v) = g.val *ᵥ Multiplicative.toAdd v)

include hρ in
/-- A fixed element of U has zero image in the genuine natural quotient. -/
theorem borel_centralizer_blockU_le_center (B : Subgroup K)
    (hB : B.map (model.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))) =
      rankOneBorel F) (hF : 2 < Nat.card F) :
    blockU K ⊓ centralizer (B : Set K) ≤ center K := by
  intro u hu
  let u' : blockU K := ⟨u, hu.1⟩
  let w := model.moduleIso (QuotientGroup.mk' (blockFixed K) u')
  obtain ⟨d, hd⟩ := large_field_unit hF
  have hdB : diag2 (d : F) d.ne_zero ∈
      B.map (model.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))) := by
    rw [hB]
    exact diag_mem_rankOneBorel _ _
  obtain ⟨b, hb, he⟩ := hdB
  have hfix : blockConjugate K b u' = u' := by
    apply Subtype.ext
    change b * u * b⁻¹ = u
    rw [mem_centralizer_iff.mp hu.2 b hb, mul_inv_cancel_right]
  have hw := model.intertwining b u'
  rw [hfix] at hw
  have hw' := congrArg Multiplicative.toAdd hw.symm
  rw [hρ] at hw'
  change (model.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K)) b).val
    *ᵥ Multiplicative.toAdd w = Multiplicative.toAdd w at hw'
  rw [he] at hw'
  have hzero := diagonal_two_fixed_eq_zero d hd (Multiplicative.toAdd w) hw'
  have hone : w = 1 := Multiplicative.toAdd.injective hzero
  have hq : QuotientGroup.mk' (blockFixed K) u' = 1 :=
    model.moduleIso.injective (hone.trans model.moduleIso.map_one.symm)
  exact (QuotientGroup.eq_one_iff u').mp hq

omit [Finite F] in
include model hρ in
/-- Faithfulness of the prescribed natural representation detects the two-core. -/
theorem centralizer_blockU_le_core : centralizer (blockU K : Set K) ≤ pCore 2 K := by
  intro x hx
  have hmat : (model.quotientIso (QuotientGroup.mk' (pCore 2 K) x)).val = 1 := by
    apply Matrix.mulVec_injective
    funext v
    obtain ⟨w, hw⟩ := model.moduleIso.surjective (Multiplicative.ofAdd v)
    obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective (blockFixed K) w
    have hfix : blockConjugate K x u = u := by
      apply Subtype.ext
      change x * (u : K) * x⁻¹ = (u : K)
      rw [← mem_centralizer_iff.mp hx u u.property, mul_inv_cancel_right]
    have he := model.intertwining x u
    rw [hfix, hw] at he
    have he' := congrArg Multiplicative.toAdd he.symm
    rw [hρ] at he'
    simpa using he'
  have hone : model.quotientIso (QuotientGroup.mk' (pCore 2 K) x) = 1 :=
    Subtype.ext hmat
  exact (QuotientGroup.eq_one_iff x).mp
    (model.quotientIso.injective (hone.trans model.quotientIso.map_one.symm))


/-- Odd index in the block itself, using the literal core quotient map. -/
theorem borel_odd_index [CharP F 2] (B : Subgroup K) (hQB : pCore 2 K ≤ B)
    (hB : B.map (model.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))) =
      rankOneBorel F) : Odd B.index := by
  let f := model.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  have hf : Function.Surjective f :=
    model.quotientIso.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : f.ker ≤ B := by
    intro x hx
    apply hQB
    apply (QuotientGroup.eq_one_iff x).mp
    exact model.quotientIso.injective ((MonoidHom.mem_ker.mp hx).trans
      model.quotientIso.map_one.symm)
  have hi := B.index_map_eq hf hker
  rw [hB] at hi
  rw [← hi]
  exact sl2_borel_odd_index

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.BlockRigidity
