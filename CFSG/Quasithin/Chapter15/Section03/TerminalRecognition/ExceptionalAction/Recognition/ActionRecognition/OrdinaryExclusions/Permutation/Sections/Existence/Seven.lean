module

public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.Recognition.ActionRecognition.OrdinaryExclusions.Permutation.Sections.Existence.AlternatingActor
public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Cases.MarkedElimination.AlternatingSevenDimension.Sections
public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.Recognition.ActionRecognition.OrdinaryExclusions.Permutation.Groups
import Theory.GroupAction.SimpleCosets
import Mathlib.LinearAlgebra.SpecialLinearGroup

/-!
# Natural sections for the terminal S₇ quotient

An alternating offender image is A₇. Simplicity selects the quasisimple
source branch, and the complete B.5.1 clauses force dimension four on the
original module. Its faithful full S₇ action would embed S₇ in SL₄(2) = A₈
with index four. The faithful coset action of simple A₈ rules this out.
Thus the offender image is all of S₇, and the full-actor construction gives
the requested natural moved central section. Fixed summands and nonsplit
kernels are handled by the source dimension theorem, not omitted.

Source: Aschbacher–Smith, B.4.2(7), B.5.1 and B.5.6, printed pp.86,
99 and 105, and the final proof of 15.3.1, p.1155 (1 March 2004 manuscript).
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
namespace CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.ActionRecognition.OrdinaryExclusions.Permutation

private theorem no_seven_in_four {D W : Type*} [Group D]
    [AddCommGroup W] [Module (ZMod 2) W] [Module.Finite (ZMod 2) W]
    (e : D ≃* Equiv.Perm (Fin 7)) (ρ : Representation (ZMod 2) D W)
    (hρ : Function.Injective ρ) (hd : Module.finrank (ZMod 2) W = 4) : False := by
  let toSL : LinearMap.GeneralLinearGroup (ZMod 2) W →* _root_.SpecialLinearGroup (ZMod 2) W :=
    { toFun a := ⟨a.toLinearEquiv, Subsingleton.elim _ _⟩
      map_one' := Subtype.ext rfl
      map_mul' _ _ := Subtype.ext rfl }
  have htoSL : Function.Injective toSL := by
    intro a b hab
    apply (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) W).injective
    exact congrArg Subtype.val hab
  have hρg : Function.Injective ρ.asGroupHom := by
    intro a b hab
    exact hρ (congrArg Units.val hab)
  let b := Module.finBasisOfFinrankEq (ZMod 2) W hd
  let f : D →* alternatingGroup (Fin 8) :=
    alternatingEightLinearEquiv.symm.toMonoidHom.comp
      ((Matrix.SpecialLinearGroup.toLin_equiv b).symm.toMonoidHom.comp
        (toSL.comp ρ.asGroupHom))
  have hf : Function.Injective f := alternatingEightLinearEquiv.symm.injective.comp
    ((Matrix.SpecialLinearGroup.toLin_equiv b).symm.injective.comp (htoSL.comp hρg))
  let : Finite D := Finite.of_equiv (Equiv.Perm (Fin 7)) e.symm.toEquiv
  let : IsSimpleGroup (alternatingGroup (Fin 8)) := alternatingGroup.isSimpleGroup (by simp)
  have hD : Nat.card D = 5040 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin]
    norm_num
  have hA : Nat.card (alternatingGroup (Fin 8)) = 20160 := by
    rw [nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hR : Nat.card f.range = 5040 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hf).toEquiv, hD]
  have hi : f.range.index = 4 := by
    have hc := f.range.index_mul_card
    rw [hR, hA] at hc
    omega
  have hn : f.range ≠ ⊤ := by
    intro h
    rw [h, index_top] at hi
    omega
  have hdiv := f.range.card_dvd_factorial_index_of_simple hn
  rw [hA, hi] at hdiv
  norm_num at hdiv

variable {H : Type*} [Group H] [Finite H] {V : Subgroup H}
  [IsElementaryAbelian 2 (moduleClosure V)] (d : SourceInput V)

private theorem dimension_of_alternating_offender
    (eN : d.offenderGroup ≃* alternatingGroup (Fin 7))
    (h : SourceAlternative d.offenderAction) :
    Module.finrank (ZMod 2) (Additive (moduleClosure V)) = 4 := by
  obtain ⟨c, ht⟩ := source_of_alternating_offender d (Or.inr rfl) eN h
  have hc : Nat.card d.offenderGroup = 2520 := by
    rw [Nat.card_congr eN.toEquiv, nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  exact MarkedElimination.AlternatingSevenDimension.original_dimension d.offenderAction
    hc ht d.offenderAction_moved_eq_top c

/-- The four-dimensional A₇ module cannot extend faithfully to the full S₇
quotient: otherwise S₇ embeds with index four in SL₄(2) = A₈. -/
theorem not_alternating_offender_seven
    (e : coreQuotient H ≃* Equiv.Perm (Fin 7))
    (hN : d.offenderGroup.map e.toMonoidHom = alternatingGroup (Fin 7))
    (h : SourceAlternative d.offenderAction) : False := by
  let eN := (e.subgroupMap d.offenderGroup).trans (MulEquiv.subgroupCongr hN)
  exact no_seven_in_four e
    (quotientAction V d.centralizer_isTwoGroup d.core_centralizes)
    (quotientAction_injective V d.centralizer_isTwoGroup d.core_centralizes)
    (dimension_of_alternating_offender d eN h)

/-- B.5.1 on the actual offender action supplies a natural central section
for every terminal S₇ quotient. -/
theorem naturalSection_seven (e : coreQuotient H ≃* Equiv.Perm (Fin 7))
    (h : SourceAlternative d.offenderAction) : Nonempty (NaturalSection d 7) := by
  rcases offender_image_cases d (by decide) e with hN | hN
  · exact (not_alternating_offender_seven d e hN h).elim
  · have ht : d.offenderGroup = ⊤ := (Subgroup.map_injective e.injective)
      (hN.trans (Subgroup.map_top_of_surjective _ e.surjective).symm)
    exact naturalSection_of_full_offender d (Or.inr rfl) e ht h
end CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.ActionRecognition.OrdinaryExclusions.Permutation
