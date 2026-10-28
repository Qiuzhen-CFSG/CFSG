module

public import CFSG.Quasithin.Chapter12.Section02.ModuleClassification.Definitions
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionAssembly
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleSLThree
public import Theory.Representation.NormalInvariants

/-!
# Assembly of the reducible rows of 12.2.16

Irreducibility forces the fixed subgroup of an original chosen Irr⁺ module
to vanish. The natural and alternating-seven four-space rows already give
TI, and the four-dimensional SL₃ row now has its natural quotient recovered
from its printed hypotheses. Thus precisely the alternating natural-quotient
row and the G₂ natural-quotient row remain in the reducible reduction.

The two geometric row proofs below are explicit outstanding inputs. This
module does not assert the unconditional reducible reduction or 12.2.16.
Its assembly retains the original seven alternatives and the actual action
quotients, so those independent row proofs can be supplied without changing
any source hypothesis.

Source: Aschbacher–Smith, 12.2.2(3a–g) and 12.2.16, pp.795,799–800.
-/

public noncomputable section

open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
open ChapterI.Section06To08 ChapterB.QuasisimpleSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- An irreducible original choice has no nonidentity L-fixed element. -/
theorem fixedSubgroup_eq_bot_of_irreducible (D : ChosenModule T L V) (hi : IsIrreducible D.quotientAction) :
    V ⊓ centralizer (L : Set G) = ⊥ := by
  let := hi
  apply bot_unique
  intro z hz
  let v := (D.spaceEquiv.symm ⟨z,hz.1⟩).toAdd
  have hv : (v.val.toMul.val : G) = z :=
    (D.spaceEquiv_apply v).symm.trans
      (congrArg Subtype.val (D.spaceEquiv.apply_symm_apply ⟨z,hz.1⟩))
  have hfix : ∀ q, D.quotientAction q v = v := by
    intro q
    obtain ⟨l,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) q
    apply Subtype.ext
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Subtype.ext
    change (l : G) * (v.val.toMul.val : G) * (l : G)⁻¹ = (v.val.toMul.val : G)
    rw [hv]
    exact mul_inv_eq_iff_eq_mul.mpr (hz.2 l l.property)
  by_contra hz1
  have hv0 : v ≠ 0 := fun he => hz1
    (hv.symm.trans (congrArg (fun w : D.space => (w.val.toMul.val : G)) he))
  have hne : Representation.invariants
      (D.quotientAction.comp (⊤ : Subgroup (L ⧸ pCore 2 L)).subtype) ≠ ⊥ := by
    intro he
    have hh : v ∈ Representation.invariants
        (D.quotientAction.comp (⊤ : Subgroup (L ⧸ pCore 2 L)).subtype) :=
      fun q => hfix q.val
    rw [he, Submodule.mem_bot] at hh
    exact hv0 hh
  have hk := le_ker_of_normal_invariants_ne_bot D.quotientAction ⊤ hne
  apply D.centralAction_ne_one
  apply MonoidHom.ext
  intro l
  apply LinearMap.ext
  intro w
  induction w using Submodule.Quotient.induction_on with
  | _ w =>
    have he : D.chosenAction l = 1 := hk (mem_top (QuotientGroup.mk' (pCore 2 L) l))
    change Submodule.Quotient.mk (D.chosenAction l w) = Submodule.Quotient.mk w
    rw [he]
    rfl

/-- All reducible rows except the two remaining geometric branches are
closed. The alternating and G₂ producers must discharge these exact inputs. -/
theorem reducible_of_alternating_and_g2
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple) (hnone : NoEscape L V)
    (rows : ModuleAlternatives1222 D)
    (hne : V ⊓ centralizer (L : Set G) ≠ ⊥)
    (alternating : ∀ n : ℕ, 5 ≤ n → n ≤ 8 →
      (letI := D.actionCentralizer_normal
       ActionEquiv D.faithfulCentralAction (alternatingNatural n)) →
      IsTISubgroup V ∨ Nonempty (AlternatingEightFusion T L V))
    (g2 : ActionEquiv D.centralQuotientAction
      ((g2Natural (ZMod 2)).comp (commutator (Atlas.G2.Model (ZMod 2))).subtype) →
      IsTISubgroup V) :
    IsTISubgroup V ∨ Nonempty (AlternatingEightFusion T L V) := by
  cases rows with
  | linear n _ action =>
      exact Or.inl (globalTI_of_natural h D structural hnone
        (D.conjugationModel_of_quotientAction action))
  | linearThreeExtension e hd _ =>
      exact Or.inl (globalTI_of_slThree_four_dimensional h D structural hnone e hd hne)
  | linearFiveExterior _ _ hi =>
      exact (hne (fixedSubgroup_eq_bot_of_irreducible D hi)).elim
  | alternating n hlo hhi action => exact alternating n hlo hhi action
  | alternatingSevenFour e hd =>
      let := D.actionCentralizer_normal
      exact Or.inl (globalTI_of_alternating_seven_four h D structural hnone e hd)
  | g2 action => exact Or.inl (g2 action)
  | tripleSix _ _ _ hi =>
      exact (hne (fixedSubgroup_eq_bot_of_irreducible D hi)).elim

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
