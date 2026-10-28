module

public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.Recognition.ActionRecognition.OrdinaryExclusions.G2.Classification.Fitting
public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Cases.MarkedElimination.AlternatingSevenDimension.Orders
/-!
# Eliminating the nonquasisimple terminal G₂ alternatives

The two direct factors in B.5.6(3) are nontrivial by their actual group
models. The kernels of the two projections would both contain the simple
normal component, although their intersection is trivial. In B.5.6(4),
the embedded A₆ would force 360 to divide 12096, which is impossible.
Together with the already checked seed and commutator exclusions this
leaves the full quasisimple source conclusion, including its actual section.

Source: Aschbacher–Smith, B.5.6, printed p.105, and the final proof of
15.3.1, printed p.1155.
-/

public section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
namespace CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.ActionRecognition.OrdinaryExclusions.G2.Classification
variable {H : Type*} [Group H] [Finite H] {V : Subgroup H}
  [IsElementaryAbelian 2 (moduleClosure V)] (d : SourceInput V)

private theorem not_product (e : coreQuotient H ≃* Atlas.G2.Model (ZMod 2))
    {A B : Type*} [Group A] [Group B] [Nontrivial A] [Nontrivial B]
    (f : (A × B) ≃* d.offenderGroup) : False := by
  let p := (MonoidHom.fst A B).comp f.symm.toMonoidHom
  let q := (MonoidHom.snd A B).comp f.symm.toMonoidHom
  have hp : p.ker ≠ ⊥ := by
    intro hz
    obtain ⟨b, hb⟩ := exists_ne (1 : B)
    have hm : f (1, b) ∈ p.ker := by
      change (f.symm (f (1, b))).1 = 1
      rw [f.symm_apply_apply]
    rw [hz, mem_bot] at hm
    have he : (1, b) = (1 : A × B) := f.injective (hm.trans f.map_one.symm)
    exact hb (congrArg Prod.snd he)
  have hq : q.ker ≠ ⊥ := by
    intro hz
    obtain ⟨a, ha⟩ := exists_ne (1 : A)
    have hm : f (a, 1) ∈ q.ker := by
      change (f.symm (f (a, 1))).2 = 1
      rw [f.symm_apply_apply]
    rw [hz, mem_bot] at hm
    have he : (a, 1) = (1 : A × B) := f.injective (hm.trans f.map_one.symm)
    exact ha (congrArg Prod.fst he)
  have hkp := fitting_le_normal d e p.ker inferInstance hp
  have hkq := fitting_le_normal d e q.ker inferInstance hq
  have hz : generalizedFitting d.offenderGroup = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    have he : f.symm x = 1 := Prod.ext (hkp hx) (hkq hx)
    exact f.symm.injective (he.trans f.symm.map_one.symm)
  have hc := fitting_card d e
  rw [hz] at hc
  norm_num at hc

/-- The actual offender actor has no source two-factor decomposition. -/
theorem not_twoFactors (e : coreQuotient H ≃* Atlas.G2.Model (ZMod 2))
    (c : SourceTwoFactorCase d.offenderAction) : False := by
  let := MarkedElimination.AlternatingSevenDimension.factor_nontrivial
    (c.firstCase.factorModel d.offenderAction)
  let := MarkedElimination.AlternatingSevenDimension.factor_nontrivial
    (c.secondCase.factorModel d.offenderAction)
  exact not_product d e c.product.equiv

omit [Finite H] in
/-- The actual A₆ embedding rules out the outer product case by divisibility. -/
theorem not_outerSixThree (e : coreQuotient H ≃* Atlas.G2.Model (ZMod 2))
    (c : OuterSixThreeCase d.offenderAction) : False := by
  have hc := c.first.card_subgroup_dvd_card.trans d.offenderGroup.card_subgroup_dvd_card
  rw [Nat.card_congr c.firstEquiv.toEquiv, nat_card_alternatingGroup,
    Nat.card_congr e.toEquiv, Atlas.G2.card_Model] at hc
  norm_num [Nat.factorial] at hc

/-- The complete B.5.6 alternatives have only the quasisimple action case
for the actual terminal G₂ actor. -/
theorem quasisimple_source (e : coreQuotient H ≃* Atlas.G2.Model (ZMod 2))
    (h : SourceAlternative d.offenderAction) :
    Nonempty (QuasisimpleSourceConclusion d.offenderAction
      (generalizedFitting d.offenderGroup)) := by
  rcases remaining_source_cases d h with ⟨_, hc⟩ | hc | hc
  · exact hc
  · exact (not_twoFactors d e hc.some).elim
  · exact (not_outerSixThree d e hc.some).elim
end CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.ActionRecognition.OrdinaryExclusions.G2.Classification
