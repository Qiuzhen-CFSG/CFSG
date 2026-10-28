module
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.SevenLifting.Inspection.BinaryLie.G2
public import Theory.AtlasPort.LinearGroups.G2.EvenFieldFixedResidual.Outer
/-!
# The genuine G₂ row of E.6.18

The actual outer-involution theorem gives a coefficient field of strictly
smaller binary degree. This discharges the descent premise in the existing
induction on field degree, preserving the whole acting two-group and its
common fixed component. The exact G₂ model witness then supplies the literal
seven-component inspection. Source: Aschbacher--Smith E.6.18, p.252.
-/
public section
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.BinaryLie.G2
/-- Actual outer descent discharges the smaller-field input to the E.6.18
induction, retaining the original automorphism and its fixed subgroup. -/
theorem outerInvolutionDescent : OuterInvolutionDescent := by
  intro F _ _ n hn hc a ha hout
  obtain ⟨σ,m,hm,hmn,_,hcard,he⟩ :=
    Atlas.G2.EvenFieldFixedResidual.outer_involution_smaller_fixed_model hn hc a ha hout
  exact ⟨m,hm,hmn,Atlas.G2.EvenFieldFixedResidual.fixedField σ,inferInstance,
    inferInstance,hcard,he⟩
/-- The actual binary G₂ model has no seven component in the common fixed
subgroup of a two-group of automorphisms. -/
theorem model_noSevenFixedComponent_unconditional (n : ℕ)
    (F : Type) [Field F] [Finite F] (hn : 0 < n) (hc : Nat.card F = 2 ^ n) :
    NoSevenFixedComponent (Atlas.G2.Model F) :=
  model_noSevenFixedComponent outerInvolutionDescent n F hn hc
end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.BinaryLie.G2
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.BinaryLie
/-- The G₂ row of the original E.6.18 component inspection, with its genuine
model witness and no outer-action or descent premise. -/
theorem g2_sevenActionInspection {S : Type*} [Group S] {f : ℕ} (hf : 2 ≤ f)
    (h : ClassificationModels.IsG2At S (2 ^ f)) : SevenActionInspection S :=
  g2_of_outerInvolutionDescent G2.outerInvolutionDescent hf h
end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.BinaryLie
