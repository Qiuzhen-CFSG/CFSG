module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Characteristic.Quotient

/-!
# The two genuine odd alternatives for the fixed component

The simple and three-cover branches of A.3.6 are ordinary components and
therefore quasisimple. Transporting along the literal two-core quotient
isomorphism eliminates both branches whenever Lᵤ/O₂(Lᵤ) is not quasisimple.
Exactly the natural SL₂(p) and nilpotent SL₂(5) branches remain, with all
common structural conclusions and the genuine omega-action data.

This reduction requires no alleged obstruction to arbitrary elementary
actions. Excluding these two alternatives using the actual critical subgroup
remains necessary for 14.7.68(2). The universal A.3.6 input is owned by
qt-a-03 and its local application is verified by Characteristic.Quotient.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
A.3.6, pp.43–45; 1.2.1(4), p.504; 14.7.68(2), pp.1071–1072.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Chapter12.Section08 Chapter1.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
namespace Data
variable (d : Data T L V F W)

/-- The exact remaining source branches, on the actual image of Lᵤ in
C_G(u)/O₂(C_G(u)); simple and three-cover cases need no action exclusion. -/
theorem fixedComponent_odd_alternatives_of_not_quasisimple
    (hA36 : ∀ (X : Type u) [Group X] [Finite X],
      IsSQTK KnownSimple.IsKnownSimple X → pCore 2 X = ⊥ → ∀ B : Subgroup X,
        B.IsCComponent → A36Conclusion B)
    (u : F.U) (hne : (u : G) ≠ 1) {Lu : Subgroup G}
    (hLu : Lu ≤ d.fixedCentralizer u)
    (hc : (Lu.subgroupOf (d.fixedCentralizer u)).IsCComponent)
    (hnq : ¬ IsQuasisimple (Lu ⧸ pCore 2 Lu)) :
    (A36Natural (d.fixedComponentImage u Lu) ∨ A36Nilpotent (d.fixedComponentImage u Lu)) ∧
      A36Common (d.fixedComponentImage u Lu) ∧
      CenterFrattiniSource.OmegaActionData (d.fixedComponentImage u Lu) := by
  obtain ⟨⟨halt, hcommon⟩, _⟩ := d.fixedComponent_earlier_structure hA36 u hne hc
  have hnot : ¬ IsQuasisimple (d.fixedComponentImage u Lu) := by
    intro h
    let := h
    exact hnq (IsQuasisimple.of_mulEquiv (d.fixedComponentQuotientEquiv u hLu hc).symm)
  refine ⟨?_, hcommon, d.fixedComponent_omega_of_not_quasisimple hA36 u hne hLu hc hnq⟩
  cases halt with
  | simple hcomp _ _ => exact (hnot hcomp.2).elim
  | cover hcomp _ _ => exact (hnot hcomp.2).elim
  | natural h => exact Or.inl h
  | nilpotent h => exact Or.inr h

end Data
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
