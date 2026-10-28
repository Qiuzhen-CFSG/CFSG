module

public import CFSG.Quasithin.Chapter13.Section08.SourceDefs
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.GroupTheory.Fitting.Core
public import Theory.GroupTheory.Covering
public import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# The actual residuals in 13.8.12 and 13.8.14

The source operation O₂,F(H) is the inverse image of the ordinary Fitting
subgroup of H/O₂(H). All subgroups are then mapped into the ambient group.
The two-residual of its intersection with M is distinct from the two-residual
of the whole inverse image. The exceptional alternative identifies the actual
central quotient of the quasisimple triple cover, with centre of order three.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), notation on
printed p.491 and Lemmas 13.8.12–14 on printed pp.950–951. This module defines
these conclusions; it does not assert the unproved source trichotomies.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter13.Section08.SolvableExclusion
open Subgroup
open Theory.GroupTheory
variable {G : Type*} [Group G]

/-- O²(X), embedded in G. -/
def twoResidual (X : Subgroup G) : Subgroup G := (pResidual 2 X).map X.subtype

/-- O₂,F(H), intrinsically in H, with F the ordinary Fitting subgroup. -/
def twoFittingIn (H : Subgroup G) : Subgroup H :=
  (fittingSubgroup (Source.Hstar H)).comap (QuotientGroup.mk' (pCore 2 H))

/-- The source O₂,F(H), embedded in G. -/
def twoFitting (H : Subgroup G) : Subgroup G := (twoFittingIn H).map H.subtype

/-- X in 13.8.12(2). -/
def residualInM (H M : Subgroup G) : Subgroup G := twoResidual (twoFitting H ⊓ M)

/-- X in 13.8.14; this definition has no intersection with M. -/
def residualWhole (H : Subgroup G) : Subgroup G := twoResidual (twoFitting H)

/-- The source Â₆ is the quasisimple triple cover (Notation A.3.5). -/
def IsTripleCoverSix (X : Type*) [Group X] : Prop :=
  IsQuasisimple X ∧ Nat.card (center X) = 3 ∧
    Nonempty ((X ⧸ center X) ≃* alternatingGroup (Fin 6))

/-- The source's three alternatives retain L, L₁, and L₁,+ separately. -/
def ResidualAlternative (L L₁ L₁plus X : Subgroup G) : Prop :=
  X = ⊥ ∨
    (Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) ∧ X = L₁) ∨
    (IsTripleCoverSix (L ⧸ pCore 2 L) ∧ X = L₁plus)

theorem twoResidual_le (X : Subgroup G) : twoResidual X ≤ X := map_subtype_le _

theorem twoResidual_mono {X Y : Subgroup G} (h : X ≤ Y) :
    twoResidual X ≤ twoResidual Y := embedded_pResidual_mono 2 h

theorem twoFitting_le (H : Subgroup G) : twoFitting H ≤ H := map_subtype_le _

/-- The intersection residual always lies in the whole residual and in M. -/
theorem residualInM_le (H M : Subgroup G) :
    residualInM H M ≤ residualWhole H ⊓ M :=
  le_inf (twoResidual_mono inf_le_left)
    ((twoResidual_le _).trans inf_le_right)

/-- Containment of the actual Fitting preimage suffices to identify the two
residuals. Establishing that containment is part of the 13.8.14 assembly. -/
theorem residualInM_eq_of_twoFitting_le {H M : Subgroup G}
    (h : twoFitting H ≤ M) : residualInM H M = residualWhole H := by
  unfold residualInM residualWhole
  rw [inf_eq_left.mpr h]

end CFSG.Quasithin.Chapter13.Section08.SolvableExclusion
end
