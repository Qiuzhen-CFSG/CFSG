module

public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.NormalizerModule.AbelianSection.NaturalQuotient
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.Actions

/-!
# The HS natural quotient in the convention of B.4.8(2)

Transport the quotient coordinates across the proved equality between the
literal central image and the invariant space. This gives an ActionEquiv
for the actual reducedAction used by the nonsplitting consumer, retaining
the compatible actor identification. The abelian-section assembly supplies
both the equality and the coordinates from the cover and model inputs.

Source: Aschbacher–Smith I.2.2(5), printed p.412 / PDF p.423, and B.4.8(2),
printed p.91 / PDF p.102.
-/

@[expose] public section

open Subgroup Matrix
open scoped IsMulCommutative
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.NaturalQuotient

/-- Change only the quotient subspace along its proved equality, preserving
the full intertwiner and the compatible actor map. -/
noncomputable def reducedActionEquivOfCoordinates {K : Type*} [Group K] [Finite K]
    (e : (K ⧸ center K) ≃* Sporadic.LeechRelated.HS.Carrier)
    (hZ : Nat.card (center K) = 2)
    (hc : centralLine e hZ = (frattiniRepresentation e).invariants)
    (f : (Additive (Qbar e) ⧸ centralLine e hZ) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2))
    (hf : ∀ a v, f (quotientRepresentation e hZ a v) =
      (actorEquiv e hZ a : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ f v) :
    ActionEquiv (reducedAction (frattiniRepresentation e))
      (linearNatural BinaryField.two 3) where
  groupEquiv := actorEquiv e hZ
  linearEquiv := (Submodule.quotEquivOfEq _ _ hc.symm).trans f
  intertwines a v := by
    induction v using Submodule.Quotient.induction_on with | _ v =>
    exact hf a (Submodule.Quotient.mk v)

end CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.NaturalQuotient
