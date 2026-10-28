module
public import Theory.SpecificGroups.ReeTwo.ParabolicConcreteLinear
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.ReeLocal.LinearOvergroups

/-!
# Applying the actual Ree and Tits representations to overgroups

A faithful action of Mc/F on E fixing the source mark, and restricting to the
computed parabolic action, makes the image of QH normal in Mc. The concrete
translation-image premise is discharged here in both actual models. The
parent must still produce the ambient action and prove its faithfulness;
neither that action nor H = Mc is asserted by these conditional reductions.

The actual quotients H/QH have cyclic Sylow two-subgroups in both models.
Consequently the cyclic-Sylow residual step survives in both cases. The
extra characteristic subgroup in full Ree remains available through the
separate lattice calculations and is not removed by irreducibility alone.

Source: Aschbacher--Smith 14.2.21, printed p.989.
-/

public section
open Subgroup Theory.LinearAlgebra.BinaryFivePointStabilizer
namespace CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.ReeLocal.Parabolics
open ReeTwo.ParabolicConcrete ReeTwo.Centralizer
open Tits.ExceptionalParabolics

/-- The concrete full-Ree translation calculation discharges the normal-image premise. -/
theorem ree_core_normal_of_extended_action {M : Type*} [Group M]
    (i : FullRee.first →* M) [(reeF.map i).Normal]
    (ρ : M ⧸ reeF.map i →* stabilizer markedVector) (hρ : Function.Injective ρ)
    (hres : ∀ h : FullRee.first,
      ρ (QuotientGroup.mk' (reeF.map i) (i h)) = reeRepresentation h) :
    (reeQ.map i).Normal := by
  apply normal_of_point_stabilizer_quotient_image markedVector markedVector_ne_zero
    derivedSpace_finrank (reeF.map i) (reeQ.map i) (Subgroup.map_mono reeF_le_Q) ρ hρ
  rw [Subgroup.map_map, Subgroup.map_map]
  have h : (ρ.comp (QuotientGroup.mk' (reeF.map i))).comp i = reeRepresentation :=
    MonoidHom.ext hres
  change reeQ.map ((ρ.comp (QuotientGroup.mk' (reeF.map i))).comp i) = _
  rw [h, ree_core_representation_image]
  exact (pCore_eq_kernel markedVector markedVector_ne_zero derivedSpace_finrank).symm

/-- The same argument works for the actual Tits parabolic, whose F is E. -/
theorem tits_core_normal_of_extended_action {M : Type*} [Group M]
    (i : Tits.ExceptionalParabolics.first →* M) [(titsF.map i).Normal]
    (ρ : M ⧸ titsF.map i →* stabilizer markedVector) (hρ : Function.Injective ρ)
    (hres : ∀ h : Tits.ExceptionalParabolics.first,
      ρ (QuotientGroup.mk' (titsF.map i) (i h)) = titsRepresentation h) :
    (titsQ.map i).Normal := by
  apply normal_of_point_stabilizer_quotient_image markedVector markedVector_ne_zero
    derivedSpace_finrank (titsF.map i) (titsQ.map i) (Subgroup.map_mono titsF_le_Q) ρ hρ
  rw [Subgroup.map_map, Subgroup.map_map]
  have h : (ρ.comp (QuotientGroup.mk' (titsF.map i))).comp i = titsRepresentation :=
    MonoidHom.ext hres
  change titsQ.map ((ρ.comp (QuotientGroup.mk' (titsF.map i))).comp i) = _
  rw [h, tits_core_representation_image]
  exact (pCore_eq_kernel markedVector markedVector_ne_zero derivedSpace_finrank).symm

/-- The full-Ree quotient supplies the cyclic-Sylow residual input. -/
theorem ree_quotient_residual (T : Sylow 2 (FullRee.first ⧸ reeQ)) :
    pResidual 2 (FullRee.first ⧸ reeQ) = pPrimeCore 2 (FullRee.first ⧸ reeQ) :=
  twoResidual_eq_oddCore T (ree_quotient_sylow_cyclic T)

/-- The Tits quotient supplies the same input, with its actual order-512 core. -/
theorem tits_quotient_residual (T : Sylow 2 (Tits.ExceptionalParabolics.first ⧸ titsQ)) :
    pResidual 2 (Tits.ExceptionalParabolics.first ⧸ titsQ) =
      pPrimeCore 2 (Tits.ExceptionalParabolics.first ⧸ titsQ) :=
  twoResidual_eq_oddCore T (tits_quotient_sylow_cyclic T)

end CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.ReeLocal.Parabolics
