module
public import Theory.SpecificGroups.ReeTwo.ParabolicMarkedComparison.SecondCore
public import Theory.SpecificGroups.ReeTwo.FirstParabolicCubicAutomorphisms
public import Theory.SpecificGroups.Tits.AmalgamRigidity.FullRee.SecondSeparator.SecondExtension.WeylVerification

/-!
# The literal cubic action on the native second core

The verified common Sylow marking identifies its intrinsic second core with
the actual two-core of the full second endpoint. Transporting endpoint
conjugation gives the specified action. The existing root/reflection Weyl
relations compute it on ten core generators and prove its order is three.
No automorphism or field-action model is assumed.

Source: Shinoda/Parrott root relations, and the binary branch of
Aschbacher–Smith F.1.12 used in J.4.5.
-/

@[expose] public section
noncomputable section
open Subgroup
namespace ReeTwo.SylowModel.CubicAction
open Tits.ExceptionalParabolics.FullRee
open Tits.AmalgamRigidity.FullRee.SecondExtension
open ReeTwo.ParabolicMarkedComparison

abbrev A := SylowModel.firstParabolicCore

/-- Restriction of the already marked Sylow map to the actual endpoint core. -/
def coreEquiv : A ≃* pCore 2 Endpoint :=
  Verified.secondCoreEquiv.trans
    ((pCore 2 Endpoint).equivMapOfInjective Endpoint.subtype Endpoint.subtype_injective).symm

theorem coreEquiv_inclusion (a:A) : (coreEquiv a:Endpoint)=inclusion (a:SylowModel) := by
  apply Endpoint.subtype_injective
  let e: pCore 2 Endpoint≃*LongRootPaths.secondCore :=
    (pCore 2 Endpoint).equivMapOfInjective Endpoint.subtype Endpoint.subtype_injective
  have hh:=congrArg (fun x:LongRootPaths.secondCore=>(x:ReeF4.Model 0))
    (e.apply_symm_apply (Verified.secondCoreEquiv a))
  exact hh

/-- Literal endpoint conjugation transported to the coordinate second core. -/
def action : Endpoint→*MulAut A :=
  (MulAut.congr coreEquiv.symm).toMonoidHom.comp MulAut.conjNormal

theorem action_inclusion (r:Endpoint) (a:A) :
    inclusion (action r a:SylowModel)=r*inclusion (a:SylowModel)*r⁻¹ := by
  rw [←coreEquiv_inclusion,←coreEquiv_inclusion]
  change ((coreEquiv (coreEquiv.symm (MulAut.conjNormal r (coreEquiv a)))):Endpoint)=_
  rw [coreEquiv.apply_symm_apply]
  rfl

/-- The genuine root/reflection cubic in the full native second endpoint. -/
def element : Endpoint := inclusion (SylowModel.root 0)*reflection

def cubic : MulAut A := action element

def generator (i:Fin 10):A :=
  ⟨radicalGenerator i,(SylowModel.mem_firstParabolicCore_iff _).mpr (radicalGenerator_mem i)⟩

def cubicImage (i:Fin 10):A :=
  ⟨SylowModel.root 0*weylImage i*(SylowModel.root 0)⁻¹,by
    rw [SylowModel.mem_firstParabolicCore_iff]
    exact (by decide +kernel : ∀i:Fin 10,
      (SylowModel.root 0*weylImage i*(SylowModel.root 0)⁻¹).left.b0=0) i⟩

theorem cubic_generator (i:Fin 10) : cubic (generator i)=cubicImage i := by
  apply A.subtype_injective
  apply Tits.AmalgamRigidity.FullRee.SecondExtension.inclusion_injective
  change inclusion (cubic (generator i):SylowModel)=inclusion (cubicImage i:SylowModel)
  rw [show inclusion (cubic (generator i):SylowModel)=
    element*inclusion (generator i:SylowModel)*element⁻¹ from action_inclusion ..]
  change (inclusion (SylowModel.root 0)*reflection)*inclusion (radicalGenerator i)*
    (inclusion (SylowModel.root 0)*reflection)⁻¹=
      inclusion (SylowModel.root 0*weylImage i*(SylowModel.root 0)⁻¹)
  rw [map_mul,map_mul,map_inv]
  calc
    _ = inclusion (SylowModel.root 0)*(reflection*inclusion (radicalGenerator i)*reflection⁻¹)*
        (inclusion (SylowModel.root 0))⁻¹ := by group
    _ = _ := by rw [weyl_relations.conjugate]

theorem cubic_order : orderOf cubic=3 := by
  let _ : Fact (Nat.Prime 3):=⟨by decide⟩
  apply orderOf_eq_prime
  · change action element^3=1
    rw [←map_pow,show element^3=1 from weyl_relations.cube,map_one]
  · intro h
    have hh:=cubic_generator 0
    rw [h,MulAut.one_apply] at hh
    exact (by decide +kernel : generator 0≠cubicImage 0) hh

end ReeTwo.SylowModel.CubicAction
