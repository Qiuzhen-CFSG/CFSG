module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.LinearEndpoints.HexadPairOrders
public import Theory.SpecificGroups.SymmetricSix.PolarAffine.FixedFreeCentralizerPower
public import Mathlib.Data.Fin.VecNotation

/-!
# The first remaining D-word after the native cubic lift

Relator 19 is the fourth power of `p₁ n p₀⁻¹`.  The quotient word has fourth
power one; the actual kernel defect is killed if it centralizes the original
fixed-point-free `p₀` action.  This exposes exactly the additional geometric
condition still needed for the seven-word completion.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Subgroup.CosetWordCertificate
namespace CFSG.Quasithin.HigmanSims
variable {G : Type*} [Group G] {A : Subgroup G} [IsElementaryAbelian 2 A]
local notation "A6" => alternatingGroup (Fin 6)
local notation "Vec" => Theory.SpecificGroups.SymmetricSix.NaturalModule

theorem NaturalEndpointData.hexad_relator19_of_centralizer
    (d : NaturalEndpointData A) (hPD : d.carrier≤d.hexad_overgroup)
    (q : d.hexad_overgroup→*A6) (_hqker : q.ker=A.subgroupOf d.hexad_overgroup)
    (k : q.ker≃*Multiplicative Vec)
    (hk : ∀ (g : d.hexad_overgroup) (a : q.ker),
      k (MulAut.conjNormal g a)=Multiplicative.ofAdd
        (Theory.SpecificGroups.SymmetricSix.polarAction (q g).val (k a).toAdd))
    (pair : Fin 2→d.carrier)
    (p0free : ∀ v : Vec,
      Theory.SpecificGroups.SymmetricSix.polarAction
        (q (inclusion hPD (pair 0))).val v=v → v=0)
    (n : G) (hnD : n∈d.hexad_overgroup)
    (hquot : (q (inclusion hPD (pair 1)) * q ⟨n,hnD⟩ *
      (q (inclusion hPD (pair 0)))⁻¹)^4=1)
    (hcentral : Commute
      (((inclusion hPD (pair 1))*⟨n,hnD⟩*(inclusion hPD (pair 0))⁻¹)^4)
      (inclusion hPD (pair 0))) :
    ∀ ell : G, eval ![(pair 0:G),(pair 1:G),ell,n]
      (Theory.SpecificGroups.MathieuAmalgamCompletion.relator 19)=1 := by
  let x : d.hexad_overgroup :=
    inclusion hPD (pair 1) * ⟨n,hnD⟩ * (inclusion hPD (pair 0))⁻¹
  have hxq : (q x)^4=1 := by simpa [x,map_mul,map_inv,mul_assoc] using hquot
  have hxa : x^4=1 :=
    Theory.SpecificGroups.SymmetricSix.PolarAffine.power_eq_one_of_quotient_power_of_centralizer_fixed_free
      q k hk x (inclusion hPD (pair 0)) 4 hxq p0free (by
        simpa [x,mul_assoc] using hcentral)
  intro ell
  simpa [Theory.SpecificGroups.MathieuAmalgamCompletion.relator,
    Theory.SpecificGroups.MathieuAmalgamCompletion.decode,
    eval,FreeGroup.lift_mk,pow_succ,mul_assoc,x] using congrArg (fun z : d.hexad_overgroup => (z:G)) hxa

end CFSG.Quasithin.HigmanSims
