import Submission.ZStar.CharacterwiseNagao
import Submission.ZStar.CharacterwiseProjection
import Submission.ZStar.BrauerThirdMain

/-!
# From characterwise Nagao vanishing to local core support

This file closes the ordinary-character side of the local support argument.
Its sole block-theoretic hypothesis is the explicit principal Brauer equality;
in particular, it does not assume local support or section invariance.
-/

noncomputable section

namespace Submission.ZStar
namespace CharacterwiseSupport

open PrincipalBlockConstruction

universe u

attribute [local instance] Fintype.ofFinite

/-- Conditional local-support theorem obtained from the characterwise Nagao
trace calculation.  This is an intermediate adapter only: the principal
Brauer equality still has to be proved unconditionally before it can be used
on the final Z*-theorem path. -/
theorem canonicalLocalPrincipalBlockCoreSupport_of_brauerEquality
    {G : Type u} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (i : d.I)
    (hi : i ∈ d.block) (z : G) (hzI : IsInvolution z)
    (heq : CompatibleBrauerBlock.InvolutionPrincipalBrauerEquality d z) :
    LocalBlockSection.CanonicalLocalPrincipalBlockCoreSupport d i z := by
  classical
  rw [LocalBlockSection.canonicalLocalPrincipalBlockCoreSupport_iff_brauerCompatibility]
  intro x hx
  apply
    CharacterwiseProjection.localPrincipalBlockProjection_eq_of_projector_coeff_eq_zero
      d i z x hi
  let R := Localization.AtPrime d.primeIdeal
  let q : MonoidAlgebra R G :=
    IsotypicLattice.characterProjectorNumerator d i
  let V := CentralIdempotentSupport.rightIdeal R q
  let rho : Representation R G V :=
    CentralIdempotentSupport.rightIdealRepresentation R q
  letI : IsDiscreteValuationRing R :=
    CyclotomicDVR.cyclotomicOrderAtPrime_isDiscreteValuationRing d
  letI : Module.Free R V := IsotypicLattice.rightIdeal_free q
  letI : Module.Finite R V :=
    Module.Finite.range (LinearMap.mulRight R q)
  have hzsq : z * z = 1 := by
    simpa [pow_two] using hzI.2
  have hxodd : Odd (orderOf (x : G)) := by
    let H := Subgroup.centralizer ({z} : Set G)
    let xCore : pPrimeCore 2 H := ⟨x, hx⟩
    have hcardOdd : Odd (Nat.card (pPrimeCore 2 H)) :=
      Nat.coprime_two_left.mp
        (pPrimeCore_coprime_card (p := 2) (G := H))
    have hxCoreOdd : Odd (orderOf xCore) :=
      hcardOdd.of_dvd_nat (orderOf_dvd_natCard xCore)
    have hxHOdd : Odd (orderOf x) := by
      simpa only [xCore, Subgroup.orderOf_mk] using hxCoreOdd
    rw [Subgroup.orderOf_coe]
    exact hxHOdd
  have heq' :
      BrauerBlockReduction.involutionBrauerPrincipalBlockElement d z =
        CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d
          (Subgroup.centralizer ({z} : Set G)) := by
    simpa [CompatibleBrauerBlock.InvolutionPrincipalBrauerEquality] using heq.symm
  have htrace :=
    CharacterwiseNagao.trace_principalComplement_comp_eq_zero
      d rho z hzI.1 hzsq heq' x hxodd
  let a : MonoidAlgebra R G :=
    MonoidAlgebra.of R G (z * (x : G)) *
      NagaoComplement.principalComplement d z
  have hrepresented :
      (rho (z * (x : G))).comp
          (rho.asAlgebraHom (NagaoComplement.principalComplement d z)) =
        IsotypicLattice.rightIdealLeftMul q a := by
    calc
      (rho (z * (x : G))).comp
            (rho.asAlgebraHom (NagaoComplement.principalComplement d z)) =
          rho.asAlgebraHom a := by
            rw [show rho (z * (x : G)) =
                rho.asAlgebraHom
                  (MonoidAlgebra.of R G (z * (x : G))) by
              exact (Representation.asAlgebraHom_of rho _).symm]
            simp only [a, map_mul, Module.End.mul_eq_comp]
      _ = IsotypicLattice.rightIdealLeftMul q a := by
        simpa [rho] using
          CharacterwiseNagao.rightIdealRepresentation_asAlgebraHom q a
  rw [hrepresented] at htrace
  have hcard : (Nat.card G : R) ≠ 0 := by
    intro hzero
    have hmap := congrArg (IsotypicLattice.localizationToComplex d) hzero
    have hcardC : (Nat.card G : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.card_pos (α := G)).ne'
    exact hcardC (by simpa [R] using hmap)
  have htraceCoeff :=
    IsotypicLattice.trace_rightIdealLeftMul_eq_coeff_one
      q a (IsotypicLattice.characterProjectorNumerator_mem_center d i)
      (IsotypicLattice.characterProjectorNumerator_mul_self d i) hcard
  rw [htraceCoeff] at htrace
  simpa [a, q, R] using htrace

/-- Unconditional local principal-block core support.  The block-theoretic
input to the characterwise argument is supplied by the Third Main theorem. -/
theorem canonicalLocalPrincipalBlockCoreSupport
    {G : Type u} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (i : d.I)
    (hi : i ∈ d.block) (z : G) (hzI : IsInvolution z) :
    LocalBlockSection.CanonicalLocalPrincipalBlockCoreSupport d i z := by
  exact canonicalLocalPrincipalBlockCoreSupport_of_brauerEquality
    d i hi z hzI
    (Submission.ZStar.involutionPrincipalBrauerEquality d z hzI)

end CharacterwiseSupport
end Submission.ZStar
