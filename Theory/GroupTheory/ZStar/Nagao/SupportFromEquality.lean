module

public import Theory.GroupTheory.ZStar.Nagao.CharacterwiseTrace
public import Theory.GroupTheory.ZStar.Nagao.CharacterwiseProjection

/-!
# Local core support from principal Brauer equality

For a principal-block character and an involution, the principal Brauer
equality forces its involution section to have no outside-local-block
component on the local odd core. Represent the group algebra on the
denominator-cleared character-projector right ideal over the cyclotomic DVR.
The Nagao trace vanishes there on commuting odd-order elements. The integral
isotypic trace formula converts this into the coefficient vanishing needed
by the characterwise projection theorem.

The Brauer equality is an explicit hypothesis, not a proved input here;
the unconditional support assembly supplies it from Third Main.
Ported from `public/lean-eval/glauberman_zStar`,
`Submission/ZStar/CharacterwiseSupport.lean` (revision `c3503435`).
-/

public section

noncomputable section

namespace Glauberman.ZStar.CharacterwiseSupport

open ModularBlock PrincipalBlockConstruction

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
  let : IsDiscreteValuationRing R :=
    CyclotomicDVR.cyclotomicOrderAtPrime_isDiscreteValuationRing d
  let : Module.Free R V := IsotypicLattice.rightIdeal_free q
  let : Module.Finite R V :=
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
    simp [R] at hmap
  have htraceCoeff :=
    IsotypicLattice.trace_rightIdealLeftMul_eq_coeff_one
      q a (IsotypicLattice.characterProjectorNumerator_mem_center d i)
      (IsotypicLattice.characterProjectorNumerator_mul_self d i) hcard
  rw [htraceCoeff] at htrace
  simpa [a, q, R] using htrace

end Glauberman.ZStar.CharacterwiseSupport

