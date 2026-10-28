module

public import Theory.Representation.Triality.OuterDisplacement.ConcretePairedTensorSource.Source
public import Theory.Representation.Triality.OuterDisplacement.ConcretePairedTensorSource.Character
public import Theory.Representation.Triality.RestrictedWeights.ConcreteInnerSource
public import Theory.SpecificGroups.Triality.OuterOddSubgroups.Coverage
public import Theory.SpecificGroups.Triality.EvenFieldFixedResidual
public import Theory.SpecificGroups.Triality.SimplyConnectedModel.SimpleUniversal.SourceUniversality
public import Theory.AlgebraicGroup.Tori.SemisimpleCenterContainment.Source

/-!
# Actual outer-involution displacement for the native triality action

Classify the original faithful irreducible native action by the proved finite
tensor theorem. The actual outer automorphism has an inner--coefficient
expression; its square forces the coefficient to be Frobenius to the three
half-exponent. The original intertwining involution fixes the character, so
the exact finite character theorem forces the required weight period.

The constructed tensor halves absorb the actual inner element on the second
half. Schur rigidity identifies the transported original operator with
interchange and proves displacement at least seven sixteenths of dimension.
Every linear equivalence and displacement map retains the native carrier.
The final theorem discharges algebraic universality by the semisimple-center
source theorem. No period, tensor realization, paired coordinates, character
invariance, or geometry conclusion is assumed. Simplicity and perfectness
may be inherited from the marked source component.

Source: Guralnick--Malle II, Section 3.5 and Lemma 8.6; GLS3 2.5 and 2.8.
-/

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open D4RestrictedWeight
open Triality.SimplyConnected Triality.Standard Triality.Standard.OuterOdd
open Triality.RestrictedWeights Triality.RestrictedWeights.Concrete
open Triality.RestrictedWeights.SteinbergTensors
open Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor
namespace Triality.OuterDisplacement.ConcretePairedTensorSource
public noncomputable section
universe u
variable (k : Type u) [Field k] [IsAlgClosed k] [CharP k 2]

/-- Native ratio with the earlier universal-version theorem explicit. -/
theorem native_outer_involution_ratio_of_universal
    (hu : IsUniversalVersion (groupVariety k)) (n : ℕ) (hn : 0<n)
    [IsSimpleGroup (BinaryCarrier n hn)] [Group.IsPerfect (BinaryCarrier n hn)]
    {W : Type u} [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (σ : Representation k (BinaryCarrier n hn) W) [Representation.IsIrreducible σ]
    (hf : Function.Injective σ)
    (α : MulAut (BinaryCarrier n hn)) (hα : α^2=1)
    (hout : α∉MulAut.innerSubgroup (BinaryCarrier n hn))
    (T : Module.End k W) (hT : T*T=1)
    (hTi : ∀ g v,T (σ g v)=σ (α g) (T v)) :
    7*Module.finrank k W ≤ 16*Module.finrank k (LinearMap.range (T-LinearMap.id)) := by
  obtain ⟨x,c,hform⟩ := Coverage.binary_inner_coefficient n hn α
  obtain ⟨m,hm,hnm⟩ := EvenField.even_parameter_of_noninner_inner_coefficient n hn α hα hout x c hform
  have hce := (EvenField.NormalForm.canonical_coefficient_and_cocycle n hn m hm hnm α hα hout x c hform).1
  have hx : ∀ g,α g=x*coefficientAction (binaryParameters n hn)
      (EvenField.coefficientFrobenius n hn (3*m)) g*x⁻¹ := by
    intro g
    rw [hform,hce]
    rfl
  obtain ⟨a,⟨e⟩,_⟩ := native_tensor_exhaustive k hu n hn (FDRep.of σ) (show Representation.IsIrreducible σ from inferInstance)
  let R := tensor (basicFamily k hu).factor (finiteGeometry k hu).frobenius.onPoints
    (nativePointHom k n hn) (extendWeights hn a) n
  let U : Module.End k R := e.toLinearEquiv.conj T
  have hU : U*U=1 := by
    apply LinearMap.ext
    intro v
    change e (T (e.symm (e (T (e.symm v)))) )=v
    rw [e.symm_apply_apply]
    have hh : T (T (e.symm v))=e.symm v := LinearMap.congr_fun hT _
    rw [hh,e.apply_symm_apply]
  have hUi : ∀ g v,U (R.ρ g v)=R.ρ (α g) (U v) := by
    intro g v
    change e (T (e.symm (R.ρ g v)))=R.ρ (α g) (e (T (e.symm v)))
    have he : e.symm (R.ρ g v)=σ g (e.symm v) :=
      LinearMap.congr_fun (e.symm.isIntertwining' g) v
    rw [he,hTi]
    exact LinearMap.congr_fun (e.isIntertwining' (α g)) _
  have hp := native_tensor_period_of_inner_coefficient_intertwiner k hu n hn a (3*m) α x hx
    U hU (fun g=>LinearMap.ext (hUi g))
  have hRf : Function.Injective R.ρ := by
    intro g h he
    apply hf
    apply LinearMap.ext
    intro v
    apply e.injective
    have hg := LinearMap.congr_fun (e.isIntertwining' g) v
    have hh := LinearMap.congr_fun (e.isIntertwining' h) v
    exact hg.trans ((LinearMap.congr_fun he (e v)).trans hh.symm)
  have hne := native_tensor_nonzero_weight k hu n hn (extendWeights hn a)
    (EvenInvolutionGeometry.longRoot n hn 1)
    (EvenInvolutionGeometry.longRoot_orderOf n hn one_ne_zero) hRf
  have hb := tensor_ratio_of_inner_coefficient_period k hu n hn m hm hnm a hp hne α hα x hx U hU hUi
  have hd := e.toLinearEquiv.finrank_eq
  have hr := Representation.BinaryOffender.NaturalTensor.operatorFixedCodim_eq_of_equiv
    T U e.toLinearEquiv (fun v=>by
      change e (T v)=e (T (e.symm (e v)))
      rw [e.symm_apply_apply])
  change Module.finrank k (LinearMap.range (T-LinearMap.id))=
    Module.finrank k (LinearMap.range (U-LinearMap.id)) at hr
  rw [←hd,←hr] at hb
  exact hb

/-- The actual faithful irreducible native operator has the required displacement,
with all finite tensor and algebraic-group source inputs discharged. -/
theorem native_outer_involution_ratio
    (n : ℕ) (hn : 0<n)
    [IsSimpleGroup (BinaryCarrier n hn)] [Group.IsPerfect (BinaryCarrier n hn)]
    {W : Type u} [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (σ : Representation k (BinaryCarrier n hn) W) [Representation.IsIrreducible σ]
    (hf : Function.Injective σ)
    (α : MulAut (BinaryCarrier n hn)) (hα : α^2=1)
    (hout : α∉MulAut.innerSubgroup (BinaryCarrier n hn))
    (T : Module.End k W) (hT : T*T=1)
    (hTi : ∀ g v,T (σ g v)=σ (α g) (T v)) :
    7*Module.finrank k W ≤ 16*Module.finrank k (LinearMap.range (T-LinearMap.id)) :=
  native_outer_involution_ratio_of_universal k
    (source_universal_of_semisimple_centers k (fun _ _ hH _ hS =>
      SemisimpleCenterContainment.center_le_maximalTorus_of_semisimple hH hS))
    n hn σ hf α hα hout T hT hTi

end
end Triality.OuterDisplacement.ConcretePairedTensorSource
