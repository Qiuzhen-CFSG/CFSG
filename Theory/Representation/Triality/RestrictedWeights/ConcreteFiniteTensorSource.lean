module
public import Theory.Representation.Triality.RestrictedWeights.ConcreteAlgebraicTensor
public import Theory.Representation.Triality.RestrictedWeights.ConcreteFiniteClassification
public import Theory.Representation.Triality.RestrictedWeights.ConcreteInvolutionDisplacement
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.CharacterShift

/-!
# Native finite triality tensor classification

The genuine rational D4 tensors restrict irreducibly to the finite elementary
subgroup. The proved finite highest-weight separation and exhaustion supply
unique binary parameter words. Transport along the actual native-to-Spin
inclusion retains the original representation and a linear intertwiner.
Only universality of the algebraic Spin carrier remains an earlier input.
Source: GLS3 2.8.2 and 2.8.6(a); Steinberg 13.1 and 13.3.
-/

@[expose] public noncomputable section
open Theory.AlgebraicGroup
open Theory.AlgebraicGroup.StandardRootSystem.D4RestrictedWeight
open scoped TensorProduct
namespace Triality.RestrictedWeights.SteinbergTensors
universe u v
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {K : Variety k} [AlgebraicGroup K]

def tensorPullbackEquiv (A : BasicWeight → RationalFactor K)
    (φ : Monoid.End K.Point) {G : Type v} [Group G] (ι : G →* K.Point)
    (w : ℕ → BasicWeight) (n : ℕ) :
    Representation.Equiv ((tensor A φ (MonoidHom.id _) w n).ρ.comp ι)
      (tensor A φ ι w n).ρ := by
  induction n with
  | zero => exact .refl _
  | succ n ih =>
    refine .mk (TensorProduct.congr ih.toLinearEquiv (LinearEquiv.refl k _)) ?_
    intro g
    apply TensorProduct.ext
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    change ih ((tensor A φ (MonoidHom.id _) w n).ρ (ι g) x) ⊗ₜ[k]
      ((A (w n)).action.action ((φ^n) (ι g))).val y =
      (tensor A φ ι w n).ρ g (ih x) ⊗ₜ[k]
      ((A (w n)).action.action ((φ^n) (ι g))).val y
    exact congrArg (fun z => z ⊗ₜ[k] ((A (w n)).action.action ((φ^n) (ι g))).val y)
      (LinearMap.congr_fun (ih.isIntertwining' g) x)

end Triality.RestrictedWeights.SteinbergTensors

namespace Triality.RestrictedWeights.Concrete
open Triality.SimplyConnected Triality.Standard
open SteinbergTensors SteinbergTensors.AlgebraicTensor SteinbergTensors.FiniteRestriction
universe u
variable (k : Type u) [Field k] [IsAlgClosed k] [CharP k 2]
variable (hu : IsUniversalVersion (groupVariety k))

def finiteTensorFactor (n : ℕ) (hn : 0<n) (a : Fin n → BasicWeight) :
    RationalFactor (groupVariety k) :=
  leftRationalTensorFactor (algebraicGeometry k hu) (ordinaryFrobenius k hu)
    (basicFamily k hu) (extendWeights hn a) n

theorem finiteTensorFactor_highest (n : ℕ) (hn : 0<n) (a : Fin n → BasicWeight) :
    HasLeftHighestWeight (finiteGeometry k hu) (finiteTensorFactor k hu n hn a)
      (wordWeight n a) := by
  have hweight : tensorWeight (extendWeights hn a) n = wordWeight n a := by
    rw [tensorWeight_eq_wordWeight]
    congr 1
    funext i
    exact extendWeights_initial hn a i
  exact hweight ▸ leftRationalTensor_hasHighWeight_sum
    (algebraicGeometry k hu) (ordinaryFrobenius k hu) (basicFamily k hu)
    (extendWeights hn a) n

def finiteTensorRestrictionEquiv (n : ℕ) (hn : 0<n) (a : Fin n → BasicWeight) :
    Representation.Equiv
      ((finiteTensorFactor k hu n hn a).restrict (nativePointHom k n hn)).ρ
      (tensor (basicFamily k hu).factor (finiteGeometry k hu).frobenius.onPoints
        (nativePointHom k n hn) (extendWeights hn a) n).ρ :=
  tensorPullbackEquiv _ _ _ _ _

theorem native_restriction_irreducible (n : ℕ) (hn : 0<n)
    (A : RationalFactor (groupVariety k)) (a : Weight) (ha : FiniteRestriction.InRestrictedRange n a)
    (hA : HasLeftHighestWeight (finiteGeometry k hu) A a) :
    Representation.IsIrreducible (A.restrict (nativePointHom k n hn)).ρ := by
  have hi := leftRestrictedIrreducibility k hu n hn A a ha hA
  have hcomp : (A.restrict (nativePointHom k n hn)).ρ =
      ((A.restrict ((finiteGeometry k hu).inclusion n)).ρ.comp
        (nativeElementaryEquiv k n hn).toMonoidHom) := by
    ext g v
    exact congrArg (fun x => (A.action.action x).val v) (nativePointHom_eq_inclusion k n hn g)
  rw [hcomp]
  exact (Representation.irreducible_comp_surjective_iff _
    (nativeElementaryEquiv k n hn).surjective _).mpr hi

theorem native_tensor_irreducible (n : ℕ) (hn : 0<n) (a : Fin n → BasicWeight) :
    Representation.IsIrreducible (tensor (basicFamily k hu).factor
      (finiteGeometry k hu).frobenius.onPoints (nativePointHom k n hn)
      (extendWeights hn a) n).ρ := by
  have hi := native_restriction_irreducible k hu n hn (finiteTensorFactor k hu n hn a)
    (wordWeight n a) (wordWeight_mem_range n a) (finiteTensorFactor_highest k hu n hn a)
  exact (Representation.RepEquiv.ofRepresentationEquiv (finiteTensorRestrictionEquiv k hu n hn a).symm).irreducible_of_euqiv hi


theorem native_restriction_unique (n : ℕ) (hn : 0<n)
    (A C : RationalFactor (groupVariety k)) (a b : Weight)
    (ha : FiniteRestriction.InRestrictedRange n a)
    (hb : FiniteRestriction.InRestrictedRange n b)
    (hA : HasLeftHighestWeight (finiteGeometry k hu) A a)
    (hC : HasLeftHighestWeight (finiteGeometry k hu) C b)
    (e : Representation.Equiv (A.restrict (nativePointHom k n hn)).ρ
      (C.restrict (nativePointHom k n hn)).ρ) : a=b := by
  apply leftRestrictedSeparation k hu n hn A C a b ha hb hA hC
  refine ⟨.mk e.toLinearEquiv (fun g => LinearMap.ext fun v => ?_)⟩
  have hpoint : nativePointHom k n hn ((nativeElementaryEquiv k n hn).symm g) =
      (finiteGeometry k hu).inclusion n g :=
    (nativePointHom_eq_inclusion k n hn _).trans
      (congrArg ((finiteGeometry k hu).inclusion n)
        ((nativeElementaryEquiv k n hn).apply_symm_apply g))
  have hh := LinearMap.congr_fun (e.isIntertwining' ((nativeElementaryEquiv k n hn).symm g)) v
  change e ((A.action.action (nativePointHom k n hn _)).val v) =
    (C.action.action (nativePointHom k n hn _)).val (e v) at hh
  rw [hpoint] at hh
  exact hh

theorem native_tensor_unique (n : ℕ) (hn : 0<n) (a b : Fin n → BasicWeight)
    (he : Nonempty (Representation.Equiv
      (tensor (basicFamily k hu).factor (finiteGeometry k hu).frobenius.onPoints
        (nativePointHom k n hn) (extendWeights hn a) n).ρ
      (tensor (basicFamily k hu).factor (finiteGeometry k hu).frobenius.onPoints
        (nativePointHom k n hn) (extendWeights hn b) n).ρ)) : a=b := by
  obtain ⟨e⟩ := he
  apply wordWeight_injective n
  exact native_restriction_unique k hu n hn _ _ _ _
    (wordWeight_mem_range n a) (wordWeight_mem_range n b)
    (finiteTensorFactor_highest k hu n hn a) (finiteTensorFactor_highest k hu n hn b)
    (((finiteTensorRestrictionEquiv k hu n hn a).trans e).trans
      (finiteTensorRestrictionEquiv k hu n hn b).symm)

theorem native_rational_lift (n : ℕ) (hn : 0<n) (V : FDRep k (BinaryCarrier n hn))
    (hi : Representation.IsIrreducible V.ρ) :
    ∃ (A : RationalFactor (groupVariety k)) (a : Weight),
      FiniteRestriction.InRestrictedRange n a ∧ HasLeftHighestWeight (finiteGeometry k hu) A a ∧
      Nonempty (Representation.Equiv V.ρ (A.restrict (nativePointHom k n hn)).ρ) := by
  let e := nativeElementaryEquiv k n hn
  let V' := FDRep.of (V.ρ.comp e.symm.toMonoidHom)
  have hi' : Representation.IsIrreducible V'.ρ :=
    (Representation.irreducible_comp_surjective_iff _ e.symm.surjective V.ρ).mpr hi
  obtain ⟨A,a,ha,hA,⟨f⟩⟩ := leftRestrictedExhaustivity k hu n hn V' hi'
  refine ⟨A,a,ha,hA,⟨.mk f.toLinearEquiv (fun g => LinearMap.ext fun v => ?_)⟩⟩
  have hh := LinearMap.congr_fun (f.isIntertwining' (e g)) v
  change f (V.ρ (e.symm (e g)) v) =
    (A.action.action ((finiteGeometry k hu).inclusion n (e g))).val (f v) at hh
  rw [e.symm_apply_apply] at hh
  change f (V.ρ g v) = (A.action.action (nativePointHom k n hn g)).val (f v)
  rw [nativePointHom_eq_inclusion]
  exact hh

theorem native_tensor_exhaustive (n : ℕ) (hn : 0<n) (V : FDRep k (BinaryCarrier n hn))
    (hi : Representation.IsIrreducible V.ρ) :
    ∃! a : Fin n → BasicWeight, Nonempty (Representation.Equiv V.ρ
      (tensor (basicFamily k hu).factor (finiteGeometry k hu).frobenius.onPoints
        (nativePointHom k n hn) (extendWeights hn a) n).ρ) := by
  obtain ⟨A,x,hx,hA,⟨f⟩⟩ := native_rational_lift k hu n hn V hi
  obtain ⟨a,ha⟩ := exists_wordWeight n x hx
  have hB := finiteTensorFactor_highest k hu n hn a
  have he : AreEquivalentRepresentations A.action (finiteTensorFactor k hu n hn a).action := by
    apply leftRationalTensor_equivalent_of_highestWeight (algebraicGeometry k hu)
      (ordinaryFrobenius k hu) (basicFamily k hu) A (extendWeights hn a) n
    have hw : tensorWeight (extendWeights hn a) n = x := by
      rw [tensorWeight_eq_wordWeight]
      convert ha using 2
      funext i
      exact extendWeights_initial hn a i
    exact hw.symm ▸ hA
  obtain ⟨e,he⟩ := he
  let E := (f.trans (restrictEquiv A (finiteTensorFactor k hu n hn a) e he
    (nativePointHom k n hn))).trans (finiteTensorRestrictionEquiv k hu n hn a)
  refine ⟨a,⟨E⟩,?_⟩
  rintro b ⟨eb⟩
  exact native_tensor_unique k hu n hn b a ⟨eb.symm.trans E⟩
end Triality.RestrictedWeights.Concrete
