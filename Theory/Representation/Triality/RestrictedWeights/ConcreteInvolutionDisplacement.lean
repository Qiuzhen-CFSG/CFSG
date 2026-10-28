module

public import Theory.SpecificGroups.Triality.EvenInvolutionGeometry.InvolutionClasses.UnitRepresentatives
public import Theory.Representation.Triality.BinaryDegree.CarrierTransport
public import Theory.Representation.Triality.RestrictedWeights.BasicDisplacement

/-!
# Displacement of all native involutions on the actual triality tensor

The canonical native carrier-to-Spin comparison retains the exact finite
inclusion and the two parameter-one root operators. Conjugacy then applies
the proved basic-factor and tensor displacement bounds to every original
involution. The remaining weight period and finite tensor realization are
kept with their source producers; no involution-class or operator-rank input
remains in this consumer.
Source: GLS3 2.8; Guralnick–Malle II, Lemma 8.6.
-/

@[expose] public noncomputable section
open Matrix
open scoped MatrixGroups
open Theory.AlgebraicGroup

namespace Triality.RestrictedWeights.Concrete
open Triality.SimplyConnected
open Triality.Standard
open Triality.BinaryDegree.CarrierTransport
open SteinbergTensors
universe u
variable (k : Type u) [Field k] [IsAlgClosed k] [CharP k 2]

def nativeElementaryEquiv (n : ℕ) (hn : 0<n) : BinaryCarrier n hn ≃*
    graphFieldElementarySubgroup (Diagram.pinnedAut k) (regularFrobeniusLift k 1).onPoints n :=
  (binaryElementaryEquiv n hn).symm.trans ((binarySpinElementaryEquiv k n hn).trans
    (GraphField.orientationElementaryEquiv k n))

def nativePointHom (n : ℕ) (hn : 0<n) : BinaryCarrier n hn →* Points k :=
  (GeckSpin.finiteComparison k (coefficientEmbedding k n hn)).comp
    (((fixedSubgroup (binaryParameters n hn)).subtype.comp
      (elementarySubgroup (binaryParameters n hn)).subtype).comp
        (binaryElementaryEquiv n hn).symm.toMonoidHom)

theorem nativePointHom_toCarrier (n : ℕ) (hn : 0<n)
    (g : ElementaryGroup (binaryParameters n hn)) :
    nativePointHom k n hn (toCarrier (binaryParameters n hn) g) =
      GeckSpin.finiteComparison k (coefficientEmbedding k n hn) g.val.val := by
  change GeckSpin.finiteComparison k (coefficientEmbedding k n hn)
    ((binaryElementaryEquiv n hn).symm (binaryElementaryEquiv n hn g)).val.val = _
  exact congrArg (fun x : ElementaryGroup (binaryParameters n hn) =>
    GeckSpin.finiteComparison k (coefficientEmbedding k n hn) x.val.val)
      ((binaryElementaryEquiv n hn).symm_apply_apply g)

/-- The exact inclusion used by the finite restriction theorem. -/
theorem nativePointHom_eq_inclusion (n : ℕ) (hn : 0<n) (g : BinaryCarrier n hn) :
    nativePointHom k n hn g = elementaryInclusion (Diagram.pinnedAut k)
      (regularFrobeniusLift k 1).onPoints n (nativeElementaryEquiv k n hn g) := by
  let a := (binaryElementaryEquiv n hn).symm g
  calc
    nativePointHom k n hn g =
        GeckSpin.finiteComparison k (coefficientEmbedding k n hn) a.val.val := rfl
    _ = GraphField.elementaryInclusion k n (binarySpinElementaryEquiv k n hn a) :=
      (binarySpinElementaryEquiv_apply_val k n hn a).symm
    _ = _ := DFunLike.congr_fun (GraphField.elementaryInclusion_eq_orientation k n)
      (binarySpinElementaryEquiv k n hn a)

open Standard.EvenInvolutionGeometry
open BasicDisplacement

theorem nativePointHom_rootOne (n : ℕ) (hn : 0<n) (short : Bool) :
    nativePointHom k n hn (rootOne n hn short) = rootOperator k short := by
  cases short with
  | false =>
    change nativePointHom k n hn (toCarrier (binaryParameters n hn)
      (Parabolics.sl2ElementaryLift _ rfl (longRankOneFixed n hn)
        (SpecialLinearGroup.upperUnipotentHom _ (Multiplicative.ofAdd 1)))) = _
    rw [nativePointHom_toCarrier]
    change GeckSpin.finiteComparison k (coefficientEmbedding k n hn)
      (longRankOneFixed n hn (SpecialLinearGroup.upperUnipotentHom _ (Multiplicative.ofAdd 1))).val = _
    let f := GeckSpin.finiteComparison k (coefficientEmbedding k n hn)
    calc
      f ((longRankOneFixed n hn (SpecialLinearGroup.upperUnipotentHom _
          (Multiplicative.ofAdd 1))).val) =
          f (Parabolics.positiveRoot (binaryParameters n hn) 1
            (baseFieldEmbedding (binaryParameters n hn) 1)) :=
        congrArg f (longRankOneFixed_upper_val n hn 1)
      _ = f (Parabolics.positiveRoot (binaryParameters n hn) 1 1) :=
        congrArg (fun z => f (Parabolics.positiveRoot (binaryParameters n hn) 1 z))
          (map_one (baseFieldEmbedding (binaryParameters n hn)))
      _ = _ := by
        simpa only [f, Parabolics.positiveRoot, rootOperator, Bool.false_eq_true, ↓reduceIte, map_one] using GeckSpin.finiteComparison_positive k
          (coefficientEmbedding k n hn) 1 1

  | true =>
    change nativePointHom k n hn (toCarrier (binaryParameters n hn)
      (Parabolics.sl2ElementaryLift _ rfl (shortRankOneFixed n hn)
        (SpecialLinearGroup.upperUnipotentHom _ (Multiplicative.ofAdd 1)))) = _
    rw [nativePointHom_toCarrier]
    change GeckSpin.finiteComparison k (coefficientEmbedding k n hn)
      (shortRankOneFixed n hn (SpecialLinearGroup.upperUnipotentHom _ (Multiplicative.ofAdd 1))).val = _
    let f := GeckSpin.finiteComparison k (coefficientEmbedding k n hn)
    have hval := shortRankOneFixed_upper_val n hn 1
    have hone : (shortRankOneFixed n hn (SpecialLinearGroup.upperUnipotentHom _
        (Multiplicative.ofAdd 1))).val =
        Parabolics.positiveRoot (binaryParameters n hn) 0 1 *
        Parabolics.positiveRoot (binaryParameters n hn) 2 1 *
        Parabolics.positiveRoot (binaryParameters n hn) 3 1 := by
      simpa only [map_one] using hval
    have h := congrArg f hone
    change f _ = _
    rw [h, map_mul, map_mul]
    have hp (i : Fin 4) : f (Parabolics.positiveRoot (binaryParameters n hn) i 1) =
        Pinning.positiveSimplePoint k i 1 := by
      simpa only [f, Parabolics.positiveRoot, map_one] using GeckSpin.finiteComparison_positive k
        (coefficientEmbedding k n hn) i 1
    rw [hp,hp,hp]
    rfl

open Representation.BinaryOffender.NaturalTensor
open Theory.AlgebraicGroup.StandardRootSystem.D4RestrictedWeight

theorem native_tensor_involution_displacement
    (hu : IsUniversalVersion (groupVariety k)) (n : ℕ) (hn : 0<n)
    (w : ℕ → BasicWeight) (s : ℕ) (hs : 0<s) (hsn : s ∣ 3*n)
    (hwrap : ∀ i,w (i+n)=diagramAction (w i)) (hp : Function.Periodic w s)
    (hne : ∃ i,w i≠zeroWeight) (t : BinaryCarrier n hn) (ht : orderOf t=2) :
    5*n < s * operatorFixedCodim ((tensor (basicFamily k hu).factor
      (finiteGeometry k hu).frobenius.onPoints (nativePointHom k n hn) w n).ρ t) := by
  let ρ := (tensor (basicFamily k hu).factor (finiteGeometry k hu).frobenius.onPoints
    (nativePointHom k n hn) w n).ρ
  obtain ⟨short,hc⟩ := involution_conjugate_rootOne n hn t ht
  have hr : rootOne n hn short ^ 2=1 := by
    cases short
    · exact longRoot_sq n hn 1
    · exact shortRoot_sq n hn 1
  have hb := five_mul_lt_basic_root_tensor_displacement k hu (nativePointHom k n hn)
    (rootOne n hn short) hr short (nativePointHom_rootOne k n hn short)
    w n s hn hs hsn hwrap hp hne
  obtain ⟨g,hg⟩ := isConj_iff.mp hc
  have hrank : operatorFixedCodim (ρ (rootOne n hn short)) = operatorFixedCodim (ρ t) := by
    apply operatorFixedCodim_eq_of_equiv _ _ (LinearMap.GeneralLinearGroup.toLinearEquiv (Representation.asGroupHom ρ g))
    intro v
    change ρ g (ρ (rootOne n hn short) v) = ρ t (ρ g v)
    have hh : g * rootOne n hn short = t * g := by rw [←hg]; group
    change ((ρ g * ρ (rootOne n hn short)) : Module.End k _) v =
      ((ρ t * ρ g) : Module.End k _) v
    rw [←map_mul,←map_mul,hh]
  exact hb.trans_eq (congrArg (fun d => s*d) hrank)

end Triality.RestrictedWeights.Concrete
