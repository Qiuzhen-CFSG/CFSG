module

public import Theory.Representation.Triality.OuterDisplacement.ConcretePairedTensorSource.Halves
public import Theory.Representation.Triality.OuterDisplacement.ConcretePairedTensorSource.Coefficients
public import Theory.Representation.Triality.RestrictedWeights.ConcreteFinitePeriodSource
public import Theory.SpecificGroups.Triality.EvenFieldFixedResidual.NormalForm

/-!
# The actual inner-twisted triality tensor displacement

The native graph-field and coefficient equations instantiate the constructed
half-tensor equivalence. A nonzero weight supplies a factor of dimension at
least eight in the first half. The actual inner factor is retained in its
second-half intertwiner; Schur rigidity then gives the seven-sixteenths bound
for the supplied native involution. The following final source module derives
the weight period and nonzero weight from the original action.
Source: GLS3 2.8; Guralnick--Malle II, 3.5 and Lemma 8.6.
-/

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open D4RestrictedWeight
open Triality.SimplyConnected Triality.Standard Triality.Standard.OuterOdd
open Triality.RestrictedWeights Triality.RestrictedWeights.Concrete
open Triality.RestrictedWeights.SteinbergTensors
open Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor
namespace Triality.OuterDisplacement.ConcretePairedTensorSource
public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
variable (k : Type u) [Field k] [IsAlgClosed k] [CharP k 2]
variable (hu : IsUniversalVersion (groupVariety k))

theorem half_finrank_ge (m : ℕ) (hm : 0<m) (w : ℕ → BasicWeight)
    (hwrap : ∀ i,w (i+2*m)=diagramAction (w i))
    (hp : Function.Periodic w (3*m)) (hne : ∃ i,w i≠zeroWeight)
    {G : Type*} [Group G] (ι : G →* Points k) :
    8≤Module.finrank k (tensor (basicFamily k hu).factor
      (finiteGeometry k hu).frobenius.onPoints ι w m) := by
  obtain ⟨i,hi⟩ := hne
  have hd : Function.Periodic (fun j=>InnerDisplacement.minimumDegree (w j)) m := by
    intro j
    change InnerDisplacement.minimumDegree (w (j+m))=InnerDisplacement.minimumDegree (w j)
    rw [show j+m=m+j by omega,PairedSource.half_weight w m hwrap hp]
    exact (InnerDisplacement.minimumDegree_diagram _).trans (InnerDisplacement.minimumDegree_diagram _)
  have hnz : w (i%m)≠zeroWeight := by
    have he := hd.map_mod_nat i
    have hh := InnerDisplacement.minimumDegree_nonzero (w i) hi
    rw [←he] at hh
    intro hz
    simp [hz,InnerDisplacement.minimumDegree] at hh
  have h8 := (basic_finrank_lower_bounds k hu (w (i%m)) hnz).1
  rw [finrank_tensor]
  exact h8.trans (Finset.single_le_prod' (f := fun j=>Module.finrank k ((basicFamily k hu).factor (w j)).Space)
    (fun j _=> ((basicFamily k hu).factor (w j)).finrank_pos)
    (Finset.mem_range.mpr (Nat.mod_lt i hm)))

theorem tensor_ratio_of_inner_coefficient_period
    (n : ℕ) (hn : 0<n) (m : ℕ) (hm : 0<m) (hnm : n=2*m)
    (a : Fin n → BasicWeight)
    (hp : Function.Periodic (extendWeights hn a) (3*m))
    (hne : ∃ i,extendWeights hn a i≠zeroWeight)
    (α : MulAut (BinaryCarrier n hn)) (hα : α^2=1) (x : BinaryCarrier n hn)
    (hform : ∀ g,α g=x*coefficientAction (binaryParameters n hn)
      (EvenField.coefficientFrobenius n hn (3*m)) g*x⁻¹)
    (T : Module.End k (tensor (basicFamily k hu).factor
      (finiteGeometry k hu).frobenius.onPoints (nativePointHom k n hn) (extendWeights hn a) n))
    (hT : T*T=1)
    (hTi : ∀ g v,T ((tensor (basicFamily k hu).factor
      (finiteGeometry k hu).frobenius.onPoints (nativePointHom k n hn) (extendWeights hn a) n).ρ g v)=
      (tensor (basicFamily k hu).factor
      (finiteGeometry k hu).frobenius.onPoints (nativePointHom k n hn) (extendWeights hn a) n).ρ (α g) (T v)) :
    7*Module.finrank k (tensor (basicFamily k hu).factor
      (finiteGeometry k hu).frobenius.onPoints (nativePointHom k n hn) (extendWeights hn a) n) ≤
    16*Module.finrank k (LinearMap.range (T-LinearMap.id)) := by
  subst n
  let ρ := (tensor (basicFamily k hu).factor
    (finiteGeometry k hu).frobenius.onPoints (nativePointHom k (2*m) hn) (extendWeights hn a) (2*m)).ρ
  let π := (tensor (basicFamily k hu).factor
    (finiteGeometry k hu).frobenius.onPoints (nativePointHom k (2*m) hn) (extendWeights hn a) m).ρ
  let δ := coefficientAction (binaryParameters (2*m) hn)
    (EvenField.coefficientFrobenius (2*m) hn (3*m))
  let e := PairedSource.tensorHalvesEquiv (algebraicGeometry k hu) (ordinaryFrobenius k hu)
    (pinnedTriality k hu) (basicFamily k hu) (finiteGeometry k hu).commute
    (nativePointHom k (2*m) hn) m (nativePointHom_graphField_fixed k hu (2*m) hn)
    δ (nativePointHom_frobenius_pow k (2*m) hn (3*m)) (extendWeights hn a)
    (extendWeights_wrap hn a) hp
  let f := PairedSource.innerTwistedPairEquiv ρ π δ α x hform e
  let := native_tensor_irreducible k hu (2*m) hn a
  exact PairedSource.paired_rank_ratio ρ π α (fun g=>DFunLike.congr_fun hα g) f
    T hT hTi (half_finrank_ge k hu m hm (extendWeights hn a) (extendWeights_wrap hn a) hp hne _)

end
end Triality.OuterDisplacement.ConcretePairedTensorSource
