module

public import Theory.Representation.Triality.InnerDisplacement.PrimeToTwoCovers.CyclotomicTori.PhiSix.Descent
public import Theory.Representation.Triality.BinaryDegree.CarrierTransport
public import Theory.Representation.Triality.InnerDisplacement.PrimeToTwoCovers.CyclotomicTori.PhiTwelve.Lang

open Triality.Standard Triality.Standard.EvenField
open Triality.SimplyConnected Triality.SimplyConnected.Pinning
open Triality.BinaryDegree.CarrierTransport
open Triality.BinaryDegree.CarrierTransport.GeckSpin
open Triality.InnerDisplacement.PrimeToTwoCovers.CyclotomicTori.PhiSix
open RootPairing.SimpleGeckGroup
open Theory.AlgebraicGroup.StandardRootSystem
/-!
# Finite Lang witness for the sixth-cyclotomic triality word

The algebraic Spin Lang map supplies a solution over the algebraic closure.
The custom half-twist intertwining identifies the literal forward q-Frobenius
on the larger Geck field with the Spin action. Since the Weyl word has order
six, the solution is fixed by the ordinary q⁶-Frobenius. Coordinate descent
and the certified rational-root generation theorem therefore recover a point
in the actual finite split Geck group, preserving the orientation
`halfTwist x = x * rotation`.

Source: GLS3 §2.1 and §§2.2–2.4, with the genuine Geck–Spin comparison and
finite-field descent used only as a transport of the literal root-generated
carrier.
-/

@[expose] public section
noncomputable section
set_option maxHeartbeats 1000000
namespace Triality.InnerDisplacement.PrimeToTwoCovers.CyclotomicTori.PhiSix
private theorem half_positive (n : ℕ) (hn : 0 < n)
    (i : (typeDRootPairing_base 2).support) (t : ExtensionField (largerParameters n hn)) :
    halfTwist n hn (positive i t) =
      positive (typeD4DiagramBasePermutation i) (t ^ (2 ^ n)) := by
  unfold halfTwist forwardGraphHalf
  change diagramAutomorphism _
      (Triality.Standard.OuterOdd.coefficientSplit _ (coefficientFrobenius _ _ n) (positive i t)) = _
  rw [Triality.Standard.OuterOdd.coefficientSplit_positive, coefficientFrobenius_apply,
    diagramAutomorphism_positive]

private theorem half_negative (n : ℕ) (hn : 0 < n)
    (i : (typeDRootPairing_base 2).support) (t : ExtensionField (largerParameters n hn)) :
    halfTwist n hn (negative i t) =
      negative (typeD4DiagramBasePermutation i) (t ^ (2 ^ n)) := by
  unfold halfTwist forwardGraphHalf
  change diagramAutomorphism _
      (Triality.Standard.OuterOdd.coefficientSplit _ (coefficientFrobenius _ _ n) (negative i t)) = _
  rw [Triality.Standard.OuterOdd.coefficientSplit_negative, coefficientFrobenius_apply,
    diagramAutomorphism_negative]
end Triality.InnerDisplacement.PrimeToTwoCovers.CyclotomicTori.PhiSix
namespace Triality.InnerDisplacement.PrimeToTwoCovers.CyclotomicTori.PhiSix
open Triality.BinaryDegree.CarrierTransport
open Triality.BinaryDegree.CarrierTransport.GeckSpin
open Triality.Standard.OuterOdd
open Triality.SimplyConnected.GraphField
open Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.SimpleGeckGroup
private theorem local_geck_induction (P : Parameters) {p : SplitGroup P → Prop}
    (hp : ∀ i t, p (positive (typeDRootPairing_baseEquiv 2 i) t))
    (hn : ∀ i t, p (negative (typeDRootPairing_baseEquiv 2 i) t))
    (h1 : p 1) (hm : ∀ g h, p g → p h → p (g * h))
    (hi : ∀ g, p g → p g⁻¹) (g : SplitGroup P) : p g := by
  rcases g with ⟨g, hg⟩
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
      obtain ⟨⟨s, j⟩, t, rfl⟩ := hx
      obtain ⟨i, rfl⟩ := (typeDRootPairing_baseEquiv 2).surjective j
      cases s
      · exact hn i t
      · exact hp i t
  | one => exact h1
  | mul x y hx hy ihx ihy => exact hm ⟨x, hx⟩ ⟨y, hy⟩ ihx ihy
  | inv x hx ih => exact hi ⟨x, hx⟩ ih

private theorem half_intertwines {k : Type*} [Field k] [IsAlgClosed k] [CharP k 2]
    (n : ℕ) (hn : 0 < n) (e : SplitGroup (largerParameters n hn) →* Points k)
    (f : ExtensionField (largerParameters n hn) →+* k)
    (he : HasRootFormula f e) (g : SplitGroup (largerParameters n hn)) :
    e (halfTwist n hn g) = sigma k n (e g) := by
  apply local_geck_induction (largerParameters n hn)
    (p := fun x => e (halfTwist n hn x) = sigma k n (e x))
  · intro i t
    calc
      e (halfTwist n hn (positive (typeDRootPairing_baseEquiv 2 i) t)) =
          e (positive (typeDRootPairing_baseEquiv 2 (typeD4DiagramPermutation i))
            (t ^ (2 ^ n))) := by
              rw [half_positive n hn, typeD4DiagramBasePermutation_numbered]
      _ = positiveSimplePoint k (typeD4DiagramPermutation i) (f (t ^ (2 ^ n))) :=
        he.1 _ _
      _ = sigma k n (e (positive (typeDRootPairing_baseEquiv 2 i) t)) := by
        simp only [sigma_apply, Diagram.pinnedAut_positiveSimple,
          GraphField.frobenius_positiveSimple, he.1, map_pow]
  · intro i t
    calc
      e (halfTwist n hn (negative (typeDRootPairing_baseEquiv 2 i) t)) =
          e (negative (typeDRootPairing_baseEquiv 2 (typeD4DiagramPermutation i))
            (t ^ (2 ^ n))) := by
              rw [half_negative n hn, typeD4DiagramBasePermutation_numbered]
      _ = negativeSimplePoint k (typeD4DiagramPermutation i) (f (t ^ (2 ^ n))) :=
        he.2 _ _
      _ = sigma k n (e (negative (typeDRootPairing_baseEquiv 2 i) t)) := by
        simp only [sigma_apply, Diagram.pinnedAut_negativeSimple,
          GraphField.frobenius_negativeSimple, he.2, map_pow]
  · simp only [map_one]
  · intro g h hg hh
    rw [map_mul, map_mul, hg, hh]
    rw [e.map_mul]
    exact (map_mul (sigma k n) (e g) (e h)).symm
  · intro g hg
    rw [map_inv, map_inv, hg]
    rw [e.map_inv]
    exact (map_inv (sigma k n) (e g)).symm

end Triality.InnerDisplacement.PrimeToTwoCovers.CyclotomicTori.PhiSix
namespace Triality.InnerDisplacement.PrimeToTwoCovers.CyclotomicTori.PhiSix
open Triality.BinaryDegree.CarrierTransport
open Triality.BinaryDegree.CarrierTransport.GeckSpin
open Triality.Standard.OuterOdd
open Triality.SimplyConnected.GraphField
open Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.SimpleGeckGroup

theorem langWitness_nonempty (n : ℕ) (hn : 0 < n) (_hlarge : 1 < n) :
    Nonempty (LangWitness n hn) := by
  let K := AlgebraicClosure (ZMod 2)
  let hn2 : 0 < 2 * n := by omega
  let f := coefficientEmbedding K (2 * n) hn2
  let e := finiteComparison K f
  let c : Points K := e (rotation n hn)
  have he : HasRootFormula f e := finiteComparison_hasRootFormula K f
  have hhalf (g : SplitGroup (largerParameters n hn)) :
      e (halfTwist n hn g) = sigma K n (e g) :=
    half_intertwines n hn e f he g
  have hcf : sigma K n c = c := by
    change sigma K n (e (rotation n hn)) = e (rotation n hn)
    rw [← hhalf (rotation n hn), rotation_fixed]
  obtain ⟨y, hy⟩ :=
    Triality.InnerDisplacement.PrimeToTwoCovers.CyclotomicTori.PhiTwelve.graphField_lang_surjective
      K n hn c
  let z : Points K := y⁻¹
  have hz : sigma K n z = z * c := by
    dsimp [z]
    have hy' : y * (sigma K n y)⁻¹ = c := by simpa only [sigma_apply] using hy
    have hz' : (sigma K n y)⁻¹ = y⁻¹ * c := by
      calc
        (sigma K n y)⁻¹ = y⁻¹ * (y * (sigma K n y)⁻¹) := by group
        _ = y⁻¹ * c := by rw [hy']
    simpa only [sigma_apply, map_inv] using hz' 
  have hz2 : sigma K n (sigma K n z) = z * c ^ 2 := by
    calc
      sigma K n (sigma K n z) = sigma K n (z * c) := congrArg (sigma K n) hz
      _ = sigma K n z * sigma K n c := map_mul _ _ _
      _ = (z * c) * c := by rw [hz, hcf]
      _ = z * c ^ 2 := by simp [pow_two, mul_assoc]
  have hz3 : sigma K n (sigma K n (sigma K n z)) = z * c ^ 3 := by
    calc
      sigma K n (sigma K n (sigma K n z)) = sigma K n (z * c ^ 2) := congrArg (sigma K n) hz2
      _ = sigma K n z * sigma K n (c ^ 2) := map_mul _ _ _
      _ = (z * c) * c ^ 2 := by rw [hz, map_pow, hcf]
      _ = z * c ^ 3 := by simp [pow_succ, mul_assoc]
  have hF3 : frobeniusPointAut K (3 * n) z = z * c ^ 3 := by
    rw [← sigma_cube K n z]
    exact hz3
  have hFc : frobeniusPointAut K (3 * n) c = c := by
    rw [← sigma_cube K n c]
    calc
      sigma K n (sigma K n (sigma K n c)) =
          sigma K n (sigma K n c) := congrArg (sigma K n) (congrArg (sigma K n) hcf)
      _ = sigma K n c := congrArg (sigma K n) hcf
      _ = c := hcf
  have hF6 : frobeniusPointAut K (6 * n) z = z := by
    calc
      frobeniusPointAut K (6 * n) z =
          frobeniusPointAut K (3 * n) (frobeniusPointAut K (3 * n) z) := by
            have heq : 6 * n = 3 * n + 3 * n := by omega
            rw [heq, frobeniusPointAut_add_apply]
      _ = frobeniusPointAut K (3 * n) (z * c ^ 3) := by rw [hF3]
      _ = frobeniusPointAut K (3 * n) z *
            (frobeniusPointAut K (3 * n) c) ^ 3 := by rw [map_mul, map_pow]
      _ = (z * c ^ 3) * c ^ 3 := by rw [hF3, hFc]
      _ = z := by
        have hce : c ^ 6 = 1 := by
          have hr : (rotation n hn) ^ 6 = 1 := by
            rw [← pow_orderOf_eq_one (rotation n hn), orderOf_rotation n hn]
          simpa only [map_pow, e.map_one] using congrArg e hr
        calc
          (z * c ^ 3) * c ^ 3 = z * (c ^ 3 * c ^ 3) := by simp [mul_assoc]
          _ = z * c ^ 6 := by rw [← pow_add]
          _ = z := by rw [hce, mul_one]
  have hcoord : ∀ i j, naturalMatrix K z i j ∈ f.range := by
    apply (frobenius_fixed_iff_coordinates f z).mp
    have heq : 3 * (2 * n) = 6 * n := by omega
    rw [heq]
    exact hF6
  have hzmem : z ∈ rationalSimpleSubgroup f := rational_generation f z hcoord
  rw [← finiteComparison_range K f] at hzmem
  obtain ⟨g, hg⟩ := hzmem
  refine ⟨⟨g, ?_⟩⟩
  apply (finiteComparison_injective K f)
  calc
    e (halfTwist n hn g) = sigma K n (e g) := hhalf g
    _ = sigma K n z := by rw [hg]
    _ = z * c := hz
    _ = e g * e (rotation n hn) := by rw [← hg]
    _ = e (g * rotation n hn) := (e.map_mul _ _).symm
