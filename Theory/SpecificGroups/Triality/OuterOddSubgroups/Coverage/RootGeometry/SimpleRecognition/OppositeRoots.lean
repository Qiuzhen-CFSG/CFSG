module

public import Theory.SpecificGroups.Triality.OuterOddSubgroups.Coverage.RootGeometry.Basic

/-!
# Literal signed roots under triality opposition

The published longest relative Weyl word negates each split D₄ root. Its
parameter-preserving conjugation formula descends through the faithful map
from the original elementary central quotient. Thus it exchanges the two
literal root curves at each node, including over GF(8). The same split
negative-height separation proves that B is disjoint from the opposite U.

These are the geometric inputs to simple-root recognition by intersections
with minimal Borel overgroups. Source: Steinberg Theorems 30(1) and 36,
`refs/KGroup/GLS3/Chapter2St1.tex`, and GLS3 2.3.4–8 and §2.4,
`refs/KGroup/GLS3/chapter2.tex`.
-/

public section
open Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction
namespace Triality.Standard.OuterOdd.Coverage.RootGeometry.SimpleRecognition
open Parabolics ConcreteBruhat ConcreteBruhat.SplitNormalForm
noncomputable section
local instance : InvolutiveNeg (TypeDRootIndex 4) := (typeDRootPairing 2).indexNeg

private theorem carrierToSplit_conj (P : Parameters) (hp : P.prime = 2)
    (g x : Carrier P) :
    FixedDescent.carrierToSplit P hp ((MulAut.conj g) x) =
      (MulAut.conj (FixedDescent.carrierToSplit P hp g))
        (FixedDescent.carrierToSplit P hp x) := by
  simp only [MulAut.conj_apply, map_mul, map_inv]

private theorem carrierToSplit_rootElement (P : Parameters) (hp : P.prime = 2)
    (s : Bool) (i : Node) (t : RootField P i) :
    FixedDescent.carrierToSplit P hp (rootElement P hp s i t) =
      elementaryInclusion P (rootElementary P hp s i t) :=
  FixedDescent.carrierToSplit_toCarrier P hp _

private theorem opposition_conj_simple (f : ℕ) (hf : 0 < f)
    (i : Fin 4) (t : ExtensionField (binaryParameters f hf)) :
    splitRepresentative (binaryParameters f hf) (binaryParameters_prime f hf) (.r 3) * positiveRoot _ i t *
      (splitRepresentative (binaryParameters f hf) (binaryParameters_prime f hf) (.r 3))⁻¹ = negativeRoot _ i t := by
  apply Subtype.ext
  have h := splitRepresentative_rootCurveUnit_conjugation (binaryParameters f hf) (binaryParameters_prime f hf)
    (.r 3) (typeDSimpleRootIndex 2 i) t
  rw [TwoLocalGeometry.ApartmentStabilizer.opposition_root] at h
  simp only [← typeDRootPairing_baseEquiv_val,
    rootCurveUnit_simple, rootCurveUnit_neg_simple] at h
  exact h

private theorem map_three {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (x y z : G) (x' y' z' : H) (hx : e x = x') (hy : e y = y') (hz : e z = z') :
    e (x * y * z) = x' * y' * z' := by
  simp only [map_mul, hx, hy, hz]

private theorem opposition_conj_root_of_simple (P : Parameters) (hp : P.prime = 2)
    (h : ∀ (i : Fin 4) (t : ExtensionField P),
      splitRepresentative P hp (.r 3) * positiveRoot P i t *
        (splitRepresentative P hp (.r 3))⁻¹ = negativeRoot P i t)
    (i : Node) (t : RootField P i) :
    (MulAut.conj (weylRepresentative P hp (.r 3))) (rootElement P hp true i t) =
      rootElement P hp false i t := by
  have hs : (MulAut.conj (splitRepresentative P hp (.r 3)))
      (elementaryInclusion P (rootElementary P hp true i t)) =
      elementaryInclusion P (rootElementary P hp false i t) := by
    cases i with
    | central => exact h 1 t.val
    | arms =>
      exact map_three (MulAut.conj (splitRepresentative P hp (.r 3)))
        (positiveRoot P 0 t) (positiveRoot P 2 (fieldFrobenius P t))
        (positiveRoot P 3 (fieldFrobenius P (fieldFrobenius P t)))
        (negativeRoot P 0 t) (negativeRoot P 2 (fieldFrobenius P t))
        (negativeRoot P 3 (fieldFrobenius P (fieldFrobenius P t)))
        (h 0 t) (h 2 (fieldFrobenius P t))
        (h 3 (fieldFrobenius P (fieldFrobenius P t)))
  apply FixedDescent.carrierToSplit_injective P hp
  exact (carrierToSplit_conj P hp (weylRepresentative P hp (.r 3))
    (rootElement P hp true i t)).trans
    ((congrArg₂ (fun g x : SplitGroup P => (MulAut.conj g) x)
      (FixedDescent.carrierToSplit_representative P hp (.r 3))
      (carrierToSplit_rootElement P hp true i t)).trans
        (hs.trans (carrierToSplit_rootElement P hp false i t).symm))

theorem opposition_conj_positive_root (f : ℕ) (hf : 0 < f) (i : Node)
    (t : RootField (binaryParameters f hf) i) :
    (MulAut.conj (weylRepresentative (binaryParameters f hf) rfl (.r 3)))
      (rootElement _ rfl true i t) = rootElement _ rfl false i t :=
  opposition_conj_root_of_simple _ (binaryParameters_prime f hf)
    (opposition_conj_simple f hf) i t

theorem opposition_involution (P : Parameters) (hp : P.prime = 2) :
    weylRepresentative P hp (.r 3) * weylRepresentative P hp (.r 3) = 1 := by
  rw [← weylRepresentative_mul]
  have h : (DihedralGroup.r 3 : DihedralGroup 6) * .r 3 = 1 := by decide +kernel
  rw [h, weylRepresentative_one]

theorem disjoint_borel_opposite (f : ℕ) (hf : 0 < f) :
    Disjoint (borel (binaryParameters f hf))
      (oppositeUnipotent (binaryParameters f hf) (binaryParameters_prime f hf)) := by
  let P := binaryParameters f hf
  apply Subgroup.disjoint_def.mpr
  intro x hx hy
  obtain ⟨u, hu, he⟩ := hy
  subst x
  apply FixedDescent.carrierToSplit_injective P (binaryParameters_prime f hf)
  rw [map_one]
  apply Subgroup.disjoint_def.mp
    (CellSeparation.borel_inf_negative f hf (InputRealization.inputs P (binaryParameters_prime f hf)))
    ((FixedDescent.mem_descend_iff P (binaryParameters_prime f hf) (splitBorel P) _).mp hx)
  have he := (carrierToSplit_conj P (binaryParameters_prime f hf)
    (weylRepresentative P (binaryParameters_prime f hf) (.r 3)) u).trans
    (congrArg (fun g : SplitGroup P =>
      (MulAut.conj g) (FixedDescent.carrierToSplit P (binaryParameters_prime f hf) u))
      (FixedDescent.carrierToSplit_representative P (binaryParameters_prime f hf) (.r 3)))
  exact he.symm ▸ TwoLocalGeometry.ApartmentStabilizer.opposition_conj_positive f hf
    ((FixedDescent.mem_descend_iff P (binaryParameters_prime f hf) (positiveSubgroup P) u).mp hu)

private theorem conj_involutive {G : Type*} [Group G] (w : G) (hw : w * w = 1) :
    Function.Involutive (MulAut.conj w) := by
  have hi : w⁻¹ = w := inv_eq_of_mul_eq_one_left hw
  intro x
  change w * (w * x * w⁻¹) * w⁻¹ = x
  rw [hi]
  calc
    _ = (w * w) * x * (w * w) := by group
    _ = x := by rw [hw, one_mul, mul_one]

theorem opposition_conj_involutive (P : Parameters) (hp : P.prime = 2) :
    Function.Involutive (MulAut.conj (weylRepresentative P hp (.r 3))) :=
  conj_involutive _ (opposition_involution P hp)

/-- Opposition changes the sign and preserves the literal root parameter. -/
theorem opposition_conj_root (f : ℕ) (hf : 0 < f) (s : Bool) (i : Node)
    (t : RootField (binaryParameters f hf) i) :
    (MulAut.conj (weylRepresentative (binaryParameters f hf) rfl (.r 3)))
      (rootElement _ rfl s i t) = rootElement _ rfl (!s) i t := by
  cases s with
  | true => exact opposition_conj_positive_root f hf i t
  | false =>
    exact (congrArg (MulAut.conj (weylRepresentative (binaryParameters f hf) rfl (.r 3)))
      (opposition_conj_positive_root f hf i t).symm).trans
      (opposition_conj_involutive _ rfl _)

/-- The negative literal root groups lie in the published opposite subgroup. -/
theorem negative_mem_opposite (f : ℕ) (hf : 0 < f) (i : Node)
    (t : RootField (binaryParameters f hf) i) :
    rootElement _ rfl false i t ∈ oppositeUnipotent (binaryParameters f hf) rfl :=
  ⟨rootElement _ rfl true i t, positive_mem_unipotent _ rfl i t,
    opposition_conj_positive_root f hf i t⟩

private theorem map_twice_of_involutive {G : Type*} [Group G]
    (H : Subgroup G) (c : MulAut G) (hc : Function.Involutive c) :
    (H.map c.toMonoidHom).map c.toMonoidHom = H := by
  ext x
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    change c (c z) ∈ H
    rw [hc z]
    exact hz
  · intro hx
    exact ⟨c x, ⟨x, hx, rfl⟩, hc x⟩

/-- Applying the same literal opposition again recovers U. -/
theorem map_oppositeUnipotent_opposition (P : Parameters) (hp : P.prime = 2) :
    (oppositeUnipotent P hp).map
      (MulAut.conj (weylRepresentative P hp (.r 3))).toMonoidHom = unipotent P :=
  map_twice_of_involutive (unipotent P) _ (opposition_conj_involutive P hp)

end
end Triality.Standard.OuterOdd.Coverage.RootGeometry.SimpleRecognition
