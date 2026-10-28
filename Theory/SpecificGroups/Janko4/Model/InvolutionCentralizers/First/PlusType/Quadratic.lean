module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.IntrinsicCenter.Pairing
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.ActionKernel.OuterImageComparison.CoordinateConstruction


/-!
# The square form and six hyperbolic pairs in the first J₄ two-core

The actual seed normal closure has twelve noncentral generators, all with
square equal to its marked involution. Collection using the certified
commutator table gives the square polynomial: one linear term per generator
and one quadratic term per noncommuting pair. The existing central-quotient
coordinates identify this polynomial with the square of every actual element.

Twelve explicit binary vectors then give six orthogonal hyperbolic pairs.
Kernel reduction checks only this small Boolean table. Their ordered lifts
are actual square-one elements, distinct pairs commute, and each pair's
product squares to the marked involution. No new matrix computation or table
assumption is used. Generation and central-product recognition are subsequent
steps; the relations here alone do not assert the final group isomorphism.

Source: Aschbacher–Smith, combined manuscript, printed p.1172, 16.1.5(9),
and GLS3, Table 5.3i, printed p.270. The generator and commutator certificates
are reused from `NormalClosureControl`, with their ATLAS source attribution.
-/

@[expose] public section

open Subgroup
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares
open TwoCoreCentralizerData NormalClosureControl NormalClosureControl.IntrinsicCenter
open OuterImageComparison Janko4.Cardinality.KernelCount

namespace Janko4.InvolutionCentralizers.First.PlusType

/-- Recursive square polynomial of a binary word, in generator order. -/
def squareParity : {n : ℕ} → (Fin n → Bool) → (Fin n → Fin n → Bool) →
    (Fin n → Bool) → Bool
  | 0, _, _, _ => false
  | _ + 1, s, b, v => (v 0 && s 0) ^^
      (squareParity (fun i => s i.succ) (fun i j => b i.succ j.succ)
        (fun i => v i.succ) ^^ (v 0 && pairing (fun i => v i.succ) (fun j => b 0 j.succ)))

private theorem bit_mul {G : Type*} [Group G] (t : G) (ht : t ^ 2 = 1)
    (a b : Bool) : bit t (a ^^ b) = bit t a * bit t b := by
  cases a <;> cases b <;> simp [bit, ← pow_two, ht]

private theorem bit_commute {G : Type*} [Group G] (t : G)
    (ht : t ∈ center G) (b : Bool) (g : G) : Commute (bit t b) g := by
  cases b
  · exact Commute.one_left _
  · exact ((mem_center_iff.mp ht) g).symm

private theorem reverse_twist {G : Type*} [Group G] (a b t : G)
    (ht : t ^ 2 = 1) (v : Bool) (h : a * b = b * a * bit t v) :
    b * a = a * b * bit t v := by
  have hs : bit t v * bit t v = 1 := by
    cases v <;> simp [bit, ← pow_two, ht]
  rw [h, mul_assoc, hs, mul_one]

private theorem square_mul {G : Type*} [Group G] (a b t : G)
    (ht : t ∈ center G) (v : Bool) (h : b * a = a * b * bit t v) :
    (a * b) ^ 2 = a ^ 2 * b ^ 2 * bit t v := by
  simp only [pow_two]
  calc
    a * b * (a * b) = a * (b * a) * b := by simp only [mul_assoc]
    _ = a * (a * b * bit t v) * b := by rw [h]
    _ = a * a * (b * b) * bit t v := by
      simp only [mul_assoc]
      rw [(bit_commute t ht v b).eq]

/-- Squares of binary words follow solely from the generator squares and twists. -/
private theorem binaryProduct_square {G : Type*} [Group G] {n : ℕ}
    (e : Fin n → G) (s : Fin n → Bool) (b : Fin n → Fin n → Bool)
    (t : G) (ht : t ∈ center G) (ht2 : t ^ 2 = 1)
    (hs : ∀ i, e i ^ 2 = bit t (s i))
    (hb : ∀ i j, e j * e i = e i * e j * bit t (b i j))
    (v : Fin n → Bool) : binaryProduct e v ^ 2 = bit t (squareParity s b v) := by
  induction n with
  | zero => simp [binaryProduct, squareParity, bit]
  | succ n ih =>
    rw [binaryProduct_succ]
    have htail := ih (fun i => e i.succ) (fun i => s i.succ)
      (fun i j => b i.succ j.succ) (fun i => hs i.succ)
      (fun i j => hb i.succ j.succ) (fun i => v i.succ)
    have htwist := binaryProduct_twist (fun i => e i.succ) (fun i => v i.succ)
      (fun i => b 0 i.succ) (e 0) t ht ht2 (fun i => hb 0 i.succ)
    cases hv : v 0
    · simpa [hv, squareParity] using htail
    · simp only [if_true]
      rw [square_mul _ _ t ht _ htwist, hs 0, htail]
      simp only [squareParity, hv, Bool.true_and, bit_mul t ht2, mul_assoc]

/-- Commutators of binary words are the bilinear extension of the generator table. -/
private theorem binaryProduct_pair_twist {G : Type*} [Group G] {n : ℕ}
    (e : Fin n → G) (b : Fin n → Fin n → Bool)
    (t : G) (ht : t ∈ center G) (ht2 : t ^ 2 = 1)
    (hb : ∀ i j, e j * e i = e i * e j * bit t (b i j))
    (v w : Fin n → Bool) :
    binaryProduct e v * binaryProduct e w =
      binaryProduct e w * binaryProduct e v *
        bit t (pairing v (fun i => pairing w (b i))) := by
  apply binaryProduct_twist e v _ _ t ht ht2
  intro i
  exact reverse_twist _ _ _ ht2 _
    (binaryProduct_twist e w (b i) (e i) t ht ht2 (hb i))

private theorem conjugates_succ_square {G : Type*} [Group G]
    (x y u t : G) (ht : t ∈ center G) (hu : u ^ 2 = t) (i : Fin 12) :
    NormalClosureControl.conjugates x y u t i.succ ^ 2 = t := by
  have step (g z : G) (hz : z ^ 2 = t) : (g⁻¹ * z * g) ^ 2 = t := by
    calc
      (g⁻¹ * z * g) ^ 2 = g⁻¹ * z ^ 2 * g := by simp only [pow_two]; group
      _ = g⁻¹ * t * g := by rw [hz]
      _ = t := by rw [mul_assoc, ← (mem_center_iff.mp ht) g, inv_mul_cancel_left]
  fin_cases i <;> dsimp only [NormalClosureControl.conjugates,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.succ]
  all_goals repeat first | exact hu | apply step

/-- Every noncentral certified generator squares to the marked involution. -/
private theorem basis_succ_square (i : Fin 12) : basis i.succ ^ 2 = subgroupInvolution :=
  conjugates_succ_square _ _ _ _ involution_mem_center localSeed_sq i

/-- The twelve actual noncentral generators inside the seed normal closure. -/
def generator (i : Fin 12) : localNormalClosure := basisElement i.succ

/-- The ordered lift of a binary vector into the actual group. -/
def word (v : Fin 12 → Bool) : localNormalClosure := binaryProduct generator v

/-- The commutator matrix on the twelve noncentral coordinates. -/
def form (i j : Fin 12) : Bool := commutatorForm i.succ j.succ

/-- The square polynomial: linear generator-square terms and upper-triangular twists. -/
def quadratic (v : Fin 12 → Bool) : Bool := squareParity (fun _ => true) form v

/-- The bilinear commutator of two coordinate vectors. -/
def polar (v w : Fin 12 → Bool) : Bool := pairing v (fun i => pairing w (form i))

theorem centralWord_square : centralWord ^ 2 = 1 := Subtype.ext involution_pow_two

/-- The central marking is the involution already certified in the ambient model. -/
theorem centralWord_order : orderOf centralWord = 2 := by
  rw [← orderOf_injective localNormalClosure.subtype Subtype.val_injective]
  exact orderOf_subgroupInvolution

theorem centralWord_ne_one : centralWord ≠ 1 := by
  intro h
  have ho := centralWord_order
  rw [h, orderOf_one] at ho
  exact (by decide : (1 : ℕ) ≠ 2) ho

theorem generator_square (i : Fin 12) : generator i ^ 2 = centralWord :=
  Subtype.ext (basis_succ_square i)

theorem generator_twist (i j : Fin 12) :
    generator j * generator i = generator i * generator j * bit centralWord (form i j) := by
  apply Subtype.ext
  change basis j.succ * basis i.succ =
    basis i.succ * basis j.succ * ((bit centralWord (form i j) : localNormalClosure) : localSubgroup)
  have hc : ((bit centralWord (form i j) : localNormalClosure) : localSubgroup) =
      bit subgroupInvolution (form i j) := by cases form i j <;> rfl
  rw [hc]
  exact basis_twist i.succ j.succ

/-- The exact square of every ordered lift, proved in the actual group. -/
theorem word_square (v : Fin 12 → Bool) : word v ^ 2 = bit centralWord (quadratic v) :=
  binaryProduct_square generator (fun _ => true) form centralWord centralWord_mem_center
    centralWord_square generator_square generator_twist v

/-- The exact commutator of every two ordered lifts, proved in the actual group. -/
theorem word_twist (v w : Fin 12 → Bool) :
    word v * word w = word w * word v * bit centralWord (polar v w) :=
  binaryProduct_pair_twist generator form centralWord centralWord_mem_center centralWord_square
    generator_twist v w

/-- The same binary vector in the existing twelve-dimensional quotient coordinates. -/
def fieldVector (v : Fin 12 → Bool) : Multiplicative BinaryVector :=
  Multiplicative.ofAdd (fun i => if v i then 1 else 0)

private theorem coordinateBits_fieldVector (v : Fin 12 → Bool) :
    coordinateBits (fieldVector v) = Fin.cases false v := by
  funext i
  refine Fin.cases rfl (fun j => ?_) i
  change ((if v j then (1 : ZMod 2) else 0) == 1) = v j
  cases v j <;> rfl

/-- The ordered word realizes precisely its specified vector in the actual quotient. -/
theorem projection_word (v : Fin 12 → Bool) :
    projection (word v) = decodeCoordinates (fieldVector v) := by
  change projection (binaryProduct generator v) =
    binaryProduct quotientBasis (coordinateBits (fieldVector v))
  rw [coordinateBits_fieldVector, binaryProduct_succ quotientBasis,
    map_binaryProduct]
  change binaryProduct (fun i => projection (generator i)) v =
    1 * binaryProduct (fun i => quotientBasis i.succ) v
  rw [one_mul]
  rfl

/-- Coordinates of the actual word under the established quotient isomorphism. -/
theorem coordinates_word (v : Fin 12 → Bool) :
    coordinates (projection (word v)) = fieldVector v := by
  rw [projection_word]
  exact coordinates.apply_symm_apply (fieldVector v)

/-- Extract Boolean coordinates from the actual central quotient. -/
noncomputable def elementBits (g : localNormalClosure) : Fin 12 → Bool :=
  fun i => (coordinates (projection g)).toAdd i == 1

private theorem fieldVector_elementBits (g : localNormalClosure) :
    fieldVector (elementBits g) = coordinates (projection g) := by
  change (fun i => if (coordinates (projection g)).toAdd i == 1 then
    (1 : ZMod 2) else 0) = (coordinates (projection g)).toAdd
  funext i
  have h : ∀ a : ZMod 2, (if a == 1 then (1 : ZMod 2) else 0) = a := by decide +kernel
  exact h _

private theorem square_mul_zpow {G : Type*} [Group G] (t : G)
    (ht : t ∈ center G) (ht2 : t ^ 2 = 1) (y : G) (k : ℤ) :
    (y * t ^ k) ^ 2 = y ^ 2 := by
  have hc : Commute y (t ^ k) :=
    (show Commute y t from (mem_center_iff.mp ht) y).zpow_right k
  have hk2 : (t ^ k) ^ 2 = 1 := by
    calc
      (t ^ k) ^ (2 : ℕ) = (t ^ k) ^ (2 : ℤ) := (zpow_natCast (t ^ k) 2).symm
      _ = t ^ (k * (2 : ℤ)) := (zpow_mul t k 2).symm
      _ = t ^ ((2 : ℤ) * k) := by rw [mul_comm k]
      _ = (t ^ (2 : ℤ)) ^ k := zpow_mul t 2 k
      _ = (t ^ (2 : ℕ)) ^ k := congrArg (fun a : G => a ^ k) (zpow_natCast t 2)
      _ = 1 := by rw [ht2, one_zpow]
  rw [hc.mul_pow, hk2, mul_one]

/-- Multiplying by a central power does not change the square. -/
theorem square_eq_of_projection_eq (x y : localNormalClosure)
    (h : projection x = projection y) : x ^ 2 = y ^ 2 := by
  have hm : y⁻¹ * x ∈ centralPowers := by
    apply (QuotientGroup.eq_one_iff _).mp
    change projection (y⁻¹ * x) = 1
    rw [map_mul, map_inv, h, inv_mul_cancel]
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hm
  have hx : x = y * centralWord ^ k := by rw [hk, mul_inv_cancel_left]
  rw [hx]
  exact square_mul_zpow centralWord centralWord_mem_center centralWord_square y k


/-- The square quadratic formula holds for every element, in its actual quotient coordinates. -/
theorem square_eq_quadratic (g : localNormalClosure) :
    g ^ 2 = bit centralWord (quadratic (elementBits g)) := by
  calc
    g ^ 2 = word (elementBits g) ^ 2 := square_eq_of_projection_eq _ _ (by
      apply coordinates.injective
      rw [coordinates_word, fieldVector_elementBits])
    _ = bit centralWord (quadratic (elementBits g)) := word_square _

/-- Bit masks for the left vectors of six hyperbolic pairs. -/
def leftMask : Fin 6 → ℕ := ![3, 6, 97, 2116, 1045, 3676]

/-- Bit masks for the right vectors of six hyperbolic pairs. -/
def rightMask : Fin 6 → ℕ := ![18, 9, 140, 1418, 3585, 3452]

/-- Coordinate i corresponds to the certified generator with index i+1. -/
def maskBits (m : ℕ) : Fin 12 → Bool := fun i => m.testBit i.val

/-- Explicit hyperbolic vectors, with the Boolean index choosing the right vector. -/
def hyperbolicVector (i : Fin 6) (side : Bool) : Fin 12 → Bool :=
  maskBits (if side then rightMask i else leftMask i)

/-- Each of the twelve proposed vectors has zero square polynomial. -/
theorem hyperbolicVector_singular (i : Fin 6) (side : Bool) :
    quadratic (hyperbolicVector i side) = false := by
  revert i side
  decide +kernel

/-- The exact Gram matrix is the orthogonal sum of six hyperbolic planes. -/
theorem hyperbolicVector_polar (i j : Fin 6) (a b : Bool) :
    polar (hyperbolicVector i a) (hyperbolicVector j b) =
      (decide (i = j) && (a ^^ b)) := by
  revert i j a b
  decide +kernel

/-- Twelve specified elements of the actual seed normal closure. -/
def hyperbolicLift (i : Fin 6) (side : Bool) : localNormalClosure :=
  word (hyperbolicVector i side)

/-- The specified lifts are involutions (square one) in the actual group. -/
theorem hyperbolicLift_square (i : Fin 6) (side : Bool) :
    hyperbolicLift i side ^ 2 = 1 := by
  rw [hyperbolicLift, word_square, hyperbolicVector_singular]
  rfl

/-- Distinct pairs commute, and the two members of each pair have marked twist t. -/
theorem hyperbolicLift_twist (i j : Fin 6) (a b : Bool) :
    hyperbolicLift i a * hyperbolicLift j b =
      hyperbolicLift j b * hyperbolicLift i a *
        bit centralWord (decide (i = j) && (a ^^ b)) := by
  rw [hyperbolicLift, hyperbolicLift, word_twist, hyperbolicVector_polar]

/-- The two members of a pair have the exact nontrivial central twist. -/
theorem hyperbolicLift_pair_twist (i : Fin 6) :
    hyperbolicLift i false * hyperbolicLift i true =
      hyperbolicLift i true * hyperbolicLift i false * centralWord := by
  simpa only [decide_true, Bool.false_xor, Bool.and_self, bit, Bool.true_eq, if_true]
    using hyperbolicLift_twist i i false true

/-- Elements chosen from distinct hyperbolic pairs commute in the actual group. -/
theorem hyperbolicLift_commute {i j : Fin 6} (hij : i ≠ j) (a b : Bool) :
    Commute (hyperbolicLift i a) (hyperbolicLift j b) := by
  change hyperbolicLift i a * hyperbolicLift j b = hyperbolicLift j b * hyperbolicLift i a
  have h := hyperbolicLift_twist i j a b
  simpa only [hij, decide_false, Bool.false_and, bit, Bool.false_eq_true, if_false, mul_one]
    using h

/-- Each dihedral rotation squares to the specified central involution. -/
theorem hyperbolicLift_product_square (i : Fin 6) :
    (hyperbolicLift i false * hyperbolicLift i true) ^ 2 = centralWord := by
  have h := hyperbolicLift_twist i i true false
  have ht : hyperbolicLift i true * hyperbolicLift i false =
      hyperbolicLift i false * hyperbolicLift i true * bit centralWord true := by
    simpa only [decide_true, Bool.xor_false, Bool.and_self] using h
  rw [square_mul _ _ centralWord centralWord_mem_center true ht,
    hyperbolicLift_square, hyperbolicLift_square, one_mul, one_mul]
  rfl

/-- Coordinates of the twelve actual lifts under the existing quotient isomorphism. -/
theorem hyperbolicLift_coordinates (i : Fin 6) (side : Bool) :
    coordinates (projection (hyperbolicLift i side)) =
      fieldVector (hyperbolicVector i side) := coordinates_word _

end Janko4.InvolutionCentralizers.First.PlusType
