module

public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.Structure.QuadraticData
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-!
# The twisted Golay quadratic space

The addition on `QuadraticCoordinates` is the source's twisted sum. The
half-overlap cocycle identity proves associativity; the cocode intersection
is bilinear and vanishes when one input is the all-ones codeword. Polarization
then proves the quadratic and bilinear laws. Perfect cocode duality proves
nonsingularity, and the zero-code coordinates form a 12-dimensional totally
singular subspace in this 24-dimensional space.

The last three lemmas simplify the proposed word coordinates. They make no
assumption about, and do not assert, multiplication of the actual permutations.

Source: Aschbacher, *Sporadic Groups*, Exercise 4.6, printed p. 64, and
Section 27, printed pp. 144–145. The Golay and cocode APIs used here are the
attributed ATLAS ports imported through `QuadraticData`.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open Atlas.Fischer Atlas.Codes
noncomputable section
namespace Sporadic.Monster.Construction.TrialitySpin

private theorem bit_add_self (s : Bit) : s + s = 0 := by exact CharTwo.add_self_eq_zero s
private theorem bit_square (s : Bit) : s * s = s := by revert s; decide

@[simp] theorem intersectionCocode_zero_left (a : golay) : intersectionCocode 0 a = 0 := by
  unfold intersectionCocode
  simp only [ZeroMemClass.coe_zero, Pi.zero_apply, zero_mul]
  exact (Submodule.Quotient.mk_eq_zero golay).mpr golay.zero_mem

theorem intersectionCocode_comm (a b : golay) : intersectionCocode a b = intersectionCocode b a := by
  simp only [intersectionCocode, mul_comm]

@[simp] theorem intersectionCocode_zero_right (a : golay) : intersectionCocode a 0 = 0 := by
  rw [intersectionCocode_comm, intersectionCocode_zero_left]

theorem intersectionCocode_add_left (a b c : golay) :
    intersectionCocode (a + b) c = intersectionCocode a c + intersectionCocode b c := by
  unfold intersectionCocode
  rw [← Submodule.Quotient.mk_add]
  congr 1
  funext p
  exact add_mul (a.val p) (b.val p) (c.val p)

theorem intersectionCocode_add_right (a b c : golay) :
    intersectionCocode a (b + c) = intersectionCocode a b + intersectionCocode a c := by
  simp only [intersectionCocode_comm a, intersectionCocode_add_left]

@[simp] theorem intersectionCocode_self (a : golay) : intersectionCocode a a = 0 := by
  unfold intersectionCocode
  simp only [bit_square]
  exact Submodule.Quotient.mk_eq_zero golay |>.mpr a.prop

@[simp] theorem intersectionCocode_one_left (a : golay) : intersectionCocode golayOne a = 0 := by
  change Submodule.Quotient.mk (fun p => 1 * a.val p) = 0
  simp only [one_mul]
  exact Submodule.Quotient.mk_eq_zero golay |>.mpr a.prop

@[simp] theorem intersectionCocode_one_right (a : golay) : intersectionCocode a golayOne = 0 := by
  rw [intersectionCocode_comm, intersectionCocode_one_left]

@[simp] theorem intersectionCocode_smul_one_left (s : Bit) (a : golay) :
    intersectionCocode (s • golayOne) a = 0 := by
  have hs : s = 0 ∨ s = 1 := by revert s; decide
  rcases hs with rfl | rfl <;> simp

@[simp] theorem intersectionCocode_smul_one_right (s : Bit) (a : golay) :
    intersectionCocode a (s • golayOne) = 0 := by
  rw [intersectionCocode_comm, intersectionCocode_smul_one_left]

@[simp] theorem cocodePairing_zero_left (c : Cocode) : cocodePairing 0 c = 0 := by
  simp [cocodePairing]

@[simp] theorem cocodePairing_zero_right (a : golay) : cocodePairing a 0 = 0 := by
  simp [cocodePairing]

theorem cocodePairing_add_left (a b : golay) (c : Cocode) :
    cocodePairing (a + b) c = cocodePairing a c + cocodePairing b c := by
  simp [cocodePairing]

theorem cocodePairing_add_right (a : golay) (c f : Cocode) :
    cocodePairing a (c + f) = cocodePairing a c + cocodePairing a f := by
  simp [cocodePairing]

@[simp] theorem cocodePairing_one (c : Cocode) : cocodePairing golayOne c = cocodeParity c := rfl

@[simp] theorem cocodePairing_smul_one (s : Bit) (c : Cocode) :
    cocodePairing (s • golayOne) c = s * cocodeParity c := by
  simp [cocodePairing, cocodeParity]

theorem cocodePairing_intersection (a b c : golay) :
    cocodePairing a (intersectionCocode b c) = parkerTripleIntersection b c a :=
  associatorFunctional_apply b c a

@[simp] theorem cocodeParity_intersection (a b : golay) :
    cocodeParity (intersectionCocode a b) = 0 := by
  rw [← cocodePairing_one, cocodePairing_intersection, parkerTripleIntersection_cycle,
    parkerTripleIntersection_one]

@[simp] theorem golayHalfOverlap_zero_right (a : golay) : golayHalfOverlap a 0 = 0 := by
  rw [golayHalfOverlap_symmetric, golayHalfOverlap_zero_left]

@[simp] theorem golayHalfOverlap_self (a : golay) : golayHalfOverlap a a = 0 := by
  have h := golayQuarterWeight_add a a
  simpa only [parkerGolay_add_self, golayQuarterWeight_zero, bit_add_self, zero_add] using h.symm

@[simp] theorem golayQuarterWeight_one : golayQuarterWeight golayOne = 0 := by
  have h := congrArg Prod.snd parkerOmega_square
  simpa only [parkerLoopMultiply_square, parkerOmega] using h

@[simp] theorem golayHalfOverlap_one_right (a : golay) : golayHalfOverlap a golayOne = 0 := by
  rw [golayHalfOverlap_symmetric, golayHalfOverlap_one]

@[simp] theorem golayHalfOverlap_add_smul_one_left (a b : golay) (s : Bit) :
    golayHalfOverlap (a + s • golayOne) b = golayHalfOverlap a b := by
  have hs : s = 0 ∨ s = 1 := by revert s; decide
  rcases hs with rfl | rfl
  · simp
  · simp only [one_smul, golayHalfOverlap_add_left, golayHalfOverlap_one, add_zero]
    rw [parkerTripleIntersection_cycle, parkerTripleIntersection_cycle _ _ golayOne,
      parkerTripleIntersection_one, add_zero]

@[simp] theorem golayHalfOverlap_add_smul_one_right (a b : golay) (s : Bit) :
    golayHalfOverlap a (b + s • golayOne) = golayHalfOverlap a b := by
  rw [golayHalfOverlap_symmetric, golayHalfOverlap_add_smul_one_left,
    golayHalfOverlap_symmetric]

@[simp] theorem golayQuarterWeight_smul_one (s : Bit) : golayQuarterWeight (s • golayOne) = 0 := by
  have hs : s = 0 ∨ s = 1 := by revert s; decide
  rcases hs with rfl | rfl <;> simp

@[simp] theorem golayQuarterWeight_add_smul_one (a : golay) (s : Bit) :
    golayQuarterWeight (a + s • golayOne) = golayQuarterWeight a := by
  have hs : s = 0 ∨ s = 1 := by revert s; decide
  rcases hs with rfl | rfl <;> simp [golayQuarterWeight_add]


@[simp] theorem coordinateSum_zero_left (x : QuadraticCoordinates) :
    coordinateSum coordinateZero x = x := by
  ext <;> simp [coordinateSum, coordinateZero]

@[simp] theorem coordinateSum_zero_right (x : QuadraticCoordinates) :
    coordinateSum x coordinateZero = x := by
  ext <;> simp [coordinateSum, coordinateZero]

theorem coordinateSum_comm (x y : QuadraticCoordinates) :
    coordinateSum x y = coordinateSum y x := by
  ext
  · simp only [coordinateSum, golayHalfOverlap_symmetric x.code y.code, add_comm x.code y.code]
  · simp only [coordinateSum, intersectionCocode_comm x.code y.code, add_comm x.cocode y.cocode]

private theorem add_five_rearrange {A : Type*} [AddCommMonoid A] (a b c d e : A) :
    (a + b + d) + c + e = a + (b + c) + (d + e) := by
  ac_rfl

private theorem add_five_rearrange' {A : Type*} [AddCommMonoid A] (a b c d e : A) :
    a + (b + c + d) + e = a + (b + c) + (d + e) := by
  ac_rfl

private theorem add_four_rearrange {A : Type*} [AddCommMonoid A] (p q r u : A) :
    p + (q + r + u) = r + (p + q + u) := by ac_rfl

theorem golayHalfOverlap_cocycle (a b c : golay) :
    golayHalfOverlap a b + golayHalfOverlap (a + b) c =
      golayHalfOverlap b c + golayHalfOverlap a (b + c) := by
  rw [golayHalfOverlap_add_left, golayHalfOverlap_symmetric a (b + c),
    golayHalfOverlap_add_left, golayHalfOverlap_symmetric b a,
    golayHalfOverlap_symmetric c a, parkerTripleIntersection_cycle b c a]
  exact add_four_rearrange _ _ _ _

theorem coordinateSum_assoc (x y z : QuadraticCoordinates) :
    coordinateSum (coordinateSum x y) z = coordinateSum x (coordinateSum y z) := by
  apply QuadraticCoordinates.ext
  · simp only [coordinateSum, golayHalfOverlap_add_smul_one_left,
      golayHalfOverlap_add_smul_one_right]
    rw [add_five_rearrange, add_five_rearrange', ← add_smul, ← add_smul,
      golayHalfOverlap_cocycle]
  · simp only [coordinateSum, intersectionCocode_add_left, intersectionCocode_add_right,
      intersectionCocode_smul_one_left, intersectionCocode_smul_one_right, add_zero]
    ac_rfl

@[simp] theorem coordinateSum_self (x : QuadraticCoordinates) :
    coordinateSum x x = coordinateZero := by
  ext
  · simp [coordinateSum, coordinateZero, parkerGolay_add_self]
  · have hc : x.cocode + x.cocode = 0 := by
      rw [← two_nsmul, ← Nat.cast_smul_eq_nsmul Bit]
      exact zero_smul Bit x.cocode
    simp [coordinateSum, coordinateZero, hc]

instance quadraticCoordinatesZero : Zero QuadraticCoordinates := ⟨coordinateZero⟩
instance quadraticCoordinatesAdd : Add QuadraticCoordinates := ⟨coordinateSum⟩
instance quadraticCoordinatesNeg : Neg QuadraticCoordinates := ⟨id⟩

instance quadraticCoordinatesAddCommGroup : AddCommGroup QuadraticCoordinates where
  add := coordinateSum
  zero := coordinateZero
  neg := id
  add_assoc := coordinateSum_assoc
  zero_add := coordinateSum_zero_left
  add_zero := coordinateSum_zero_right
  add_comm := coordinateSum_comm
  neg_add_cancel := coordinateSum_self
  nsmul := nsmulRec
  zsmul := zsmulRec

theorem quadraticCoordinates_add_eq (x y : QuadraticCoordinates) :
    x + y = coordinateSum x y := rfl

theorem quadraticCoordinates_zero_eq : (0 : QuadraticCoordinates) = coordinateZero := rfl

instance quadraticCoordinatesModule : Module Bit QuadraticCoordinates :=
  AddCommGroup.zmodModule (n := 2) (fun x => by
    rw [two_nsmul]; exact coordinateSum_self x)

/-- The product here is only an equivalence of sets, used to count coordinates. -/
def quadraticCoordinatesEquiv : QuadraticCoordinates ≃ golay × Cocode where
  toFun x := (x.code, x.cocode)
  invFun x := ⟨x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance quadraticCoordinatesFinite : Finite QuadraticCoordinates :=
  Finite.of_equiv (golay × Cocode) quadraticCoordinatesEquiv.symm

theorem quadraticCoordinates_card : Nat.card QuadraticCoordinates = 2 ^ 24 := by
  rw [Nat.card_congr quadraticCoordinatesEquiv, Nat.card_prod, golay_card, cocode_card]
  norm_num

theorem quadraticCoordinates_finrank : Module.finrank Bit QuadraticCoordinates = 24 := by
  have h := Module.natCard_eq_pow_finrank (K := Bit) (V := QuadraticCoordinates)
  rw [quadraticCoordinates_card] at h
  have hb : Nat.card Bit = 2 := by simp [Bit]
  rw [hb] at h
  exact (Nat.pow_right_injective (by decide : 1 < 2) h).symm

@[simp] theorem cocodePairing_intersection_self_left (a b : golay) :
    cocodePairing a (intersectionCocode a b) = 0 := by
  rw [cocodePairing_intersection, parkerTripleIntersection_cycle,
    parkerTripleIntersection_cycle, parkerTripleIntersection_repeat]

@[simp] theorem cocodePairing_intersection_self_right (a b : golay) :
    cocodePairing b (intersectionCocode a b) = 0 := by
  rw [cocodePairing_intersection, parkerTripleIntersection_repeat]

@[simp] theorem coordinateQuadratic_zero : coordinateQuadratic 0 = 0 := by
  simp [coordinateQuadratic, quadraticCoordinates_zero_eq, coordinateZero]

@[simp] theorem coordinatePolar_zero_left (x : QuadraticCoordinates) :
    coordinatePolar 0 x = 0 := by
  simp [coordinatePolar, quadraticCoordinates_zero_eq, coordinateZero]

@[simp] theorem coordinatePolar_zero_right (x : QuadraticCoordinates) :
    coordinatePolar x 0 = 0 := by
  simp [coordinatePolar, quadraticCoordinates_zero_eq, coordinateZero]

theorem coordinatePolar_comm (x y : QuadraticCoordinates) :
    coordinatePolar x y = coordinatePolar y x := by
  unfold coordinatePolar
  rw [golayHalfOverlap_symmetric]
  ac_rfl

theorem coordinatePolar_add_left (x y z : QuadraticCoordinates) :
    coordinatePolar (x + y) z = coordinatePolar x z + coordinatePolar y z := by
  simp only [quadraticCoordinates_add_eq, coordinatePolar, coordinateSum]
  simp only [golayQuarterWeight_add_smul_one, golayHalfOverlap_add_smul_one_left]
  simp only [cocodePairing_add_left, cocodePairing_add_right, cocodePairing_smul_one,
    cocodePairing_intersection, map_add, cocodeParity_intersection, add_zero,
    golayQuarterWeight_add, golayHalfOverlap_add_left]
  ring_nf
  simp

theorem coordinatePolar_add_right (x y z : QuadraticCoordinates) :
    coordinatePolar x (y + z) = coordinatePolar x y + coordinatePolar x z := by
  rw [coordinatePolar_comm, coordinatePolar_add_left,
    coordinatePolar_comm y x, coordinatePolar_comm z x]

theorem coordinateQuadratic_add (x y : QuadraticCoordinates) :
    coordinateQuadratic (x + y) =
      coordinateQuadratic x + coordinateQuadratic y + coordinatePolar x y := by
  simp only [quadraticCoordinates_add_eq, coordinateQuadratic, coordinatePolar, coordinateSum]
  simp only [golayQuarterWeight_add_smul_one]
  simp only [golayQuarterWeight_add,
    cocodePairing_add_left, cocodePairing_add_right, cocodePairing_smul_one,
    cocodePairing_intersection_self_left, cocodePairing_intersection_self_right,
    map_add, cocodeParity_intersection, add_zero, mul_zero]
  ring_nf
  simp

/-- The source commutator formula, as a bilinear form for the twisted addition. -/
def coordinatePolarForm : LinearMap.BilinForm Bit QuadraticCoordinates :=
  let f : QuadraticCoordinates →+ QuadraticCoordinates →ₗ[Bit] Bit :=
    { toFun := fun x => AddMonoidHom.toZModLinearMap 2
        { toFun := coordinatePolar x
          map_zero' := coordinatePolar_zero_right x
          map_add' := coordinatePolar_add_right x }
      map_zero' := by ext; exact coordinatePolar_zero_left _
      map_add' := fun x y => by ext z; exact coordinatePolar_add_left x y z }
  f.toZModLinearMap 2

@[simp] theorem coordinatePolarForm_apply (x y : QuadraticCoordinates) :
    coordinatePolarForm x y = coordinatePolar x y := rfl

/-- The source square function, with its quadratic laws proved. -/
def coordinateQuadraticForm : QuadraticForm Bit QuadraticCoordinates where
  toFun := coordinateQuadratic
  toFun_smul s x := by
    have hs : s = 0 ∨ s = 1 := by revert s; decide
    rcases hs with rfl | rfl <;> simp
  exists_companion' := ⟨coordinatePolarForm, coordinateQuadratic_add⟩

@[simp] theorem coordinateQuadraticForm_apply (x : QuadraticCoordinates) :
    coordinateQuadraticForm x = coordinateQuadratic x := rfl

theorem coordinateQuadraticForm_polar : coordinateQuadraticForm.polarBilin = coordinatePolarForm := by
  ext x y
  change coordinateQuadratic (x + y) - coordinateQuadratic x - coordinateQuadratic y =
    coordinatePolar x y
  rw [coordinateQuadratic_add]
  abel

theorem cocodePairing_separates_code (a : golay) (h : ∀ c, cocodePairing a c = 0) : a = 0 := by
  apply (Module.forall_dual_apply_eq_zero_iff Bit a).mp
  intro f
  simpa only [cocodePairing, LinearEquiv.apply_symm_apply] using h (cocodeDualEquiv.symm f)

theorem cocodePairing_separates_cocode (c : Cocode) (h : ∀ a, cocodePairing a c = 0) : c = 0 := by
  apply cocodeDualEquiv.injective
  ext a
  simpa only [cocodePairing, map_zero, LinearMap.zero_apply] using h a

theorem coordinatePolar_separates (x : QuadraticCoordinates)
    (h : ∀ y, coordinatePolar x y = 0) : x = 0 := by
  have ha : x.code + golayQuarterWeight x.code • golayOne = 0 := by
    apply cocodePairing_separates_code
    intro c
    have hc := h ⟨0,c⟩
    simpa only [coordinatePolar, cocodePairing_zero_left, golayQuarterWeight_zero,
      golayHalfOverlap_zero_right, mul_zero, zero_mul, zero_add, add_zero,
      cocodePairing_add_left, cocodePairing_smul_one, mul_comm] using hc
  have hq : golayQuarterWeight x.code = 0 := by
    have hh := congrArg golayQuarterWeight ha
    simpa only [golayQuarterWeight_add_smul_one, golayQuarterWeight_zero] using hh
  have hx : x.code = 0 := by simpa only [hq, zero_smul, add_zero] using ha
  have hp : cocodeParity x.cocode = 0 := by
    have hh := h ⟨golayOne, 0⟩
    simpa only [coordinatePolar, hx, cocodePairing_one, cocodePairing_zero_right,
      golayQuarterWeight_one, golayQuarterWeight_zero, golayHalfOverlap_zero_left,
      mul_zero, add_zero] using hh
  have hc : x.cocode = 0 := by
    apply cocodePairing_separates_cocode
    intro a
    simpa only [coordinatePolar, hx, hp, cocodePairing_zero_right,
      golayQuarterWeight_zero, golayHalfOverlap_zero_left, zero_mul, mul_zero,
      add_zero] using h ⟨a, 0⟩
  apply QuadraticCoordinates.ext
  · exact hx
  · exact hc

/-- Nonsingularity of the source polar form on the actual twisted vector space. -/
theorem coordinatePolarForm_nondegenerate : coordinatePolarForm.Nondegenerate := by
  constructor
  · exact coordinatePolar_separates
  · intro x hx
    apply coordinatePolar_separates x
    intro y
    rw [coordinatePolar_comm]
    exact hx y

theorem coordinateQuadraticForm_nonsingular : coordinateQuadraticForm.polarBilin.Nondegenerate := by
  rw [coordinateQuadraticForm_polar]
  exact coordinatePolarForm_nondegenerate

/-- The cocode embeds linearly as the coordinates whose code component is zero. -/
def cocodeCoordinates : Cocode →ₗ[Bit] QuadraticCoordinates :=
  AddMonoidHom.toZModLinearMap 2
    { toFun := fun c => ⟨0,c⟩
      map_zero' := rfl
      map_add' := fun c f => by
        apply QuadraticCoordinates.ext <;> simp [quadraticCoordinates_add_eq, coordinateSum] }

@[simp] theorem cocodeCoordinates_apply (c : Cocode) : cocodeCoordinates c = ⟨0,c⟩ := rfl

theorem cocodeCoordinates_injective : Function.Injective cocodeCoordinates := by
  intro c f h
  exact congrArg QuadraticCoordinates.cocode h

/-- The explicit maximal totally singular subspace exhibiting plus type. -/
def coordinateSingularSubspace : Submodule Bit QuadraticCoordinates := cocodeCoordinates.range

theorem mem_coordinateSingularSubspace (x : QuadraticCoordinates) :
    x ∈ coordinateSingularSubspace ↔ x.code = 0 := by
  constructor
  · rintro ⟨c,rfl⟩
    rfl
  · intro hx
    refine ⟨x.cocode, ?_⟩
    apply QuadraticCoordinates.ext
    · exact hx.symm
    · rfl

theorem coordinateSingularSubspace_finrank : Module.finrank Bit coordinateSingularSubspace = 12 := by
  exact (LinearEquiv.ofInjective cocodeCoordinates cocodeCoordinates_injective).finrank_eq.symm.trans
    cocode_finrank

theorem coordinateSingularSubspace_totallySingular (x : QuadraticCoordinates)
    (hx : x ∈ coordinateSingularSubspace) : coordinateQuadraticForm x = 0 := by
  have hc := (mem_coordinateSingularSubspace x).mp hx
  simp [coordinateQuadratic, hc]

/-- A nonsingular 24-dimensional quadratic space with a half-dimensional totally
singular subspace, i.e. the plus type required in Exercise 4.6 and Section 27. -/
theorem coordinateQuadraticForm_plusType :
    coordinateQuadraticForm.polarBilin.Nondegenerate ∧
    Module.finrank Bit QuadraticCoordinates = 24 ∧
    ∃ W : Submodule Bit QuadraticCoordinates, Module.finrank Bit W = 12 ∧
      ∀ x ∈ W, coordinateQuadraticForm x = 0 :=
  ⟨coordinateQuadraticForm_nonsingular, quadraticCoordinates_finrank,
    coordinateSingularSubspace, coordinateSingularSubspace_finrank,
    coordinateSingularSubspace_totallySingular⟩

/-- The proposed product representative has exactly the twisted sum coordinates,
including the all-ones and intersection corrections. -/
theorem q1WordCoordinates_sum (d e : ParkerLoop) (t s : ParkerBit) (c f : Cocode) :
    q1WordCoordinates (d.1 + e.1, 0) (t + s + golayHalfOverlap d.1 e.1)
      (c + f + intersectionCocode d.1 e.1) =
    coordinateSum (q1WordCoordinates d t c) (q1WordCoordinates e s f) := by
  apply QuadraticCoordinates.ext
  · simp only [q1WordCoordinates, coordinateSum, golayHalfOverlap_add_smul_one_left,
      golayHalfOverlap_add_smul_one_right, add_smul]
    ac_rfl
  · simp only [q1WordCoordinates, coordinateSum, intersectionCocode_add_left,
      intersectionCocode_add_right, intersectionCocode_smul_one_left,
      intersectionCocode_smul_one_right, add_zero]

/-- The square exponent expressed directly in word parameters. -/
theorem q1WordCoordinates_quadratic (d : ParkerLoop) (t : ParkerBit) (c : Cocode) :
    coordinateQuadratic (q1WordCoordinates d t c) =
      (1 + cocodeParity c) * golayQuarterWeight d.1 + cocodePairing d.1 c +
        t * cocodeParity c := by
  simp only [coordinateQuadratic, q1WordCoordinates, golayQuarterWeight_add_smul_one,
    cocodePairing_add_left, cocodePairing_smul_one]
  ring

/-- The commutator exponent expressed directly in word parameters. -/
theorem q1WordCoordinates_polar (d e : ParkerLoop) (t s : ParkerBit) (c f : Cocode) :
    coordinatePolar (q1WordCoordinates d t c) (q1WordCoordinates e s f) =
      cocodePairing e.1 c + cocodePairing d.1 f +
      cocodeParity c * golayQuarterWeight e.1 + cocodeParity f * golayQuarterWeight d.1 +
      golayHalfOverlap d.1 e.1 + s * cocodeParity c + t * cocodeParity f := by
  simp only [coordinatePolar, q1WordCoordinates, golayQuarterWeight_add_smul_one,
    cocodePairing_add_left, cocodePairing_smul_one, golayHalfOverlap_add_smul_one_left,
    golayHalfOverlap_add_smul_one_right]
  ring

end Sporadic.Monster.Construction.TrialitySpin
