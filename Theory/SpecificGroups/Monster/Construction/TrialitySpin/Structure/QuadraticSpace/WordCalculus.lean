module

public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.Structure.QuadraticSpace.Coordinates
public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.Structure.NormalForms.Collection.Relations

/-!
# Multiplication and quadratic identities for actual triality words

The action of `q1Word d t c` on each loop coordinate is computed directly from
its three defining permutation factors, with axes two and three interchanged
when the cocode is odd. The Golay factor-set and polarization identities then
give an exact multiplication law: the prescribed twisted product representative
differs by an explicit power of `z1N`. Squaring and comparing the two product
orders give the quadratic and polar formulas. The product discrepancy therefore
belongs to `Q1CentralKernel`, already through its generator `z1N`.

These calculations do not use normal-form existence or uniqueness, or any
identification of the group quotient with the coordinate space.

Source: Aschbacher, *Sporadic Groups*, Exercise 4.6, printed p. 64
(PDF p. 38), and the proof of Lemma 27.2, printed pp. 144–145.
Products use Lean's left-composition convention. The Golay factor set and
cocode pairing are the attributed ATLAS ports imported through `Coordinates`.
-/

@[expose] public section

open Atlas.Fischer Atlas.Codes
noncomputable section
namespace Sporadic.Monster.Construction.TrialitySpin
set_option backward.isDefEq.respectTransparency false

private theorem bit_cases (t : ParkerBit) : t = 0 ∨ t = 1 := by revert t; decide

private theorem sandwich (d b : ParkerLoop) :
    parkerLoopMultiply (parkerLoopMultiply (loopInverse d) b) (loopInverse d) =
      parkerSign (golayHalfOverlap d.1 b.1 + golayQuarterWeight d.1) b := by
  simpa only [add_comm] using normalForm_sandwich d b

private def wordFirst (d : ParkerLoop) (t : ParkerBit) (c : Cocode) (x : ParkerLoop) : ParkerLoop :=
  (x.1, x.2 + t + golayQuarterWeight d.1 + golayHalfOverlap d.1 x.1 +
    cocodePairing x.1 c + cocodeParity c * golayQuarterWeight x.1)

private def wordSecond (d : ParkerLoop) (t : ParkerBit) (c : Cocode) (x : ParkerLoop) : ParkerLoop :=
  (d.1 + x.1, x.2 + d.2 + parkerGolayFactorSet d.1 x.1 + cocodePairing (d.1 + x.1) c +
    cocodeParity c * (t + golayQuarterWeight d.1 + golayQuarterWeight x.1))

private def wordThird (d : ParkerLoop) (t : ParkerBit) (c : Cocode) (x : ParkerLoop) : ParkerLoop :=
  (d.1 + x.1, x.2 + d.2 + t + parkerGolayFactorSet x.1 d.1 + cocodePairing (d.1 + x.1) c +
    cocodeParity c * (t + golayQuarterWeight d.1 + golayQuarterWeight x.1))

private def wordAction (d : ParkerLoop) (t : ParkerBit) (c : Cocode) (x : Triple) : Triple :=
  if cocodeParity c = 0 then
    (x.1.map (wordFirst d t c), x.2.1.map (wordSecond d t c), x.2.2.map (wordThird d t c))
  else
    (x.1.map (wordFirst d t c), x.2.2.map (wordSecond d t c), x.2.1.map (wordThird d t c))

private theorem cocode_even_iff (c : Cocode) :
    (parkerCocodeStandard c).val parkerOmega = parkerOmega ↔ cocodeParity c = 0 := by
  simp [parkerOmega, cocodePairing_one]

private theorem actual_action (d : ParkerLoop) (t : ParkerBit) (c : Cocode) (x : Triple) :
    (q1Word d t c).val.val x = wordAction d t c x := by
  rcases x with ⟨a,b,e⟩
  change psiAut1 (parkerCocodeStandard c).val (psi2 (0,t) (psi1 d (a,b,e))) = _
  rcases bit_cases (cocodeParity c) with hp | hp
  · have he := (cocode_even_iff c).mpr hp
    simp only [psi1_apply, psi2_apply, psiAut1, he, ↓reduceIte, wordAction, hp,
      diagonal, Equiv.prodCongr_apply, Prod.map_apply, Equiv.optionCongr_apply]
    apply Prod.ext
    · cases a with
      | none => rfl
      | some a =>
        simp only [leftZero_some, rightZero_some, sandwich, Option.map_some,
          parkerCocodeStandard_apply]
        apply congrArg some
        apply Prod.ext
        · change a.1 + 0 = a.1; simp
        · dsimp [parkerLoopMultiply, parkerMultiply, parkerSign, wordFirst]
          simp only [parkerGolayFactorSet_zero_right, add_zero, hp, zero_mul]
          ring
    · apply Prod.ext
      · cases b with
        | none => rfl
        | some b =>
          simp only [leftZero_some, rightZero_some, sandwich, Option.map_some,
            parkerCocodeStandard_apply]
          apply congrArg some
          apply Prod.ext
          · rfl
          · dsimp [parkerLoopMultiply, parkerMultiply, parkerSign, wordSecond]
            simp only [golayHalfOverlap_zero_left, golayQuarterWeight_zero,
              add_zero, hp, zero_mul]
            ring
      · cases e with
        | none => rfl
        | some e =>
          simp only [leftZero_some, rightZero_some, Option.map_some, parkerCocodeStandard_apply]
          apply congrArg some
          apply Prod.ext
          · change 0 + (e.1 + d.1) = d.1 + e.1; abel
          · dsimp [parkerLoopMultiply, parkerMultiply, wordThird]
            simp only [parkerGolayFactorSet_zero_left, zero_add, add_zero, hp, zero_mul]
            rw [add_comm e.1 d.1]
            ring
  · have he : (parkerCocodeStandard c).val parkerOmega ≠ parkerOmega := by
      intro hh
      have hz := (cocode_even_iff c).mp hh
      rw [hp] at hz
      exact one_ne_zero hz
    simp only [psi1_apply, psi2_apply, psiAut1, he, ↓reduceIte, wordAction, hp,
      show (1 : ParkerBit) ≠ 0 from one_ne_zero, Equiv.trans_apply, flip1,
      diagonal, Equiv.prodCongr_apply]
    apply Prod.ext
    · cases a with
      | none => rfl
      | some a =>
        simp only [leftZero_some, rightZero_some, sandwich, Option.map_some]
        apply congrArg some
        apply Prod.ext
        · change a.1 + 0 = a.1; simp
        · dsimp [parkerLoopMultiply, parkerMultiply, parkerSign, loopInverseEquiv, loopInverse, wordFirst]
          simp only [parkerGolayFactorSet_zero_right, add_zero, hp, one_mul]
          ring
    · apply Prod.ext
      · cases e with
        | none => rfl
        | some e =>
          simp only [leftZero_some, rightZero_some, Option.map_some]
          apply congrArg some
          apply Prod.ext
          · change 0 + (e.1 + d.1) = d.1 + e.1; abel
          · dsimp [parkerLoopMultiply, parkerMultiply, parkerSign, loopInverseEquiv, loopInverse, wordSecond]
            simp only [parkerGolayFactorSet_zero_left, zero_add, add_zero, hp, one_mul]
            rw [add_comm e.1 d.1, golayQuarterWeight_add, ← parkerGolayFactorSet_commutator]
            ring_nf
            simp
      · cases b with
        | none => rfl
        | some b =>
          simp only [leftZero_some, rightZero_some, sandwich, Option.map_some]
          apply congrArg some
          apply Prod.ext
          · rfl
          · dsimp [parkerLoopMultiply, parkerMultiply, parkerSign, loopInverseEquiv, loopInverse, wordThird]
            simp only [golayHalfOverlap_zero_left, golayQuarterWeight_zero,
              add_zero, hp, one_mul]
            rw [golayQuarterWeight_add, ← parkerGolayFactorSet_commutator]
            ring_nf
            simp


/-- The exact central sign in the product of two triality words. -/
def q1WordProductSign (d e : ParkerLoop) (t : ParkerBit) (f : Cocode) : ParkerBit :=
  d.2 + e.2 + parkerGolayFactorSet d.1 e.1 + cocodePairing d.1 f +
    cocodeParity f * (t + golayQuarterWeight d.1)

private theorem z1_pow_action (r : ParkerBit) (a b c : LoopZero) :
    (z1 ^ r.val) (a,b,c) = (a,b.map (parkerSign r), c.map (parkerSign r)) := by
  rcases bit_cases r with rfl | rfl
  · cases b <;> cases c <;> simp
  · simp only [show (1 : ParkerBit).val = 1 from rfl, pow_one, z1_apply]
    cases b <;> cases c <;> simp

private theorem action_product (d e : ParkerLoop) (t s : ParkerBit) (c f : Cocode) (x : Triple) :
    wordAction d t c (wordAction e s f x) =
      (z1 ^ (q1WordProductSign d e t f).val)
        (wordAction (d.1 + e.1, 0) (t + s + golayHalfOverlap d.1 e.1)
          (c + f + intersectionCocode d.1 e.1) x) := by
  rcases x with ⟨a,b,h⟩
  have hp : cocodeParity (c + f + intersectionCocode d.1 e.1) =
      cocodeParity c + cocodeParity f := by simp
  rcases bit_cases (cocodeParity c) with hc | hc <;>
    rcases bit_cases (cocodeParity f) with hf | hf <;>
    simp only [wordAction, hp, hc, hf, zero_add, add_zero,
      show (1 : ParkerBit) + 1 = 0 from rfl, ↓reduceIte,
      show (1 : ParkerBit) ≠ 0 from one_ne_zero, z1_pow_action, Option.map_map]
  all_goals
    apply Prod.ext
    · apply congrArg (fun F : ParkerLoop → ParkerLoop => Option.map F a)
      funext v
      apply Prod.ext
      · rfl
      · simp only [Function.comp_apply, wordFirst, golayQuarterWeight_add, golayHalfOverlap_add_left,
          cocodePairing_add_right, cocodePairing_intersection, hp, hc, hf,
          zero_mul, one_mul, zero_add, add_zero]
        ring_nf
        simp
    · apply Prod.ext
      all_goals
        apply congrArg (fun F : ParkerLoop → ParkerLoop => Option.map F _)
        funext v
        apply Prod.ext
        · dsimp [Function.comp_apply, wordSecond, wordThird, parkerSign]
          abel
        · dsimp only [Function.comp_apply, wordSecond, wordThird, parkerSign, q1WordProductSign]
          simp only [cocodePairing_add_left, cocodePairing_add_right]
          simp only [
            golayQuarterWeight_add,
            cocodePairing_intersection_self_left, cocodePairing_intersection_self_right,
            cocodePairing_intersection, parkerGolayFactorSet_add_left,
            parkerGolayFactorSet_add_right, hp, hc, hf,
            zero_mul, one_mul, zero_add, add_zero,
            ← parkerGolayFactorSet_commutator,
            parkerTripleIntersection_cycle v.1 d.1 e.1,
            parkerTripleIntersection_cycle e.1 v.1 d.1]
          ring_nf
          simp only [show (2 : ParkerBit) = 0 from rfl,
            show (3 : ParkerBit) = 1 from rfl, show (4 : ParkerBit) = 0 from rfl,
            show (5 : ParkerBit) = 1 from rfl, show (6 : ParkerBit) = 0 from rfl,
            mul_zero, mul_one, add_zero]


/-- Multiplication of the actual permutations, with the source's twisted
code and cocode corrections and an explicit central sign. -/
theorem q1Word_mul (d e : ParkerLoop) (t s : ParkerBit) (c f : Cocode) :
    (q1Word d t c).val * (q1Word e s f).val =
      z1N ^ (q1WordProductSign d e t f).val *
        (q1Word (d.1 + e.1, 0) (t + s + golayHalfOverlap d.1 e.1)
          (c + f + intersectionCocode d.1 e.1)).val := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_pow, q1WordProductSign,
    show z1N.val = z1 from rfl]
  apply Equiv.ext
  intro x
  simp only [Equiv.Perm.mul_apply, actual_action]
  exact action_product d e t s c f x

private theorem word_zero : (q1Word (0,0) 0 0).val = 1 := by
  apply Subtype.ext
  apply Equiv.ext
  rintro ⟨a,b,c⟩
  rw [actual_action]
  change wordAction (0,0) 0 0 (a,b,c) = (a,b,c)
  have h1 : wordFirst (0,0) 0 0 = id := by funext x; simp [wordFirst]
  have h2 : wordSecond (0,0) 0 0 = id := by funext x; simp [wordSecond]
  have h3 : wordThird (0,0) 0 0 = id := by funext x; simp [wordThird]
  simp [wordAction, h1, h2, h3]

private theorem cocode_double (c : Cocode) : c + c = 0 := by
  rw [← two_nsmul, ← Nat.cast_smul_eq_nsmul Bit]
  exact zero_smul Bit c

/-- The square is the central involution raised to the source quadratic value. -/
theorem q1Word_sq (d : ParkerLoop) (t : ParkerBit) (c : Cocode) :
    (q1Word d t c).val ^ 2 =
      z1N ^ (coordinateQuadratic (q1WordCoordinates d t c)).val := by
  rw [pow_two, q1Word_mul]
  simp only [parkerGolay_add_self, CharTwo.add_self_eq_zero, golayHalfOverlap_self,
    cocode_double, intersectionCocode_self, zero_add, word_zero, mul_one]
  congr 1
  congr 1
  simp only [q1WordProductSign, q1WordCoordinates_quadratic,
    CharTwo.add_self_eq_zero, parkerGolayFactorSet_square, zero_add]
  ring

private theorem z1_pow_add (r s : ParkerBit) :
    z1N ^ (r + s).val = z1N ^ r.val * z1N ^ s.val := by
  rw [ZMod.val_add, ← pow_eq_pow_mod _ z1N_sq, pow_add]

private theorem z1_pow_inv (r : ParkerBit) : (z1N ^ r.val)⁻¹ = z1N ^ r.val := by
  apply inv_eq_of_mul_eq_one_left
  rw [← z1_pow_add, CharTwo.add_self_eq_zero]
  rfl

private theorem productSign_polar (d e : ParkerLoop) (t s : ParkerBit) (c f : Cocode) :
    q1WordProductSign d e t f + q1WordProductSign e d s c =
      coordinatePolar (q1WordCoordinates d t c) (q1WordCoordinates e s f) := by
  simp only [q1WordProductSign, q1WordCoordinates_polar,
    ← parkerGolayFactorSet_commutator]
  ring_nf
  simp

/-- The explicit commutator `a * b * a⁻¹ * b⁻¹` is given by the source polar form. -/
theorem q1Word_commutator (d e : ParkerLoop) (t s : ParkerBit) (c f : Cocode) :
    (q1Word d t c).val * (q1Word e s f).val *
      (q1Word d t c).val⁻¹ * (q1Word e s f).val⁻¹ =
      z1N ^ (coordinatePolar (q1WordCoordinates d t c) (q1WordCoordinates e s f)).val := by
  have hr : (q1Word e s f).val * (q1Word d t c).val =
      z1N ^ (q1WordProductSign e d s c).val *
        (q1Word (d.1 + e.1, 0) (t + s + golayHalfOverlap d.1 e.1)
          (c + f + intersectionCocode d.1 e.1)).val := by
    rw [q1Word_mul]
    rw [add_comm e.1 d.1, add_comm s t, golayHalfOverlap_symmetric e.1 d.1,
      add_comm f c, intersectionCocode_comm e.1 d.1]
  calc
    _ = ((q1Word d t c).val * (q1Word e s f).val) *
        ((q1Word e s f).val * (q1Word d t c).val)⁻¹ := by
      rw [mul_inv_rev, mul_assoc]
    _ = z1N ^ (q1WordProductSign d e t f).val *
        (z1N ^ (q1WordProductSign e d s c).val)⁻¹ := by
      rw [hr, q1Word_mul]
      simp only [mul_inv_rev, mul_assoc, mul_inv_cancel_left]
    _ = z1N ^ (coordinatePolar (q1WordCoordinates d t c)
        (q1WordCoordinates e s f)).val := by
      rw [z1_pow_inv, ← z1_pow_add, productSign_polar]

/-- The prescribed product representative agrees modulo the actual subgroup
`⟨z1N,k1⟩`. In fact the discrepancy is already in `⟨z1N⟩`. -/
theorem q1Word_mul_mem_Q1CentralKernel (d e : ParkerLoop) (t s : ParkerBit) (c f : Cocode) :
    (q1Word d t c).val * (q1Word e s f).val *
      (q1Word (d.1 + e.1, 0) (t + s + golayHalfOverlap d.1 e.1)
        (c + f + intersectionCocode d.1 e.1)).val⁻¹ ∈ Q1CentralKernel := by
  rw [q1Word_mul, mul_inv_cancel_right]
  apply Subgroup.pow_mem
  exact Subgroup.subset_closure (by simp)

end Sporadic.Monster.Construction.TrialitySpin
