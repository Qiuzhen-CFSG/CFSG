module
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Endpoint.Actors.FixedBounds.CatalogueCoverage.Faithfulness

/-!
# Comparison of binary codes with the standard adjoint actors

Upper unitriangular multiplication and reversal of inverse transpose realize
`CoverageCode.mul` on the literal adjoint quotient. The code image contains
both kinds of standard generator and is closed under multiplication and
inversion, so it exhausts `standardActors`.

These are the multiplication and coverage premises of
`standardCatalogue_cover_of_extensions`. Elementary-subgroup enumeration and
its final catalogue assembly are separate from this comparison.

Source: Guralnick–Malle, Classification of 2F-modules II, Lemma 4.5 and
Proposition 4.8 step 3A; Aschbacher–Smith K.3.2, printed pp.454–455.
-/

public section
open Representation Representation.BinaryOffender Matrix
namespace CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Endpoint.FixedBounds
open CoverageCode
private theorem decode_encode : ∀ (b : Fin 6 → ZMod 2) (e : Bool),
    codeBits (encode b e) = b ∧ codeOuter (encode b e) = e := by
  intro b e
  have h : Function.LeftInverse
      (fun p : (Fin 6 → ZMod 2) × Bool => encode p.1 p.2)
      (fun c : Code => (codeBits c, codeOuter c)) := encode_decode
  have hi := h.rightInverse_of_card_le (by
    simp only [Fintype.card_prod, Fintype.card_fun, ZMod.card, Fintype.card_fin,
      Fintype.card_bool]
    decide) (b, e)
  exact ⟨congrArg Prod.fst hi, congrArg Prod.snd hi⟩

private theorem upperElement_mulBits (a b : Fin 6 → ZMod 2) :
    upperElement (mulBits a b) = upperElement a * upperElement b := by
  apply Subtype.ext
  change upperMatrix (mulBits a b) = upperMatrix a * upperMatrix b
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [upperMatrix, mulBits, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

private theorem upperElement_graphBits (b : Fin 6 → ZMod 2) :
    upperElement (graphBits b) = reverseElement *
      BinaryLinear.OuterCyclic.graphSL 4 (upperElement b) * reverseElement⁻¹ := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, graphSL_matrix, upperElement_inv,
    reverseElement_inv]
  change upperMatrix (graphBits b) = reverseMatrix * (upperInverse b).transpose * reverseMatrix
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [upperMatrix, graphBits, upperInverse, reverseMatrix, Matrix.mul_apply,
      Fin.sum_univ_succ, Matrix.transpose_apply]

private theorem mapped_conjugation {H K : Type*} [_root_.Group H] [_root_.Group K]
    (f : H →* K) (r g g' : H) (t : K) (h : t * f g * t⁻¹ = f g') :
    (f r * t) * f g * (f r * t)⁻¹ = f (r * g' * r⁻¹) := by
  calc
    _ = f r * (t * f g * t⁻¹) * (f r)⁻¹ := by group
    _ = _ := by rw [h, map_mul, map_mul, map_inv]

private theorem extension_mul {H : Type*} [_root_.Group H]
    (a b d t : H) (ht : t * t = 1) (hb : t * b = d * t) (e f : Bool) :
    (a * (if e then d else b)) * (if Bool.xor e f then t else 1) =
      (a * (if e then t else 1)) * (b * (if f then t else 1)) := by
  cases e <;> cases f <;> simp only [Bool.false_xor, Bool.true_xor,
    Bool.not_false, Bool.not_true, Bool.false_eq_true, if_false, if_true, mul_one]
  · exact mul_assoc a b t
  · rw [mul_assoc, ← hb, ← mul_assoc]
  · calc
      a * d = (a * d) * (t * t) := by rw [ht, mul_one]
      _ = a * (d * t) * t := by simp only [mul_assoc]
      _ = (a * t) * (b * t) := by rw [← hb]; simp only [mul_assoc]

private theorem reversingGraphActor_conj_upper (b : Fin 6 → ZMod 2) :
    reversingGraphActor * innerActor (upperElement b) * reversingGraphActor⁻¹ =
      innerActor (upperElement (graphBits b)) :=
  (mapped_conjugation innerActor reverseElement (upperElement b)
    (BinaryLinear.OuterCyclic.graphSL 4 (upperElement b)) graphActor (graphActor_conj _)).trans
      (congrArg innerActor (upperElement_graphBits b).symm)

private theorem reversingGraphActor_mul_upper (b : Fin 6 → ZMod 2) :
    reversingGraphActor * innerActor (upperElement b) =
      innerActor (upperElement (graphBits b)) * reversingGraphActor :=
  mul_inv_eq_iff_eq_mul.mp (reversingGraphActor_conj_upper b)

private theorem codeActor_encode (b : Fin 6 → ZMod 2) (e : Bool) :
    codeActor (encode b e) =
      innerActor (upperElement b) * if e then reversingGraphActor else 1 := by
  simp only [codeActor, (decode_encode b e).1, (decode_encode b e).2]

/-- The seven-bit multiplication is multiplication of the actual adjoint actors. -/
theorem codeActor_mul (a b : Code) :
    codeActor (CoverageCode.mul a b) = codeActor a * codeActor b := by
  let bits := if codeOuter a then graphBits (codeBits b) else codeBits b
  let outer := if Bool.xor (codeOuter a) (codeOuter b) then reversingGraphActor else 1
  have hb : innerActor (upperElement bits) =
      if codeOuter a then innerActor (upperElement (graphBits (codeBits b)))
      else innerActor (upperElement (codeBits b)) := by
    dsimp only [bits]
    split_ifs <;> rfl
  have hm := (congrArg innerActor (upperElement_mulBits (codeBits a) bits)).trans
    (map_mul innerActor (upperElement (codeBits a)) (upperElement bits))
  have hs : reversingGraphActor * reversingGraphActor = 1 := by
    simpa only [pow_two] using reversingGraphActor_sq
  exact (codeActor_encode (mulBits (codeBits a) bits)
      (Bool.xor (codeOuter a) (codeOuter b))).trans
    ((congrArg (fun g => g * outer)
      (hm.trans (congrArg (fun g => innerActor (upperElement (codeBits a)) * g) hb))).trans
        (extension_mul _ _ _ _ hs (reversingGraphActor_mul_upper (codeBits b))
          (codeOuter a) (codeOuter b)))

private theorem upperElement_zero : upperElement (fun _ => 0) = 1 := by
  apply Subtype.ext
  change upperMatrix (fun _ => 0) = 1
  decide +kernel

private theorem upperElement_entries (g : Group) (hg : IsUpperUnitriangular g) :
    upperElement ![g.val 0 1, g.val 0 2, g.val 0 3, g.val 1 2, g.val 1 3,
      g.val 2 3] = g := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [upperElement, upperMatrix, hg.1, hg.2]

/-- The codes exhaust the literal subgroup generated by upper inner actors and
reversing graph transpose on the adjoint quotient. -/
theorem codeActor_cover : ∀ x ∈ standardActors, ∃ c : Code, codeActor c = x := by
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with ⟨g, hg, rfl⟩ | rfl
    · refine ⟨encode ![g.val 0 1, g.val 0 2, g.val 0 3, g.val 1 2, g.val 1 3,
        g.val 2 3] false, ?_⟩
      exact (codeActor_encode _ false).trans
        ((mul_one _).trans (congrArg innerActor (upperElement_entries g hg)))
    · refine ⟨encode (fun _ => 0) true, ?_⟩
      exact (codeActor_encode _ true).trans
        ((congrArg (fun g => g * reversingGraphActor)
          ((congrArg innerActor upperElement_zero).trans (map_one innerActor))).trans
            (one_mul _))
  | one => exact ⟨0, codeActor_zero⟩
  | mul x y hx hy ihx ihy =>
    obtain ⟨a, rfl⟩ := ihx
    obtain ⟨b, rfl⟩ := ihy
    exact ⟨CoverageCode.mul a b, codeActor_mul a b⟩
  | inv x hx ih =>
    obtain ⟨a, rfl⟩ := ih
    refine ⟨CoverageCode.inv a, eq_inv_of_mul_eq_one_left ?_⟩
    rw [← codeActor_mul, CoverageCode.inv_mul, codeActor_zero]

end CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Endpoint.FixedBounds
