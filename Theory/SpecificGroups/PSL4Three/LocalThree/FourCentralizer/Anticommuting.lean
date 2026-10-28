module

public import Theory.SpecificGroups.PSL4Three.LocalThree.Model
public import Theory.SpecificGroups.PSL4Three.LocalThree.FourCentralizer.Restriction
import Mathlib.Tactic.NoncommRing

/-!
# Anticommuting projective involution lifts in SL₄(3)

A lift squares to I or -I. If either square is I, use that involution.
If both squares are -I, the sum and difference of the two matrices square
to I and anticommute in characteristic three. In all cases the original
common centralizer embeds into the centralizer of an involution and an
invertible anticommuting matrix. Anticommutation forces trace zero, and
the faithful plane restriction excludes nine from this latter order.

The sum/difference step treats the nonsplit scalar-square case over F₃
itself, without discarding a scalar commutator or assuming a model isomorphism.
Source application: Aschbacher–Smith, Theorem 0.1.2(4), printed p.4,
repeated as Theorem 0.1.1(4), printed p.482 of `refs/quasithin.pdf`.
-/

public noncomputable section
open Matrix
namespace Matrix.PSL4Three.LocalThree.FourCentralizer

private abbrev GL4 := GL (Fin 4) (ZMod 3)
private abbrev PairSL (a b : SL) := Subgroup.centralizer ({a, b} : Set SL)

private theorem trace_eq_zero_of_anticommute (a b : GL4)
    (hab : a.val * b.val = -(b.val * a.val)) : trace a.val = 0 := by
  have hconj : b.val * a.val * (b⁻¹).val = -a.val := by
    have he := congrArg (fun M : Mat => M * (b⁻¹).val) hab
    simp only [mul_assoc, Units.mul_inv, mul_one, neg_mul] at he
    simpa only [neg_neg, mul_assoc] using (congrArg Neg.neg he).symm
  have ht := congrArg trace hconj
  rw [Matrix.trace_units_conj, Matrix.trace_neg] at ht
  exact (by decide : ∀ x : ZMod 3, x = -x → x = 0) _ ht

private theorem bound_of_involution_pair (a b : SL) (A B : GL4)
    (hA : A ^ 2 = 1) (hAB : A.val * B.val = -(B.val * A.val))
    (hcomm : ∀ x : PairSL a b,
      Commute (SpecialLinearGroup.toGL x.val) A ∧ Commute (SpecialLinearGroup.toGL x.val) B) :
    ¬ 3 ^ 2 ∣ Nat.card (PairSL a b) := by
  let f : PairSL a b →* Subgroup.centralizer ({A, B} : Set GL4) :=
    { toFun := fun x => ⟨SpecialLinearGroup.toGL x.val, by
        intro z hz
        rcases hz with rfl | hz
        · exact (hcomm x).1.eq.symm
        · obtain rfl := Set.mem_singleton_iff.mp hz
          exact (hcomm x).2.eq.symm⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun x y => Subtype.ext (map_mul _ _ _) }
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    apply SpecialLinearGroup.toGL_injective
    exact congrArg Subtype.val h
  exact fun h => Anticommuting.centralizer_not_nine_dvd_of_square_one A B hA
    (trace_eq_zero_of_anticommute A B hAB) hAB
    (h.trans (Subgroup.card_dvd_of_injective f hf))

private theorem square_cases (a : SL) (ha : (project a) ^ 2 = 1) :
    (a : Mat) * (a : Mat) = 1 ∨ (a : Mat) * (a : Mat) = -1 := by
  obtain ⟨c, hc, he⟩ := square_scalar a ha
  rcases sq_eq_one_iff.mp hc with rfl | rfl
  · exact Or.inl (by simpa only [pow_two, one_smul] using he)
  · exact Or.inr (by simpa only [pow_two, neg_smul, one_smul] using he)

private theorem pair_commutes (a b : SL) (x : PairSL a b) :
    Commute ((x : SL) : Mat) (a : Mat) ∧ Commute ((x : SL) : Mat) (b : Mat) := by
  constructor
  · exact congrArg (fun y : SL => (y : Mat)) (x.property a (by simp)).symm
  · exact congrArg (fun y : SL => (y : Mat)) (x.property b (by simp)).symm

private def unitOfSquare (M : Mat) (hM : M * M = 1) : GL4 := ⟨M, M, hM, hM⟩

private theorem add_self_matrix (M : Mat) : M + M = -M := by
  apply Matrix.ext
  intro i j
  exact (by decide : ∀ x : ZMod 3, x + x = -x) (M i j)

private theorem sum_difference (a b : Mat)
    (ha : a * a = -1) (hb : b * b = -1) (hab : a * b = -(b * a)) :
    (a + b) * (a + b) = 1 ∧ (a - b) * (a - b) = 1 ∧
      (a + b) * (a - b) = -((a - b) * (a + b)) := by
  have hba : b * a = -(a * b) := by rw [hab, neg_neg]
  have hm : -(1 : Mat) + -1 = 1 := by
    calc
      _ = -((1 : Mat) + 1) := by abel
      _ = 1 := by rw [add_self_matrix, neg_neg]
  constructor
  · calc
      _ = a * a + (a * b + b * a) + b * b := by noncomm_ring
      _ = 1 := by rw [ha, hb, hba, add_neg_cancel, add_zero]; exact hm
  constructor
  · calc
      _ = a * a - (a * b + b * a) + b * b := by noncomm_ring
      _ = 1 := by rw [ha, hb, hba, add_neg_cancel, sub_zero]; exact hm
  · noncomm_ring [ha, hb, hba]

/-- The common centralizer of anticommuting projective involution lifts has
order indivisible by nine, in both scalar-square cases. -/
theorem anticommuting_lift_centralizer_not_nine_dvd (a b : SL)
    (ha : (project a) ^ 2 = 1) (hb : (project b) ^ 2 = 1)
    (hab : (a : Mat) * (b : Mat) = -((b : Mat) * (a : Mat))) :
    ¬ 3 ^ 2 ∣ Nat.card (Subgroup.centralizer ({a, b} : Set SL)) := by
  rcases square_cases a ha with ha1 | ham
  · apply bound_of_involution_pair a b (SpecialLinearGroup.toGL a) (SpecialLinearGroup.toGL b)
    · apply Units.ext
      change (a : Mat) ^ 2 = 1
      simpa only [pow_two] using ha1
    · exact hab
    · intro x
      obtain ⟨hxa, hxb⟩ := pair_commutes a b x
      exact ⟨Units.ext hxa.eq, Units.ext hxb.eq⟩
  rcases square_cases b hb with hb1 | hbm
  · apply bound_of_involution_pair a b (SpecialLinearGroup.toGL b) (SpecialLinearGroup.toGL a)
    · apply Units.ext
      change (b : Mat) ^ 2 = 1
      simpa only [pow_two] using hb1
    · change (b : Mat) * (a : Mat) = -((a : Mat) * (b : Mat))
      rw [hab, neg_neg]
    · intro x
      obtain ⟨hxa, hxb⟩ := pair_commutes a b x
      exact ⟨Units.ext hxb.eq, Units.ext hxa.eq⟩
  obtain ⟨hp, hm, hpm⟩ := sum_difference (a : Mat) (b : Mat) ham hbm hab
  apply bound_of_involution_pair a b (unitOfSquare _ hp) (unitOfSquare _ hm)
  · apply Units.ext
    change ((a : Mat) + (b : Mat)) ^ 2 = 1
    simpa only [pow_two] using hp
  · exact hpm
  · intro x
    obtain ⟨hxa, hxb⟩ := pair_commutes a b x
    exact ⟨Units.ext (hxa.add_right hxb).eq, Units.ext (hxa.sub_right hxb).eq⟩

end Matrix.PSL4Three.LocalThree.FourCentralizer
