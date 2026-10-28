module

public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.OddFourClosure.DefiningPrime.Roots
public import Mathlib.GroupTheory.OrderOfElement

/-!
# Collecting the positive unitary roots

The four additive root groups have a unique ordered product expression.
Their six relations collect a product of two expressions. Consequently the
same relations in a central cover give a section over the literal positive
subgroup. Neither the existence of those lifts nor the prime-to-q index is
assumed to follow from these matrix calculations.

Source: GLS3 §6.1, the defining-characteristic multiplier calculation for
SU₄, used in Aschbacher--Smith I.1.4(3), printed p.408.
-/

@[expose] public noncomputable section
open Matrix BenderSuzuki.MatrixGroups
namespace Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.OddFourClosure.DefiningPrime
variable {F : Type*} [Field F] {J : HermitianForm 4 F}
variable {E : Type*} [Group E] {f : E →* HyperbolicSU J}

namespace PositiveRootLifts
variable (L : PositiveRootLifts J f)

/-- The ordered product short, highest, middle, long. -/
def word (a : F) (s : traceZero J) (b : F) (t : traceZero J) : E :=
  L.short (.ofAdd a) * L.high (.ofAdd s) * L.middle (.ofAdd b) * L.long (.ofAdd t)

@[simp] theorem word_zero : L.word 0 0 0 0 = 1 := by simp [word]

private theorem add_left {A : Type*} [AddGroup A]
    (x : Multiplicative A →* E) (s t : A) (z : E) :
    x (.ofAdd s) * (x (.ofAdd t) * z) = x (.ofAdd (s+t)) * z := by
  rw [← mul_assoc, ← map_mul]
  rfl

/-- The unitary collection law, with its skew-trace and norm terms. -/
theorem word_mul (a : F) (s : traceZero J) (b : F) (t : traceZero J)
    (c : F) (l : traceZero J) (d : F) (v : traceZero J) :
    L.word a s b t * L.word c l d v =
      L.word (a+c) (s + skew J c b + normMul J c t + l)
        (b + (-c * (t : F)) + d) (t+v) := by
  simp only [word, mul_assoc]
  rw [← mul_assoc (L.long (.ofAdd t)) (L.short (.ofAdd c)), L.crossing_long_short]
  simp only [mul_assoc]
  rw [← mul_assoc (L.middle (.ofAdd b)) (L.short (.ofAdd c)), L.crossing_middle_short]
  simp only [mul_assoc]
  rw [(L.commute_short_high c s).symm.left_comm]
  rw [(L.commute_high_long l t).symm.left_comm,
    (L.commute_middle_long d t).symm.left_comm]
  rw [(L.commute_high_middle (normMul J c t) b).symm.left_comm]
  rw [(L.commute_high_middle l (-c * (t : F))).symm.left_comm,
    (L.commute_high_middle l b).symm.left_comm]
  rw [add_left, add_left, add_left, add_left, add_left, add_left, ← map_mul]
  rfl

/-- Projection of every collected word is the literal matrix word. -/
theorem project_word (a : F) (s : traceZero J) (b : F) (t : traceZero J) :
    f (L.word a s b t) = (matrixRootLifts J).word a s b t := by
  simp only [word, map_mul, ← MonoidHom.comp_apply,
    L.project_short, L.project_high, L.project_middle, L.project_long]
  rfl

end PositiveRootLifts

variable (J)

/-- Entries of the ordered root product. -/
theorem word_matrix (a : F) (s : traceZero J) (b : F) (t : traceZero J) :
    ((matrixRootLifts J).word a s b t).val.val =
      !![1,a,(s : F)-a*J.conj b,b+a*(t : F);
         0,1,-J.conj b,(t : F); 0,0,1,0; 0,0,-J.conj a,1] := by
  change shortMatrix J a * highMatrix J s * middleMatrix J b * longMatrix J t = _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [shortMatrix, highMatrix, middleMatrix, longMatrix,
      Matrix.mul_apply, Fin.sum_univ_succ]
  all_goals ring

/-- Six field dimensions, with no identifications between coordinate tuples. -/
theorem word_injective : Function.Injective (fun p : F × traceZero J × F × traceZero J =>
    (matrixRootLifts J).word p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  rintro ⟨a,s,b,t⟩ ⟨c,l,d,v⟩ h
  have hm := congrArg (fun g : HyperbolicSU J => g.val.val) h
  simp only [word_matrix] at hm
  have ha : a = c := congrArg (fun M => M 0 1) hm
  have ht : t = v := Subtype.ext (congrArg (fun M => M 1 3) hm)
  subst c; subst v
  have hb : b = d := add_right_cancel (congrArg (fun M => M 0 3) hm)
  subst d
  have hs : s = l := Subtype.ext (sub_left_inj.mp (congrArg (fun M => M 0 2) hm))
  subst l
  rfl

private def wordSubmonoid : Submonoid (HyperbolicSU J) where
  carrier := Set.range (fun p : F × traceZero J × F × traceZero J =>
    (matrixRootLifts J).word p.1 p.2.1 p.2.2.1 p.2.2.2)
  one_mem' := ⟨(0,0,0,0), (matrixRootLifts J).word_zero⟩
  mul_mem' := by
    rintro x y ⟨⟨a,s,b,t⟩,rfl⟩ ⟨⟨c,l,d,v⟩,rfl⟩
    exact ⟨(a+c,s + skew J c b + normMul J c t + l,b + (-c*(t:F)) + d,t+v),
      ((matrixRootLifts J).word_mul a s b t c l d v).symm⟩

private def wordSubgroup [Finite F] : Subgroup (HyperbolicSU J) where
  toSubmonoid := wordSubmonoid J
  inv_mem' := by
    intro a ha
    change a⁻¹ ∈ wordSubmonoid J
    rw [← one_mul a⁻¹, ← pow_one a, ← pow_orderOf_eq_one a, ← pow_sub a (orderOf_pos a)]
    exact (wordSubmonoid J).pow_mem ha _

private theorem positive_eq_wordSubgroup [Finite F] : positive J = wordSubgroup J := by
  apply le_antisymm
  · refine sup_le (sup_le (sup_le ?_ ?_) ?_) ?_
    · rintro x ⟨a,rfl⟩
      exact ⟨(a.toAdd,0,0,0), by simp [PositiveRootLifts.word, matrixRootLifts]⟩
    · rintro x ⟨s,rfl⟩
      exact ⟨(0,s.toAdd,0,0), by simp [PositiveRootLifts.word, matrixRootLifts]⟩
    · rintro x ⟨b,rfl⟩
      exact ⟨(0,0,b.toAdd,0), by simp [PositiveRootLifts.word, matrixRootLifts]⟩
    · rintro x ⟨t,rfl⟩
      exact ⟨(0,0,0,t.toAdd), by simp [PositiveRootLifts.word, matrixRootLifts]⟩
  · rintro x ⟨⟨a,s,b,t⟩,rfl⟩
    apply Subgroup.mul_mem
    · apply Subgroup.mul_mem
      · apply Subgroup.mul_mem
        · exact (show (shortRoot J).range ≤ positive J from
            le_sup_left.trans (le_sup_left.trans le_sup_left)) ⟨.ofAdd a,rfl⟩
        · exact (show (highRoot J).range ≤ positive J from
            le_sup_right.trans (le_sup_left.trans le_sup_left)) ⟨.ofAdd s,rfl⟩
      · exact (show (middleRoot J).range ≤ positive J from
          le_sup_right.trans le_sup_left) ⟨.ofAdd b,rfl⟩
    · exact (show (longRoot J).range ≤ positive J from le_sup_right) ⟨.ofAdd t,rfl⟩

/-- Every element of the root-generated subgroup has the ordered expression. -/
theorem mem_positive_iff [Finite F] (g : HyperbolicSU J) :
    g ∈ positive J ↔ ∃ a s b t, (matrixRootLifts J).word a s b t = g := by
  rw [positive_eq_wordSubgroup]
  change (∃ p : F × traceZero J × F × traceZero J,
    (matrixRootLifts J).word p.1 p.2.1 p.2.2.1 p.2.2.2 = g) ↔ _
  constructor
  · rintro ⟨⟨a,s,b,t⟩,h⟩; exact ⟨a,s,b,t,h⟩
  · rintro ⟨a,s,b,t,h⟩; exact ⟨(a,s,b,t),h⟩

/-- Unique ordered coordinates on the actual positive subgroup. -/
def coordinateEquiv [Finite F] : (F × traceZero J × F × traceZero J) ≃ positive J :=
  Equiv.ofBijective (fun p =>
    ⟨(matrixRootLifts J).word p.1 p.2.1 p.2.2.1 p.2.2.2,
      (mem_positive_iff J _).mpr ⟨p.1,p.2.1,p.2.2.1,p.2.2.2,rfl⟩⟩)
    ⟨fun _ _ h => word_injective J (congrArg Subtype.val h), by
      rintro ⟨g,hg⟩
      obtain ⟨a,s,b,t,h⟩ := (mem_positive_iff J g).mp hg
      exact ⟨(a,s,b,t), Subtype.ext h⟩⟩

/-- The positive subgroup has the expected four parameter factors. -/
theorem card_positive [Finite F] : Nat.card (positive J) =
    Nat.card F ^ 2 * Nat.card (traceZero J) ^ 2 := by
  rw [← Nat.card_congr (coordinateEquiv J), Nat.card_prod, Nat.card_prod, Nat.card_prod]
  ring

/-- Multiplication by a nonzero trace-zero scalar identifies the fixed and
trace-zero additive parameter sets. -/
theorem card_traceZero [Finite F] {q : ℕ} (hp : q.Prime)
    (hcard : Nat.card F = q^2) (hconj : ∀ x, J.conj x = x^q) :
    Nat.card (traceZero J) = q := by
  let : Fact q.Prime := ⟨hp⟩
  let := Fintype.ofFinite F
  let : CharP F q := charP_of_card_eq_prime_pow (by
    simpa only [Nat.card_eq_fintype_card] using hcard)
  obtain ⟨α,hα0,hα⟩ :=
    Theory.SpecificGroups.ClassicalUnitary.OddFourRanks.Defining.exists_trace_zero J hcard hconj
  let e : {x : F // J.conj x = x} ≃ traceZero J :=
    { toFun := fun x => ⟨α*x, by
        change J.conj _ = -_
        rw [map_mul, hα, x.property, neg_mul]⟩
      invFun := fun t => ⟨(t:F)/α, by
        rw [map_div₀, conj_traceZero, hα, neg_div_neg_eq]⟩
      left_inv := fun x => Subtype.ext (by
        change α * (x:F) / α = _
        exact mul_div_cancel_left₀ (x:F) hα0)
      right_inv := fun t => Subtype.ext (by
        change α * ((t:F)/α) = _
        exact mul_div_cancel₀ (t:F) hα0) }
  exact (Nat.card_congr e).symm.trans (J.card_fixed_of_prime_frobenius hconj)

/-- The concrete positive subgroup has order q⁶. This alone does not claim
that its index is prime to q. -/
theorem card_positive_prime [Finite F] {q : ℕ} (hp : q.Prime)
    (hcard : Nat.card F = q^2) (hconj : ∀ x, J.conj x = x^q) :
    Nat.card (positive J) = q^6 := by
  rw [card_positive, hcard, card_traceZero J hp hcard hconj]
  ring

namespace PositiveRootLifts
variable (L : PositiveRootLifts J f) [Finite F]

include L in
/-- The complete lifted relations give a homomorphic section over the
literal positive subgroup, with no global-presentation assertion. -/
theorem exists_positive_section :
    ∃ s : positive J →* E, f.comp s = (positive J).subtype := by
  let e := coordinateEquiv J
  let j : positive J → E := fun g =>
    let p := e.symm g
    L.word p.1 p.2.1 p.2.2.1 p.2.2.2
  have hj (p : F × traceZero J × F × traceZero J) :
      j (e p) = L.word p.1 p.2.1 p.2.2.1 p.2.2.2 := by
    simp [j]
  have he0 : e (0,0,0,0) = 1 := Subtype.ext (matrixRootLifts J).word_zero
  have hemul (a : F) (s : traceZero J) (b : F) (t : traceZero J)
      (c : F) (l : traceZero J) (d : F) (v : traceZero J) :
      e (a,s,b,t) * e (c,l,d,v) =
        e (a+c,s + skew J c b + normMul J c t + l,b + (-c*(t:F)) + d,t+v) :=
    Subtype.ext ((matrixRootLifts J).word_mul a s b t c l d v)
  have hjone : j 1 = 1 := by rw [← he0, hj]; exact L.word_zero
  have hjmul (x y : positive J) : j (x*y) = j x * j y := by
    obtain ⟨⟨a,s,b,t⟩,rfl⟩ := e.surjective x
    obtain ⟨⟨c,l,d,v⟩,rfl⟩ := e.surjective y
    rw [hemul, hj, hj, hj, L.word_mul]
  refine ⟨{toFun := j, map_one' := hjone, map_mul' := hjmul}, ?_⟩
  apply MonoidHom.ext
  intro g
  obtain ⟨⟨a,s,b,t⟩,rfl⟩ := e.surjective g
  change f (j (e (a,s,b,t))) = _
  rw [hj, L.project_word]
  rfl

end PositiveRootLifts
end Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.OddFourClosure.DefiningPrime
