module
public import Theory.SpecificGroups.G2.RootPresentationRecognition.BorelCollection

/-!
# Internal Bruhat collection for the G₂ Borel–Weyl equations

A word in the Borel and the two reflections lies in a Borel double cell
represented by an alternating word of length at most six. The five ascending
root conjugations, rank-one exchange for descending steps, and the length-six
braid give closure under left multiplication by every generator and its inverse.
This argument takes place in any group satisfying the equations. It assumes
neither a faithful model map nor a Bruhat decomposition.

For presentation faithfulness this cover is used to put the evaluation kernel
inside the Borel, whose coordinates are faithful. The unrestricted double-cell
cover alone is not used to claim the refined finite order bound.
Source: the split G₂ comparison in DGS, Groups and Graphs, Theorem D, p.224;
the Bruhat exchange argument of GLS III, §2.3, in the A–F ATLAS convention.
-/

@[expose] public noncomputable section
namespace Atlas.G2.RootPresentationRecognition.BorelWeylData
variable {F G : Type*} [Field F] [CharP F 2] [Group G]
  (d : BorelWeylData F G) (R : d.Relations)

/-- Alternating words beginning with the indicated reflection. -/
def alternating (short : Bool) : ℕ → G
  | 0 => 1
  | n+1 => d.reflection short * alternating (!short) n

omit [CharP F 2] in
@[simp] theorem alternating_zero (short : Bool) : d.alternating short 0 = 1 := rfl

include R
omit [CharP F 2] in
theorem alternating_conjugate_succ (short : Bool) (n : ℕ) (x : G) :
    (d.alternating short (n+1))⁻¹ * x * d.alternating short (n+1) =
      (d.alternating (!short) n)⁻¹ *
        (d.reflection short * x * (d.reflection short)⁻¹) * d.alternating (!short) n := by
  simp only [alternating, mul_inv_rev, reflection_inv d R, mul_assoc]

omit [CharP F 2] in
theorem alternating_longest : d.alternating false 6 = d.alternating true 6 := by
  apply eq_of_mul_inv_eq_one
  calc
    _ = (d.r * d.s)^6 := by
      simp only [alternating, reflection, Bool.not_false, Bool.not_true, Bool.false_eq_true,
        if_true, if_false, mul_inv_rev, r_inv d R, s_inv d R,
        pow_succ, pow_zero, mul_one, one_mul, mul_assoc]
    _ = 1 := R.braid

omit [CharP F 2] in
theorem alternating_longest_flip (short : Bool) :
    d.alternating (!short) 6 = d.alternating short 6 := by
  cases short
  · exact (alternating_longest d R).symm
  · exact alternating_longest d R

omit [CharP F 2] in
/-- The five possible ascending steps conjugate the simple root to a positive
root. No negative-root homomorphism or model evaluation is used. -/
theorem alternating_simple_positive (short : Bool) (n : ℕ) (hn : n ≤ 5) (a : F) :
    ∃ i : Fin 6, (d.alternating (!short) n)⁻¹ * d.x (simpleRoot short) a *
      d.alternating (!short) n = d.x i a := by
  cases short <;> interval_cases n
  all_goals
    simp only [Bool.not_false, Bool.not_true, simpleRoot, Bool.false_eq_true,
      if_true, if_false]
  · exact ⟨4, by simp⟩
  · refine ⟨1, ?_⟩
    simp only [alternating_conjugate_succ d R, reflection, if_true,
      R.sE, Bool.not_true, alternating_zero, inv_one, one_mul, mul_one]
  · refine ⟨0, ?_⟩
    simp only [alternating_conjugate_succ d R, reflection, Bool.false_eq_true,
      if_true, if_false, R.sE, R.rB, Bool.not_true, Bool.not_false,
      alternating_zero, inv_one, one_mul, mul_one]
  · refine ⟨0, ?_⟩
    simp only [alternating_conjugate_succ d R, reflection, Bool.false_eq_true,
      if_true, if_false, R.sE, R.rB, R.sA, Bool.not_true, Bool.not_false,
      alternating_zero, inv_one, one_mul, mul_one]
  · refine ⟨1, ?_⟩
    simp only [alternating_conjugate_succ d R, reflection, Bool.false_eq_true,
      if_true, if_false, R.sE, R.rB, R.sA, R.rA, Bool.not_true, Bool.not_false,
      alternating_zero, inv_one, one_mul, mul_one]
  · refine ⟨4, ?_⟩
    simp only [alternating_conjugate_succ d R, reflection, Bool.false_eq_true,
      if_true, if_false, R.sE, R.rB, R.sA, R.rA, R.sB, Bool.not_true, Bool.not_false,
      alternating_zero, inv_one, one_mul, mul_one]
  · exact ⟨5, by simp⟩
  · refine ⟨3, ?_⟩
    simp only [alternating_conjugate_succ d R, reflection, Bool.false_eq_true, if_false,
      R.rF, Bool.not_false, alternating_zero, inv_one, one_mul, mul_one]
  · refine ⟨2, ?_⟩
    simp only [alternating_conjugate_succ d R, reflection, Bool.false_eq_true,
      if_true, if_false, R.rF, R.sD, Bool.not_true, Bool.not_false,
      alternating_zero, inv_one, one_mul, mul_one]
  · refine ⟨2, ?_⟩
    simp only [alternating_conjugate_succ d R, reflection, Bool.false_eq_true,
      if_true, if_false, R.rF, R.sD, R.rC, Bool.not_true, Bool.not_false,
      alternating_zero, inv_one, one_mul, mul_one]
  · refine ⟨3, ?_⟩
    simp only [alternating_conjugate_succ d R, reflection, Bool.false_eq_true,
      if_true, if_false, R.rF, R.sD, R.rC, R.sC, Bool.not_true, Bool.not_false,
      alternating_zero, inv_one, one_mul, mul_one]
  · refine ⟨5, ?_⟩
    simp only [alternating_conjugate_succ d R, reflection, Bool.false_eq_true,
      if_true, if_false, R.rF, R.sD, R.rC, R.sC, R.rD, Bool.not_true, Bool.not_false,
      alternating_zero, inv_one, one_mul, mul_one]

omit [CharP F 2] in
theorem alternating_simple_mem (short : Bool) (n : ℕ) (hn : n ≤ 5) (a : F) :
    (d.alternating (!short) n)⁻¹ * d.x (simpleRoot short) a *
      d.alternating (!short) n ∈ d.borel := by
  obtain ⟨i,hi⟩ := alternating_simple_positive d R short n hn a
  rw [hi]
  exact root_mem_borel d i a

/-- A Borel double cell with an alternating Weyl word of length at most six. -/
def Covered (g : G) : Prop := ∃ (a b : G) (short : Bool) (n : ℕ),
  a ∈ d.borel ∧ b ∈ d.borel ∧ n ≤ 6 ∧ g = a * d.alternating short n * b

omit R [CharP F 2] in
theorem covered_one : d.Covered 1 := ⟨1,1,false,0,Subgroup.one_mem _,Subgroup.one_mem _,by omega,by simp⟩

omit R [CharP F 2] in
theorem covered_left (b : G) (hb : b ∈ d.borel) {g : G} (hg : d.Covered g) :
    d.Covered (b*g) := by
  obtain ⟨a,c,short,n,ha,hc,hn,rfl⟩ := hg
  exact ⟨b*a,c,short,n,Subgroup.mul_mem _ hb ha,hc,hn,by simp only [mul_assoc]⟩

omit R [CharP F 2] in
theorem covered_right (b : G) (hb : b ∈ d.borel) {g : G} (hg : d.Covered g) :
    d.Covered (g*b) := by
  obtain ⟨a,c,short,n,ha,hc,hn,rfl⟩ := hg
  exact ⟨a,c*b,short,n,ha,Subgroup.mul_mem _ hc hb,hn,by simp only [mul_assoc]⟩

omit [CharP F 2] in
theorem covered_ascent (short : Bool) (n : ℕ) (hn : n ≤ 5) (a : F) :
    d.Covered (d.reflection short * d.x (simpleRoot short) a * d.alternating (!short) n) := by
  refine ⟨1, (d.alternating (!short) n)⁻¹ * d.x (simpleRoot short) a *
    d.alternating (!short) n, short, n+1, Subgroup.one_mem _,
    alternating_simple_mem d R short n hn a, by omega, ?_⟩
  simp only [alternating]
  group

/-- Descending exchange keeps the coroot factor in the left Borel. -/
theorem covered_descent (short : Bool) (n : ℕ) (hn : n ≤ 5) (a : F) :
    d.Covered (d.reflection short * d.x (simpleRoot short) a * d.alternating short (n+1)) := by
  by_cases ha : a = 0
  · subst a
    refine ⟨1,1,!short,n,Subgroup.one_mem _,Subgroup.one_mem _,by omega,?_⟩
    simp only [PositiveRoots.x_zero, alternating, mul_one, one_mul]
    rw [← mul_assoc, reflection_sq d R, one_mul]
  · let u : Fˣ := Units.mk0 a ha
    let t : Fˣ × Fˣ := if short then (u⁻¹,u) else (1,u⁻¹)
    have he : d.reflection short * d.x (simpleRoot short) a * d.reflection short =
        d.x (simpleRoot short) (↑u⁻¹:F) * d.torus t * d.reflection short *
          d.x (simpleRoot short) (↑u⁻¹:F) := by
      cases short
      · exact long_exchange d R u
      · exact short_exchange d R u
    refine ⟨d.x (simpleRoot short) (↑u⁻¹:F) * d.torus t,
      (d.alternating (!short) n)⁻¹ * d.x (simpleRoot short) (↑u⁻¹:F) *
        d.alternating (!short) n, short,n+1,
      Subgroup.mul_mem _ (root_mem_borel d _ _) (torus_mem_borel d t),
      alternating_simple_mem d R short n hn _,by omega,?_⟩
    change _ * (d.reflection short * d.alternating (!short) n) =
      _ * (d.reflection short * d.alternating (!short) n) * _
    rw [← mul_assoc, he]
    group

/-- Every simple-root transition stays within the twelve Weyl cells. -/
theorem covered_transition (short start : Bool) (n : ℕ) (hn : n ≤ 6) (a : F) :
    d.Covered (d.reflection short * d.x (simpleRoot short) a * d.alternating start n) := by
  by_cases heq : start = short
  · subst start
    cases n with
    | zero => simpa only [alternating_zero] using covered_ascent d R short 0 (by omega) a
    | succ n => exact covered_descent d R short n (by omega) a
  · have hstart : start = !short := by cases start <;> cases short <;> simp_all
    subst start
    by_cases hlast : n = 6
    · subst n
      rw [alternating_longest_flip d R]
      exact covered_descent d R short 5 (by omega) a
    · exact covered_ascent d R short n (by omega) a

theorem covered_reflection (short : Bool) {g : G} (hg : d.Covered g) :
    d.Covered (d.reflection short * g) := by
  obtain ⟨a,b,start,n,ha,hb,hn,rfl⟩ := hg
  obtain ⟨c,t,hc,hct⟩ := reflection_borel d R short a ha
  have hh := covered_right d b hb
    (covered_left d c hc (covered_transition d R short start n hn t))
  have he : d.reflection short * (a * d.alternating start n * b) =
      c * (d.reflection short * d.x (simpleRoot short) t * d.alternating start n) * b := by
    calc
      _ = (d.reflection short * a) * d.alternating start n * b := by group
      _ = _ := by rw [hct]; group
  rw [he]
  exact hh

/-- The whole group generated by the literal Borel and both reflections. -/
def whole : Subgroup G := Subgroup.closure ((d.borel : Set G) ∪ {d.r,d.s})

/-- Internal Bruhat collection; this uses neither a model homomorphism nor
any assumed finiteness, uniqueness or presentation faithfulness. -/
theorem bruhat_collection {g : G} (hg : g ∈ d.whole) : d.Covered g := by
  induction hg using Subgroup.closure_induction_left with
  | one => exact covered_one d
  | mul_left x hx y _ ih =>
      rcases hx with hx | hx
      · exact covered_left d x hx ih
      · rcases hx with rfl | rfl
        · exact covered_reflection d R false ih
        · exact covered_reflection d R true ih
  | inv_mul_cancel x hx y _ ih =>
      rcases hx with hx | hx
      · exact covered_left d x⁻¹ (Subgroup.inv_mem _ hx) ih
      · rcases hx with rfl | rfl
        · rw [r_inv d R]
          exact covered_reflection d R false ih
        · rw [s_inv d R]
          exact covered_reflection d R true ih

end Atlas.G2.RootPresentationRecognition.BorelWeylData
