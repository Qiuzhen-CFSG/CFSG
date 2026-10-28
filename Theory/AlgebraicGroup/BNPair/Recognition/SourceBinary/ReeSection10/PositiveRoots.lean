module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10.Input
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.FourRootIntervals
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.OctagonRoots

/-!
# The eight positive source roots in the native Ree indexing

The source linear endpoint is 0 and the Suzuki endpoint is 1. Carter's
alternating order is the reverse of the native angular order. Octagon
root stability and the proved longest-word stabilizer reduce its factors
to the short right-conjugation words used in Fong--Seitz II, Section 10.
Every factor lies in the same split U. The root equivalences use words in
the supplied actual N-reflections and retain their representative formulas.

These are geometric placements, before any choice of compatible field labels
or verification of mixed coefficients. No relation on the eighth power of
the actual lifts is inferred from their Weyl classes.

Source: Fong--Seitz I (1973), (3G); II (1974), Section 10, pp.221--224;
the native indexing is ReeF4.CentralCovers.TwoPrimary.sourceIndex.
-/

@[expose] public noncomputable section
open Subgroup
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open ReeF4.RootPresentationRecognition
namespace Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)

/-- Short right-conjugation words, in the native positive-root indexing. -/
def positiveWord {M : Type*} [Monoid M] (s t : M) : PositiveTables.Root → M
  | .inl i => ![1,t,t*s,t*s*t] i
  | .inr i => ![1,s*t*s,s,s*t] i

def positiveKind : PositiveTables.Root → Fin 2
  | .inl _ => 0
  | .inr _ => 1

def positiveRoot (i : PositiveTables.Root) : Subgroup (X ⧸ Q.D) :=
  rootAt Q split (positiveKind i) (positiveWord (Q.simple 0) (Q.simple 1) i)

/-- Carter order starts with the linear simple root in this orientation. -/
def positiveIndex : Fin 8 ≃ PositiveTables.Root :=
  (Function.Involutive.toPerm Fin.rev Fin.rev_involutive).trans
    ReeF4.CentralCovers.TwoPrimary.rootIndexEquiv.symm

private theorem simple_square (i : Fin 2) : Q.simple i * Q.simple i = 1 := by
  simpa only [pow_two] using (Q.tits.involutions _ (Q.simple_mem i)).2

private theorem root_four (hm : rotationOrder Q = 8) (i j : Fin 2) (hij : i ≠ j) :
    rootAt Q split i (Q.simple j*Q.simple i*Q.simple j*Q.simple i) =
      rootAt Q split i (Q.simple j*Q.simple i*Q.simple j) := by
  rw [← rootAt_right Q split i _ _ (representative _) (representative_spec _)]
  exact perpendicular_root_stable Q split hm i j hij _ (representative_spec _)

private theorem root_five (hm : rotationOrder Q = 8) (i j : Fin 2) (hij : i ≠ j) :
    rootAt Q split j (Q.simple i*Q.simple j*Q.simple i*Q.simple j*Q.simple i) =
      rootAt Q split j (Q.simple i*Q.simple j) := by
  have hl : longest Q = Q.simple i*Q.simple j*Q.simple i*Q.simple j*
      Q.simple i*Q.simple j*Q.simple i*Q.simple j := by
    have h0 := alternatingWord_longest Q false
    have h1 := alternatingWord_longest Q true
    rw [hm] at h0 h1
    have hi : i = 0 ∨ i = 1 := by omega
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
    · exact (hij rfl).elim
    · simpa only [alternatingWord, Bool.false_eq_true, ↓reduceIte,
        Bool.not_false, Bool.not_true, mul_one, mul_assoc] using h0.symm
    · simpa only [alternatingWord, Bool.false_eq_true, ↓reduceIte,
        Bool.not_false, Bool.not_true, mul_one, mul_assoc] using h1.symm
    · exact (hij rfl).elim
  have he : Q.simple i*Q.simple j*Q.simple i*Q.simple j*Q.simple i =
      (longest Q*Q.simple j)*(Q.simple i*Q.simple j) := by
    rw [hl]
    simp only [mul_assoc, ← mul_assoc (Q.simple i) (Q.simple i),
      simple_square, one_mul, mul_one]
  rw [he, rootAt_longest_simple_mul Q split hm j i hij.symm]

/-- The eight charts use exactly the actual ordered factors of the source U. -/
theorem positiveRoot_ordered (hm : rotationOrder Q = 8) :
    orderedRoots Q split false 8 = List.ofFn (fun j => positiveRoot Q split (positiveIndex j)) := by
  have hr (i : Fin 2) (v w : Weyl Q) :
      rightConjugate (rootAt Q split i v) (representative w : X ⧸ Q.D) =
        rootAt Q split i (v*w) := rootAt_right Q split i v w _ (representative_spec _)
  have hs (i : Fin 2) (w : Weyl Q) :
      rightConjugate (simpleRoot Q split i) (representative w : X ⧸ Q.D) =
        rootAt Q split i w := rfl
  simp only [orderedRoots, List.map_cons, List.map_nil, Bool.false_eq_true, ↓reduceIte,
    Bool.not_false, Bool.not_true, hs, hr,
    root_four Q split hm 0 1 (by decide), root_five Q split hm 0 1 (by decide)]
  simp only [mul_assoc, simple_square, mul_one, rootAt_one]
  simp [List.ofFn_succ, positiveIndex, positiveRoot, positiveKind, positiveWord,
    ReeF4.CentralCovers.TwoPrimary.rootIndexEquiv,
    ReeF4.CentralCovers.TwoPrimary.sourceIndex, mul_assoc]

theorem positiveRoot_le_unipotent (hm : rotationOrder Q = 8) (i : PositiveTables.Root) :
    positiveRoot Q split i ≤ split.U := by
  have hmem : positiveRoot Q split i ∈ orderedRoots Q split false (rotationOrder Q) := by
    rw [hm, positiveRoot_ordered Q split hm]
    exact List.mem_ofFn.mpr ⟨positiveIndex.symm i, by rw [Equiv.apply_symm_apply]⟩
  have h := orderedRoots_le Q split false (rotationOrder Q) le_rfl _ hmem
  simpa only [alternatingWord_longest, longest_inv, rootIntersection_longest] using h

variable {n m : ℕ} (c : ReeSixHData Q split n m)

/-- These are words in the given actual reflections, not choices of Weyl classes. -/
def positiveLift (i : PositiveTables.Root) : Q.tits.N :=
  positiveWord (c.reflections 0).val (c.reflections 1).val i

theorem positiveLift_class (i : PositiveTables.Root) :
    QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N)
      (positiveLift Q split c i) = positiveWord (Q.simple 0) (Q.simple 1) i := by
  cases i with
  | inl j => fin_cases j <;> simp [positiveLift, positiveWord, map_mul, (c.reflections _).class_eq]
  | inr j => fin_cases j <;> simp [positiveLift, positiveWord, map_mul, (c.reflections _).class_eq]

/-- Whole-root transport preserves the prescribed literal N-word. -/
def positiveRootEquiv (i : PositiveTables.Root) :
    simpleRoot Q split (positiveKind i) ≃* positiveRoot Q split i :=
  (RootAction.conjugateEquiv (simpleRoot Q split (positiveKind i))
    (positiveLift Q split c i : X ⧸ Q.D)).symm.trans
    (MulEquiv.subgroupCongr (rootAt_eq Q split _ _ _ (positiveLift_class Q split c i)).symm)

@[simp] theorem positiveRootEquiv_apply (i : PositiveTables.Root)
    (x : simpleRoot Q split (positiveKind i)) :
    (positiveRootEquiv Q split c i x : X ⧸ Q.D) =
      (positiveLift Q split c i : X ⧸ Q.D)⁻¹ * x * positiveLift Q split c i := rfl

end Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10
