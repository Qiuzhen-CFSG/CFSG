module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.RootReflections

/-!
# The perpendicular source roots in the octagon

The longest Weyl element exchanges the two defining unipotent intersections
of a simple root. For rotation order eight this proves that every lift of
s_i preserves U_i^(s_j s_i s_j). This is subgroup stability on the same
source quotient, with right conjugation throughout; no equation on the
order of a product of the actual reflection lifts is assumed.

Source: Fong--Seitz I (1973), (3G) and the opening action argument in the
proof of (6H)(a), printed p.51. LinearActions uses the stability to derive
centralization and field-unit divisibility.
-/

@[expose] public noncomputable section
open Subgroup
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
variable (Q : MarkedQuotient P) (split : SplitData Q.tits)

private theorem ssq (i : Fin 2) : Q.simple i*Q.simple i = 1 := by
  simpa only [pow_two] using (Q.tits.involutions _ (Q.simple_mem i)).2

private theorem longest_eight (hm : rotationOrder Q = 8)
    (i j : Fin 2) (hij : i ≠ j) :
    longest Q = Q.simple i*Q.simple j*Q.simple i*Q.simple j*
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

private theorem longest_comm (hm : rotationOrder Q = 8)
    (i j : Fin 2) (hij : i ≠ j) :
    Q.simple i * longest Q = longest Q * Q.simple i := by
  conv_lhs => rw [longest_eight Q hm i j hij]
  conv_rhs => rw [longest_eight Q hm j i hij.symm]
  simp only [mul_assoc, ← mul_assoc (Q.simple i) (Q.simple i), ssq,
    one_mul, mul_one]

private theorem rootAt_stabilizer (hm : rotationOrder Q = 8)
    (i j : Fin 2) (hij : i ≠ j) :
    rootAt Q split i (longest Q*Q.simple i) = simpleRoot Q split i := by
  have he : (longest Q*Q.simple i)*(longest Q*Q.simple i) = 1 := by
    rw [mul_assoc, ← mul_assoc (Q.simple i), longest_comm Q hm i j hij,
      ← mul_assoc, ← mul_assoc, longest_mul_self, one_mul, ssq]
  change rightConjugate (split.U ⊓ unipotentConjugate split (longest Q*Q.simple i))
    (representative (longest Q*Q.simple i) : X ⧸ Q.D) = _
  rw [rightConjugate_inf, ← unipotentConjugate_eq split _ _ (representative_spec _),
    unipotentConjugate_right split _ _ _ (representative_spec _), he,
    unipotentConjugate_one, inf_comm]
  rfl

/-- The perpendicular root in the octagon is fixed as a subgroup by the
original simple reflection, using its actual Weyl class. -/
theorem perpendicular_root_stable (hm : rotationOrder Q = 8)
    (i j : Fin 2) (hij : i ≠ j) (n : Q.tits.N)
    (hn : QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N) n = Q.simple i) :
    rightConjugate (rootAt Q split i (Q.simple j*Q.simple i*Q.simple j)) (n : X ⧸ Q.D) =
      rootAt Q split i (Q.simple j*Q.simple i*Q.simple j) := by
  rw [rootAt_right Q split i _ _ n hn]
  have he : (Q.simple j*Q.simple i*Q.simple j)*Q.simple i =
      (longest Q*Q.simple i)*(Q.simple j*Q.simple i*Q.simple j) := by
    rw [longest_eight Q hm j i hij.symm]
    simp only [mul_assoc, ← mul_assoc (Q.simple j) (Q.simple j),
      ← mul_assoc (Q.simple i) (Q.simple i), ssq, one_mul, mul_one]
  rw [he, ← rootAt_right Q split i _ _ (representative _) (representative_spec _),
    rootAt_stabilizer Q split hm i j hij]
  rfl

theorem perpendicular_root_normalizes (hm : rotationOrder Q = 8)
    (i j : Fin 2) (hij : i ≠ j) (n : Q.tits.N)
    (hn : QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N) n = Q.simple i) :
    (n : X ⧸ Q.D) ∈ normalizer
      (rootAt Q split i (Q.simple j*Q.simple i*Q.simple j) : Set (X ⧸ Q.D)) := by
  rw [mem_normalizer_iff]
  intro x
  change x ∈ rootAt Q split i _ ↔ x ∈ rightConjugate (rootAt Q split i _) (n : X ⧸ Q.D)
  rw [perpendicular_root_stable Q split hm i j hij n hn]

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
