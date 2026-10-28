module

public import Theory.GroupAction.SemilinearPointStabilizerExceptional.DegreeEight.Action
public import Theory.GroupAction.SemilinearPointStabilizerExceptional.DegreeEight.InvolutionCalculation
public import Theory.GroupAction.SemilinearPointStabilizerExceptional.DegreeEight.InvolutionCore
public import Theory.GroupAction.SemilinearPointStabilizerExceptional.DegreeEight.LinearModel

/-!
# Recognition of the degree-eight semilinear-stabilizer action

The coordinates give a faithful marked image on eight points, of order
56 or 168, with fixed-point-free involutions. The checked finite permutation
calculation shows that this image contains the marked linear subgroup, or all
its involutions commute. The latter branch contradicts the trivial two-core,
while the former gives the genuine matrix equivalence with GL₃(2).

The theorem `equiv_generalLinear` completes the degree-eight case under the
trivial two-core hypothesis, discharging the finite calculation in the
conditional API below. Source: GLS, Volume 4, Chapter 1, Theorem 3.2 and the
degree-eight endpoint of Lemma 3.9
(`refs/KGroup/GLS4/Chapter1.tex`, lines 305–468).
-/

public section
namespace MulAction.SemilinearPointStabilizer.DegreeEight

/-- Recognition from the two alternatives of the involution calculation. -/
theorem equiv_of_involution_alternatives (U : Subgroup Perm)
    (hcard : Nat.card U ∣ 168) (heven : 2 ∣ Nat.card U) (hcore : pCore 2 U = ⊥)
    (halternatives : linearSeed ≤ U ∨
      ∀ a b : U, a ^ 2 = 1 → b ^ 2 = 1 → Commute a b) :
    Nonempty (U ≃* Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) := by
  rcases halternatives with hseed | hcomm
  · exact equiv_of_seed_le U hcard hseed
  · exact (not_all_square_one_commute heven hcore hcomm).elim

/-- Application to the original actor, conditional only on the finite
permutation dichotomy. `equiv_generalLinear` discharges this input. -/
theorem equiv_of_involution_calculation
    {X F : Type*} [Group X] [Finite X] [Field F] [Finite F]
    [MulAction X F] [FaithfulSMul X F]
    (c : Coordinates X F) (htwo : IsMultiplyPretransitive X F 2)
    (hF : Nat.card F = 8) (hcore : pCore 2 X = ⊥)
    (hcalc : ∀ U : Subgroup Perm, cycle ∈ U → Nat.card U ∣ 168 →
      (∀ t ∈ U, t ^ 2 = 1 → t ≠ 1 → ∀ i : Fin 8, t i ≠ i) →
      linearSeed ≤ U ∨ (∀ a b : U, a ^ 2 = 1 → b ^ 2 = 1 → Commute a b)) :
    Nonempty (X ≃* Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) := by
  obtain ⟨f, hf, hc, hcard, heven, hfree⟩ := exists_marked_image c htwo hF
  let e : X ≃* f.range := MonoidHom.ofInjective hf
  have hcore' : pCore 2 f.range = ⊥ := by
    rw [← pCore_map_iso 2 e, hcore, Subgroup.map_bot]
  obtain ⟨e'⟩ := equiv_of_involution_alternatives f.range hcard heven hcore'
    (hcalc f.range hc hcard hfree)
  exact ⟨e.trans e'⟩

/-- Degree-eight recognition for the original faithful doubly transitive
actor with semilinear point stabilizer and trivial two-core. The isomorphism
comes from the actual marked permutation image and its matrix realization. -/
theorem equiv_generalLinear
    {X F : Type*} [Group X] [Finite X] [Field F] [Finite F]
    [MulAction X F] [FaithfulSMul X F]
    (c : Coordinates X F) (htwo : IsMultiplyPretransitive X F 2)
    (hF : Nat.card F = 8) (hcore : pCore 2 X = ⊥) :
    Nonempty (X ≃* Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) :=
  equiv_of_involution_calculation c htwo hF hcore involution_calculation

end MulAction.SemilinearPointStabilizer.DegreeEight
