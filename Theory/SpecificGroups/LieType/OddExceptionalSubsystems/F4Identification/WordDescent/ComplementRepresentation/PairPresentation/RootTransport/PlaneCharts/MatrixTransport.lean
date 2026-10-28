module

public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.WordDescent.ComplementRepresentation.PairPresentation.RootTransport
public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Intertwining.Transport.RouteComparison

/-!
# Signed F4 root transport over arbitrary fields

Two signed-simple routes with the same root endpoint have integral divided
powers differing by powers of one sign. The positive comparison is the existing
rational-root-space and primitive-coordinate argument in `RouteComparison`.
Appending the source reflection converts a negative source to a positive source;
its minus sign is retained before specializing the cubic root curves.

Thus arbitrary Weyl transport of the canonical root curve has the literal
matrix value of any route to the transported root, with parameter `ε * t`.
All factorial cancellation occurs over the integers. The result includes F3
and uses no completion-level coherence or group presentation.

Source: the matrix root-transport step of GLS3 §2.9.3,
`refs/KGroup/GLS3/chapter2.tex`, lines 1439–1462, and the integral Geck
comparison in `ReeF4/ExceptionalEndomorphism/WordRelations/Intertwining/Transport/RouteComparison`.
-/

@[expose] public section
noncomputable section
namespace TwistedE6.FoldedSubsystem.F4Identification.ComplementRepresentation.PlaneCharts
open Theory.AlgebraicGroup.StandardRootSystem RootPairing.IntegralGeckConstruction
open RootPairing.SimpleGeckGroup
open scoped Classical
attribute [local instance] Classical.decEq
local instance planeChartsMatrixTransportRootFintype : Fintype typeF4Roots := Fintype.ofFinite _
local notation "𝓟" => typeF4RootPairing

private theorem reflectionWord_append (w z : List typeF4RootPairing_base.support) (r : typeF4Roots) :
    reflectionWord (P := 𝓟) (w ++ z) r = reflectionWord w (reflectionWord z r) := by
  induction w with
  | nil => rfl
  | cons i w ih => simp only [List.cons_append, reflectionWord, ih]

private theorem appended_dividedPower (w : List typeF4RootPairing_base.support) (i : typeF4RootPairing_base.support) (n : ℕ) :
    transportedMatrix (P := 𝓟) (w ++ [i]) (eDividedPower i n) =
      (-1 : ℤ) ^ n • transportedMatrix w (fDividedPower i n) := by
  apply ReeF4.WordRelations.RouteComparison.dividedPower_eq_sign_smul
    (transportedMatrix (w ++ [i]) (eMatrix i)) (transportedMatrix w (fMatrix i))
  · rw [← transportedMatrix_pow, eMatrix_pow_eq_factorial_smul, transportedMatrix_smul]
  · rw [← transportedMatrix_pow, fMatrix_pow_eq_factorial_smul, transportedMatrix_smul]
  · simpa only [neg_one_smul] using
      ReeF4.WordRelations.RouteComparison.transportedMatrix_append_simple_eMatrix w i

/-- The divided power of the literal signed simple generator. -/
def signedDividedPower (s : Bool) (i : Fin 4) (n : ℕ) :=
  if s then eDividedPower (P := 𝓟) (sourceIndex i) n
  else fDividedPower (P := 𝓟) (sourceIndex i) n

private theorem positive_negative_comparison
    (w z : List typeF4RootPairing_base.support) (i j : Fin 4)
    (h : reflectionWord (P := 𝓟) w (signedRoot true i) =
      reflectionWord z (signedRoot false j)) :
    ∃ ε : ℤ, ε ^ 2 = 1 ∧ ∀ n : ℕ,
      transportedMatrix w (eDividedPower (sourceIndex i) n) =
        ε ^ n • transportedMatrix z (fDividedPower (sourceIndex j) n) := by
  let := typeF4RootPairing.indexNeg
  have hr : reflectionWord (P := 𝓟) w (sourceIndex i) =
      reflectionWord (z ++ [sourceIndex j]) (sourceIndex j) := by
    rw [ReeF4.WordRelations.RouteComparison.reflectionWord_append_simple_self,
      ← reflectionWord_neg]
    exact h
  obtain ⟨ε, hε, he⟩ :=
    ReeF4.WordRelations.RouteComparison.transported_eDividedPower_eq_sign_smul
      w (z ++ [sourceIndex j]) (sourceIndex i) (sourceIndex j) hr
  refine ⟨-ε, by simpa only [neg_sq] using hε, fun n => ?_⟩
  rw [he, appended_dividedPower, smul_smul, ← mul_pow]
  simp only [mul_neg_one]

/-- Equal signed root endpoints give one integral sign in every degree. -/
theorem signedDividedPower_comparison
    (w z : List typeF4RootPairing_base.support) (s q : Bool) (i j : Fin 4)
    (h : reflectionWord (P := 𝓟) w (signedRoot s i) =
      reflectionWord z (signedRoot q j)) :
    ∃ ε : ℤ, ε ^ 2 = 1 ∧ ∀ n : ℕ,
      transportedMatrix w (signedDividedPower s i n) =
        ε ^ n • transportedMatrix z (signedDividedPower q j n) := by
  let := typeF4RootPairing.indexNeg
  cases s <;> cases q
  · have hr : reflectionWord (P := 𝓟) w (sourceIndex i) =
        reflectionWord z (sourceIndex j) := by
      change reflectionWord w (-(sourceIndex i) : typeF4Roots) =
        reflectionWord z (-(sourceIndex j) : typeF4Roots) at h
      simpa only [reflectionWord_neg, neg_inj] using h
    exact ReeF4.WordRelations.RouteComparison.transported_fDividedPower_eq_sign_smul
      w z (sourceIndex i) (sourceIndex j) hr
  · obtain ⟨ε, hε, he⟩ := positive_negative_comparison z w j i h.symm
    refine ⟨ε, hε, fun n => ?_⟩
    change transportedMatrix w (fDividedPower (sourceIndex i) n) =
      ε ^ n • transportedMatrix z (eDividedPower (sourceIndex j) n)
    rw [he, smul_smul, ← mul_pow, ← pow_two, hε, one_pow, one_smul]
  · exact positive_negative_comparison w z i j h
  · exact ReeF4.WordRelations.RouteComparison.transported_eDividedPower_eq_sign_smul
      w z (sourceIndex i) (sourceIndex j) h


private theorem route_matrix (F : Type*) [Field F]
    (w : List typeF4RootPairing_base.support) (s : Bool) (i : Fin 4) (t : F) :
    (coverEvaluation F (transportRouteWord F w s i t)).val.val =
      1 + t • specializeMatrix (transportedMatrix w (signedDividedPower s i 1)) +
        t ^ 2 • specializeMatrix (transportedMatrix w (signedDividedPower s i 2)) +
        t ^ 3 • specializeMatrix (transportedMatrix w (signedDividedPower s i 3)) := by
  have hTI : specializeMatrix (S := F) (titsWord (P := 𝓟) w) *
      specializeMatrix (titsWordInv (P := 𝓟) w) = 1 :=
    (rootCurveTitsWord (S := F) w).val_inv
  simp only [transportRouteWord, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv,
    coverEvaluation_of, coverEvaluation_transportTitsWord, coverSimple_val]
  cases s
  · change specializeMatrix (titsWord w) * negativeMatrix (sourceIndex i) t *
      specializeMatrix (titsWordInv w) = _
    simp only [negativeMatrix_formula, signedDividedPower, Bool.false_eq_true, if_false,
      Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
    rw [hTI]
    simp only [specializeMatrix_transportedMatrix]
    rfl
  · change specializeMatrix (titsWord w) * positiveMatrix (sourceIndex i) t *
      specializeMatrix (titsWordInv w) = _
    simp only [positiveMatrix_formula, signedDividedPower, if_true,
      Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
    rw [hTI]
    simp only [specializeMatrix_transportedMatrix]
    rfl

private theorem specialize_sign_smul (F : Type*) [Field F] (ε : ℤ) (n : ℕ)
    (A : Matrix (typeF4RootPairing_base.support ⊕ typeF4Roots) (typeF4RootPairing_base.support ⊕ typeF4Roots) ℤ) :
    specializeMatrix (S := F) (ε ^ n • A) =
      (ε : F) ^ n • specializeMatrix A := by
  ext x y
  change ((ε ^ n * A x y : ℤ) : F) = (ε : F) ^ n * (A x y : F)
  rw [Int.cast_mul, Int.cast_pow]

/-- A single sign gives the parameter change between arbitrary signed routes,
over every field, before any completion or presentation is considered. -/
theorem route_evaluation_comparison (F : Type*) [Field F]
    (w z : List typeF4RootPairing_base.support) (s q : Bool) (i j : Fin 4)
    (h : reflectionWord (P := 𝓟) w (signedRoot s i) =
      reflectionWord z (signedRoot q j)) :
    ∃ ε : ℤ, ε ^ 2 = 1 ∧ ∀ t : F,
      coverEvaluation F (transportRouteWord F w s i t) =
        coverEvaluation F (transportRouteWord F z q j ((ε : F) * t)) := by
  obtain ⟨ε, hε, he⟩ := signedDividedPower_comparison w z s q i j h
  refine ⟨ε, hε, fun t => ?_⟩
  apply Subtype.ext
  apply Units.ext
  rw [route_matrix, route_matrix, he 1, he 2, he 3,
    specialize_sign_smul, specialize_sign_smul, specialize_sign_smul]
  simp only [smul_smul, mul_pow, pow_one, mul_comm]

/-- The canonical root curve has a signed-simple route with the stated root endpoint. -/
theorem root_route (F : Type*) [Field F] (r : typeF4Roots) :
    ∃ (z : List typeF4RootPairing_base.support) (s : Bool) (i : Fin 4),
      reflectionWord (P := typeF4RootPairing) z (signedRoot s i) = r ∧
      ∀ t : F, coverEvaluation F (transportRouteWord F z s i t) =
        ExceptionalSplit.elementaryRoot typeF4RootPairing typeF4RootPairing_base F r t := by
  let := typeF4RootPairing.indexNeg
  by_cases hr : typeF4RootPairing_base.IsPos r
  · let route := rootRoute (P := typeF4RootPairing) (b := typeF4RootPairing_base) r
    refine ⟨route.word, true, typeF4RootPairing_baseEquiv.symm route.simple, ?_, ?_⟩
    · simpa only [signedRoot, if_true, sourceIndex, Equiv.apply_symm_apply] using route.target
    · intro t
      rw [← coverEvaluation_transportRootWord]
      congr 1
      simp only [transportRootWord, if_pos hr, route]
  · let route := rootRoute (P := typeF4RootPairing) (b := typeF4RootPairing_base) (-r)
    refine ⟨route.word, false, typeF4RootPairing_baseEquiv.symm route.simple, ?_, ?_⟩
    · simp only [signedRoot, Bool.false_eq_true, if_false, sourceIndex,
        Equiv.apply_symm_apply, reflectionWord_neg, route.target, neg_neg]
    · intro t
      rw [← coverEvaluation_transportRootWord]
      congr 1
      simp only [transportRootWord, if_neg hr, route]

/-- Root-system endpoint equality gives the literal conjugation formula, with a
single integral sign multiplying the original parameter. -/
theorem root_conjugate_eq_route (F : Type*) [Field F]
    (w z : List typeF4RootPairing_base.support) (r : typeF4Roots) (q : Bool) (j : Fin 4)
    (h : reflectionWord (P := typeF4RootPairing) w r =
      reflectionWord z (signedRoot q j)) :
    ∃ ε : ℤ, ε ^ 2 = 1 ∧ ∀ t : F,
      coverEvaluation F (transportTitsWord F w) *
          ExceptionalSplit.elementaryRoot typeF4RootPairing typeF4RootPairing_base F r t *
          (coverEvaluation F (transportTitsWord F w))⁻¹ =
        coverEvaluation F (transportRouteWord F z q j ((ε : F) * t)) := by
  obtain ⟨v, s, i, hr, he⟩ := root_route F r
  have hroute : reflectionWord (P := typeF4RootPairing) (w ++ v) (signedRoot s i) =
      reflectionWord z (signedRoot q j) := by
    rw [reflectionWord_append, hr]
    exact h
  obtain ⟨ε, hε, hεroute⟩ := route_evaluation_comparison F (w ++ v) z s q i j hroute
  refine ⟨ε, hε, fun t => ?_⟩
  calc
    _ = coverEvaluation F (transportRouteWord F (w ++ v) s i t) := by
      rw [transportRouteWord_append, map_mul, map_mul, map_inv, he]
    _ = _ := hεroute t

end TwistedE6.FoldedSubsystem.F4Identification.ComplementRepresentation.PlaneCharts
