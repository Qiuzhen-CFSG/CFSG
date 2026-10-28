module

public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.Words
public import Theory.AlgebraicGroup.RootSystems.IntegralChevalleyOperatorOrientation
public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Intertwining.Simple.DividedPowers
public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Faithfulness.AdjointEquivariance.LinearExtension

/-!
# Odd-characteristic central elements and oriented F4 operators

The F4 integral root curves are quadratic, including after specialization in
characteristic three. Their values at `1` and `-1` differ by twice the root
operator. Thus a central element of the literal matrix cover commutes with
all root operators whenever `2 ≠ 0`.

We also fix an oriented candidate for the adjoint embedding of the actual
52-coordinate Geck lattice. If `εᵢ` is the bipartite simple-root orientation,
its values on the positive, negative and Cartan simple coordinates are
`εᵢ Eᵢ`, `-εᵢ Fᵢ` and `-εᵢ [Eᵢ,Fᵢ]`. Root routes carry these signs to the
other root coordinates. The normalization is essential in odd characteristic;
the unsigned characteristic-two adjoint map is not used here.

Central elements commute with every value of this candidate. Equivariance
and injectivity of the candidate are separate mathematical obligations; this
module does not assert them or centerlessness of the cover.

Sources: the integral Geck construction and its operator orientations in
`IntegralGeckConstruction` and `IntegralChevalleyOperatorOrientation`;
GLS3 §§2.2–2.6 for the root-group conventions and adjoint versions.
-/

@[expose] public section

open scoped Matrix Classical
open Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction
open Theory.AlgebraicGroup
open ReeF4.WordRelations.Faithfulness
noncomputable section
namespace TwistedE6.FoldedSubsystem.F4Identification.CoverCenter
/-- The literal four Cartan and 48 root coordinates of the cover. -/
abbrev Coordinate := F4Chevalley.BasisIndex
variable (F : Type*) [Field F]
/-- Operator orientation along the same canonical route as the root operator. -/
def rootOperatorOrientation (r : typeF4Roots) : ℤ :=
  let := typeF4RootPairing.indexNeg
  if typeF4RootPairing_base.IsPos r then
    simpleRouteOperatorOrientation true
      (rootRoute (P := typeF4RootPairing) (b := typeF4RootPairing_base) r).word
      (rootRoute (P := typeF4RootPairing) (b := typeF4RootPairing_base) r).simple
  else simpleRouteOperatorOrientation false
      (rootRoute (P := typeF4RootPairing) (b := typeF4RootPairing_base) (-r)).word
      (rootRoute (P := typeF4RootPairing) (b := typeF4RootPairing_base) (-r)).simple

/-- The existing integral all-root operator, specialized to the coefficient field. -/
def specializedRootOperator (r : typeF4Roots) : Matrix Coordinate Coordinate F :=
  (rootOperator (P := typeF4RootPairing) (b := typeF4RootPairing_base) r).map
    (Int.castRingHom F)

/-- Signed root operators and signed simple Cartan commutators. -/
def coordinateOperator : Coordinate → Matrix Coordinate Coordinate F
  | Sum.inr r => (rootOperatorOrientation r : F) • specializedRootOperator F r
  | Sum.inl i =>
      let E := (eMatrix (P := typeF4RootPairing) i).map (Int.castRingHom F)
      let N := (fMatrix (P := typeF4RootPairing) i).map (Int.castRingHom F)
      (-(simpleOperatorOrientation (b := typeF4RootPairing_base) i : F)) • (E * N - N * E)

/-- The fixed linear map whose equivariance and injectivity are still required. -/
def adjointMap : (Coordinate → F) →ₗ[F] Matrix Coordinate Coordinate F :=
  Adjoint.linearExtension (coordinateOperator F)

theorem adjointMap_single (j : Coordinate) :
    adjointMap F (Pi.single j 1) = coordinateOperator F j :=
  Adjoint.linearExtension_single _ _

private theorem commute_linear_of_quadratic
    {n K : Type*} [Fintype n] [DecidableEq n] [Field K]
    (htwo : (2 : K) ≠ 0) (A E B : Matrix n n K)
    (hp : A * (1 + E + B) = (1 + E + B) * A)
    (hn : A * (1 - E + B) = (1 - E + B) * A) : A * E = E * A := by
  have hsub := congrArg₂ (fun X Y : Matrix n n K => X - Y) hp hn
  have he : (2 : K) • (A * E) = (2 : K) • (E * A) := by
    calc
      _ = A * (1 + E + B) - A * (1 - E + B) := by
        simp only [mul_add, mul_sub, mul_one]
        module
      _ = (1 + E + B) * A - (1 - E + B) * A := hsub
      _ = _ := by
        simp only [add_mul, sub_mul, one_mul]
        module
  exact (smul_right_injective _ htwo) he

/-- Centrality of the actual cover implies commutation with each root operator. -/
theorem central_commutes_rootOperator (htwo : (2 : F) ≠ 0)
    (g : Cover F) (hg : g ∈ Subgroup.center (Cover F)) (r : typeF4Roots) :
    Commute (g.val.val) (specializedRootOperator F r) := by
  have hc (t : F) : g.val.val * (F4Chevalley.rootCurve r t).val =
      (F4Chevalley.rootCurve r t).val * g.val.val := by
    have h := Subgroup.mem_center_iff.mp hg (ExceptionalSplit.elementaryRoot
      typeF4RootPairing typeF4RootPairing_base F r t)
    exact (congrArg (fun x : Cover F => x.val.val) h).symm
  have hp := hc 1
  have hn := hc (-1)
  rw [ReeF4.WordRelations.rootCurve_quadratic, F4Chevalley.dividedPower_one] at hp hn
  simp only [one_smul, one_pow, neg_one_sq, neg_smul] at hp hn
  change _ = _
  apply commute_linear_of_quadratic htwo _ _ _
  · exact hp
  · rw [sub_eq_add_neg]
    exact hn

/-- Commutation extends to the signed root and Cartan coordinate operators. -/
theorem central_commutes_coordinateOperator (htwo : (2 : F) ≠ 0)
    (g : Cover F) (hg : g ∈ Subgroup.center (Cover F)) (j : Coordinate) :
    Commute g.val.val (coordinateOperator F j) := by
  let := typeF4RootPairing.indexNeg
  rcases j with i | r
  · have he : Commute g.val.val
        ((eMatrix (P := typeF4RootPairing) i).map (Int.castRingHom F)) := by
      simpa only [specializedRootOperator, rootOperator_simple] using
        central_commutes_rootOperator F htwo g hg i
    have hf : Commute g.val.val
        ((fMatrix (P := typeF4RootPairing) i).map (Int.castRingHom F)) := by
      simpa only [specializedRootOperator, rootOperator_neg_simple] using
        central_commutes_rootOperator F htwo g hg (-i)
    exact ((he.mul_right hf).sub_right (hf.mul_right he)).smul_right _
  · exact (central_commutes_rootOperator F htwo g hg r).smul_right _

/-- Every value of the fixed candidate commutes with a central cover matrix. -/
theorem central_commutes_adjointMap (htwo : (2 : F) ≠ 0)
    (g : Cover F) (hg : g ∈ Subgroup.center (Cover F)) (v : Coordinate → F) :
    Commute g.val.val (adjointMap F v) := by
  apply Commute.sum_right
  intro j _
  exact (central_commutes_coordinateOperator F htwo g hg j).smul_right _

theorem rootOperatorOrientation_sq (r : typeF4Roots) :
    rootOperatorOrientation r * rootOperatorOrientation r = 1 := by
  unfold rootOperatorOrientation
  split <;> exact simpleRouteOperatorOrientation_sq _ _ _

theorem rootOperatorOrientation_simple (i : typeF4RootPairing_base.support) :
    rootOperatorOrientation i = simpleOperatorOrientation (b := typeF4RootPairing_base) i := by
  simp [rootOperatorOrientation, typeF4RootPairing_base.isPos_of_mem_support i.property,
    simpleRouteOperatorOrientation, titsWordSign]

theorem rootOperatorOrientation_neg_simple (i : typeF4RootPairing_base.support) :
    let := typeF4RootPairing.indexNeg
    rootOperatorOrientation (-i : typeF4Roots) =
      -simpleOperatorOrientation (b := typeF4RootPairing_base) i := by
  let := typeF4RootPairing.indexNeg
  dsimp only
  have hi := typeF4RootPairing_base.isPos_of_mem_support i.property
  have hn : ¬typeF4RootPairing_base.IsPos (-i : typeF4Roots) := by
    rw [RootPairing.Base.IsPos.neg_iff_not]
    exact not_not_intro hi
  rw [rootOperatorOrientation]
  rw [if_neg hn, neg_neg, rootRoute_word_simple, rootRoute_simple]
  simp only [simpleRouteOperatorOrientation, titsWordSign, one_mul,
    signedSimpleOperatorOrientation_false]

theorem adjointMap_simple (i : typeF4RootPairing_base.support) :
    adjointMap F (Pi.single (Sum.inr (i : typeF4Roots)) 1) =
      (simpleOperatorOrientation (b := typeF4RootPairing_base) i : F) •
        (eMatrix (P := typeF4RootPairing) i).map (Int.castRingHom F) := by
  rw [adjointMap_single]
  simp only [coordinateOperator, rootOperatorOrientation_simple,
    specializedRootOperator, rootOperator_simple]

theorem adjointMap_neg_simple (i : typeF4RootPairing_base.support) :
    let := typeF4RootPairing.indexNeg
    adjointMap F (Pi.single (Sum.inr (-i : typeF4Roots)) 1) =
      -(simpleOperatorOrientation (b := typeF4RootPairing_base) i : F) •
        (fMatrix (P := typeF4RootPairing) i).map (Int.castRingHom F) := by
  let := typeF4RootPairing.indexNeg
  dsimp only
  rw [adjointMap_single]
  simp only [coordinateOperator, rootOperatorOrientation_neg_simple, Int.cast_neg,
    specializedRootOperator, rootOperator_neg_simple]


end TwistedE6.FoldedSubsystem.F4Identification.CoverCenter
