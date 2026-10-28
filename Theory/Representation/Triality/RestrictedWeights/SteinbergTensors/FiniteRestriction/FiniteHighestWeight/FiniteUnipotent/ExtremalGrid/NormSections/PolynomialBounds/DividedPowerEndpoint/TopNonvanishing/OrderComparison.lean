module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid.NormSections.PolynomialBounds.DividedPowerEndpoint.Operators
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid.NormSections.PolynomialBounds.DividedPowerEndpoint.TopNonvanishing.WeylOrder
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid.Dimension.WeylCovers.DimensionBound.TruncatedAlgebra.CoefficientLaws
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid.Dimension.WeylCovers.DimensionBound.TruncatedAlgebra.RootPairs
/-!
# Order comparison for the D4 top divided-power words

The literal height order and the reversed convex operator order give the same
endomorphism on every finite-dimensional rational module, for both signs.
No highest-vector, cyclicity, nonvanishing or basis hypothesis is needed.

For a sum root c = a + b, exchange the top coefficients of a and b while
retaining the top coefficient of c immediately to their right. In each
positive-degree correction term, the c coefficient commutes past the remaining
a coefficient and meets that top coefficient. Their exponents cross 2^n,
so the binary-carry multiplication law makes the term zero. The degree-zero
term is precisely the exchanged word, regardless of the root-string constant.
A kernel-checked sequence of seventy such moves and ordinary commuting moves
connects the two twelve-root orders. Integral coordinate calculations connect
every move to the actual roots through S.rootIndex, for each sign separately.

Sources: Steinberg, *Representations of algebraic groups* (1963), §§2.8 and 4.3;
GLS3 Chapter1.tex §1.12 and Chapter2St2.tex §6. The supplied root parameters
and the root/coroot convention are unchanged.
-/

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid.DividedPowerEndpoint
open CyclicDimension CyclicDimension.RootPairGeometry
public noncomputable section
universe u v
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K]
variable {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- Distinct nonopposite D4 roots with pairing zero or one have no sum root. -/
private theorem coefficients_commute (S : Geometry K) (hrel : RootPairParameterRelations S)
    (rho : RationalRepresentation K V) (hr : IsRationalRepresentation rho)
    (a b : S.roots.Root)
    (hp : (typeDRootPairing 2).pairing (S.rootIndex a) (S.rootIndex b) = 0 ∨
      (typeDRootPairing 2).pairing (S.rootIndex a) (S.rootIndex b) = 1) (i j : ℕ) :
    Commute (rootCoefficient S rho hr a i) (rootCoefficient S rho hr b j) := by
  apply rootCoefficient_commute_of_parameterRelations S hrel rho hr a b
  · intro hab
    subst b
    rw [RootPairing.pairing_same] at hp
    rcases hp with hp | hp <;> norm_num at hp
  · intro hab
    rw [hab, S.based.2.2.1, RootPairing.pairing_reflectionPerm_self_right,
      RootPairing.pairing_same] at hp
    rcases hp with hp | hp <;> norm_num at hp
  · rintro ⟨c, hc⟩
    have hs := d4_sum_pairing _ _ _ hc
    rw [hs] at hp
    rcases hp with hp | hp <;> norm_num at hp

/-- The existing top coefficient of the sum root kills every exchange correction. -/
private theorem top_triple (S : Geometry K) (hrel : RootPairParameterRelations S)
    (rho : RationalRepresentation K V) (hr : IsRationalRepresentation rho)
    (a b c : S.roots.Root) (hs : RootSum S a b c) (n : ℕ) :
    rootCoefficient S rho hr a (2 ^ n - 1) * rootCoefficient S rho hr b (2 ^ n - 1) *
        rootCoefficient S rho hr c (2 ^ n - 1) =
      rootCoefficient S rho hr b (2 ^ n - 1) * rootCoefficient S rho hr a (2 ^ n - 1) *
        rootCoefficient S rho hr c (2 ^ n - 1) := by
  let P := typeDRootPairing 2
  have hac : P.pairing (S.rootIndex a) (S.rootIndex c) = 1 := by
    rw [d4_pairing_symm]
    have he := RootPairing.pairing_eq_add_of_root_eq_add (P := P) (l := S.rootIndex a) hs
    rw [he, RootPairing.pairing_same, d4_pairing_symm (S.rootIndex b),
      d4_sum_pairing _ _ _ hs]
    norm_num
  obtain ⟨κ, _, he⟩ := rootCoefficient_exchange_of_parameterRelations S hrel rho hr a b c hs
  let M := 2 ^ n - 1
  have hq : 0 < (2 : ℕ) ^ n := pow_pos (by decide) _
  have hM : M < 2 ^ n := by dsimp [M]; omega
  change rootCoefficient S rho hr a M * rootCoefficient S rho hr b M *
      rootCoefficient S rho hr c M = _
  rw [he, min_self, Finset.sum_mul]
  rw [Finset.sum_eq_single 0]
  · simp only [pow_zero, one_smul, Nat.sub_zero, rootCoefficient,
      curveCoefficient_zero, mul_one, M]
  · intro m hm hm0
    have hmM : m ≤ M := Nat.le_of_lt_succ (Finset.mem_range.mp hm)
    have hzero := rootCoefficient_mul_eq_zero S rho hr c n m M
      (lt_of_le_of_lt hmM hM) hM (by dsimp [M] at *; omega)
    have hca := (coefficients_commute S hrel rho hr a c (Or.inr hac) (M - m) m).symm
    rw [smul_mul_assoc,
      mul_assoc (rootCoefficient S rho hr b (M - m)) _ (rootCoefficient S rho hr a (M - m)),
      hca, ← mul_assoc (rootCoefficient S rho hr b (M - m)) _ (rootCoefficient S rho hr c m),
      mul_assoc _ (rootCoefficient S rho hr c m), hzero, mul_zero, smul_zero]
  · intro h
    exact (h (Finset.mem_range.mpr (Nat.zero_lt_succ M))).elim
/-- Integral standard coordinates of the published twelve positive roots. -/
private def rootVector : Fin 12 → Fin 4 → ℤ :=
  ![![1,-1,0,0], ![0,0,1,-1], ![0,0,1,1], ![0,1,-1,0],
    ![1,0,-1,0], ![0,1,0,-1], ![0,1,0,1], ![1,0,0,-1],
    ![0,1,1,0], ![1,0,0,1], ![1,0,1,0], ![1,1,0,0]]

private def vectorPairing (i j : Fin 12) : ℤ :=
  ∑ l : Fin 4, rootVector j l * rootVector i l

private def CommutePair (i j : Fin 12) : Prop :=
  vectorPairing i j = 0 ∨ vectorPairing i j = 1

private def SumTriple (i j c : Fin 12) : Prop :=
  rootVector c = rootVector i + rootVector j

private theorem rootVector_cast (i : Fin 12) (j : Fin 4) :
    (rootVector i j : ℝ) =
      (typeDRootEmbedding 4 (Triality.Standard.PositiveCoordinates.rootIndex i) : Vec 4) j := by
  fin_cases i <;> fin_cases j <;>
    norm_num [rootVector, Triality.Standard.PositiveCoordinates.rootIndex,
      Triality.Standard.PositiveCoordinates.difference, Triality.Standard.PositiveCoordinates.sumRoot,
      typeDRootEmbedding, typeDRootVector, basisVector, Pi.single_apply, Fin.ext_iff]

private theorem vectorPairing_cast (i j : Fin 12) :
    (vectorPairing i j : ℝ) = (typeDRootPairing 2).pairing
      (Triality.Standard.PositiveCoordinates.rootIndex i)
      (Triality.Standard.PositiveCoordinates.rootIndex j) := by
  simp only [vectorPairing, Int.cast_sum, Int.cast_mul, rootVector_cast,
    typeDRootPairing_pairing, dot]

private def signedRoot (S : Geometry K) (negative : Bool) (i : Fin 12) : S.roots.Root :=
  if negative then negativeCoordinateRoot S i else positiveCoordinateRoot S i

omit [IsAlgClosed k] in
private theorem signed_pairing (S : Geometry K) (negative : Bool) (i j : Fin 12) :
    (typeDRootPairing 2).pairing (S.rootIndex (signedRoot S negative i))
      (S.rootIndex (signedRoot S negative j)) = (vectorPairing i j : ℝ) := by
  cases negative <;>
    simp only [signedRoot, Bool.false_eq_true, if_false, if_true,
      negativeCoordinateRoot, S.based.2.2.1, positiveCoordinateRoot, Equiv.apply_symm_apply,
      RootPairing.pairing_reflectionPerm_self_left, RootPairing.pairing_reflectionPerm_self_right,
      neg_neg, vectorPairing_cast]

omit [IsAlgClosed k] in
private theorem signed_sum (S : Geometry K) (negative : Bool) (i j c : Fin 12)
    (h : SumTriple i j c) :
    RootSum S (signedRoot S negative i) (signedRoot S negative j) (signedRoot S negative c) := by
  have he : (typeDRootPairing 2).root (Triality.Standard.PositiveCoordinates.rootIndex c) =
      (typeDRootPairing 2).root (Triality.Standard.PositiveCoordinates.rootIndex i) +
      (typeDRootPairing 2).root (Triality.Standard.PositiveCoordinates.rootIndex j) := by
    apply Subtype.ext
    funext l
    have hl := congrFun h l
    change rootVector c l = rootVector i l + rootVector j l at hl
    change (typeDRootEmbedding 4 (Triality.Standard.PositiveCoordinates.rootIndex c) : Vec 4) l =
      (typeDRootEmbedding 4 (Triality.Standard.PositiveCoordinates.rootIndex i) : Vec 4) l +
      (typeDRootEmbedding 4 (Triality.Standard.PositiveCoordinates.rootIndex j) : Vec 4) l
    rw [← rootVector_cast, ← rootVector_cast, ← rootVector_cast]
    exact_mod_cast hl
  cases negative <;>
    simp only [RootSum, signedRoot, Bool.false_eq_true, if_false, if_true,
      negativeCoordinateRoot, S.based.2.2.1, positiveCoordinateRoot, Equiv.apply_symm_apply,
      RootPairing.root_reflectionPerm, RootPairing.reflection_apply_self]
  · exact he
  · rw [he, neg_add]

private theorem signed_coefficients_commute (S : Geometry K)
    (hrel : RootPairParameterRelations S) (rho : RationalRepresentation K V)
    (hr : IsRationalRepresentation rho) (negative : Bool) (i j : Fin 12)
    (h : CommutePair i j) (a b : ℕ) :
    Commute (rootCoefficient S rho hr (signedRoot S negative i) a)
      (rootCoefficient S rho hr (signedRoot S negative j) b) := by
  apply coefficients_commute S hrel rho hr
  rw [signed_pairing]
  rcases h with h | h
  · exact Or.inl (by rw [h, Int.cast_zero])
  · exact Or.inr (by rw [h, Int.cast_one])

private instance (i j : Fin 12) : Decidable (CommutePair i j) :=
  inferInstanceAs (Decidable (vectorPairing i j = 0 ∨ vectorPairing i j = 1))

private instance (i j c : Fin 12) : Decidable (SumTriple i j c) :=
  inferInstanceAs (Decidable (rootVector c = rootVector i + rootVector j))

private def swapAt : ℕ → List (Fin 12) → List (Fin 12)
  | 0, a :: b :: rest => b :: a :: rest
  | j + 1, a :: rest => a :: swapAt j rest
  | _, L => L

/-- A move either commutes two roots or uses the following sum-root top factor. -/
private def canSwap : ℕ → List (Fin 12) → Bool
  | 0, a :: b :: rest => decide (CommutePair a b) ||
      match rest with
      | c :: _ => decide (SumTriple a b c)
      | [] => false
  | j + 1, _ :: rest => canSwap j rest
  | _, _ => false

private theorem prod_swap {A : Type*} [Monoid A] (T : Fin 12 → A)
    (hc : ∀ a b, CommutePair a b → Commute (T a) (T b))
    (hs : ∀ a b c, SumTriple a b c → T a * T b * T c = T b * T a * T c)
    (j : ℕ) (L : List (Fin 12)) (h : canSwap j L = true) :
    (L.map T).prod = ((swapAt j L).map T).prod := by
  induction j generalizing L with
  | zero =>
    cases L with
    | nil => simp [canSwap] at h
    | cons a L =>
      cases L with
      | nil => simp [canSwap] at h
      | cons b L =>
        cases L with
        | nil =>
          have hab : CommutePair a b := by simpa [canSwap] using h
          simpa [swapAt] using (hc a b hab).eq
        | cons c L =>
          have hab : CommutePair a b ∨ SumTriple a b c := by simpa [canSwap] using h
          rcases hab with hab | hab
          · simpa only [swapAt, List.map_cons, List.prod_cons, mul_assoc] using
              congrArg (fun x => x * ((c :: L).map T).prod) (hc a b hab).eq
          · simpa only [swapAt, List.map_cons, List.prod_cons, mul_assoc] using
              congrArg (fun x => x * (L.map T).prod) (hs a b c hab)
  | succ j ih =>
    cases L with
    | nil => simp [canSwap] at h
    | cons a L =>
      simpa only [swapAt, List.map_cons, List.prod_cons] using
        congrArg (T a * ·) (ih L h)

private def performMoves : List ℕ → List (Fin 12) → List (Fin 12)
  | [], L => L
  | j :: js, L => performMoves js (swapAt j L)

private def movesValid : List ℕ → List (Fin 12) → Bool
  | [], _ => true
  | j :: js, L => canSwap j L && movesValid js (swapAt j L)

private theorem prod_moves {A : Type*} [Monoid A] (T : Fin 12 → A)
    (hc : ∀ a b, CommutePair a b → Commute (T a) (T b))
    (hs : ∀ a b c, SumTriple a b c → T a * T b * T c = T b * T a * T c)
    (js : List ℕ) (L : List (Fin 12)) (h : movesValid js L = true) :
    (L.map T).prod = ((performMoves js L).map T).prod := by
  induction js generalizing L with
  | nil => rfl
  | cons j js ih =>
    have hh : canSwap j L = true ∧ movesValid js (swapAt j L) = true := by
      simpa only [movesValid, Bool.and_eq_true] using h
    obtain ⟨h₁, h₂⟩ := hh
    exact (prod_swap T hc hs j L h₁).trans (ih (swapAt j L) h₂)

/-- Adjacent positions in the finite collection path; each is checked by `canSwap`. -/
private def comparisonMoves : List ℕ :=
  [1, 0, 1, 7, 6, 5, 10, 9, 8, 7, 6, 4, 6, 7,
    8, 9, 10, 3, 9, 8, 7, 6, 5, 10, 9, 8, 7, 6,
    4, 6, 7, 8, 9, 10, 2, 3, 6, 5, 10, 8, 10, 7,
    6, 4, 6, 7, 10, 8, 10, 7, 6, 9, 8, 7, 5, 7,
    8, 9, 10, 9, 8, 7, 6, 7, 10, 9, 8, 10, 9, 10]

private theorem finite_collection {A : Type*} [Monoid A] (T : Fin 12 → A)
    (hc : ∀ a b, CommutePair a b → Commute (T a) (T b))
    (hs : ∀ a b c, SumTriple a b c → T a * T b * T c = T b * T a * T c) :
    (([0,1,2,3,4,5,6,7,8,9,10,11] : List (Fin 12)).map T).prod =
      (([2,1,8,10,5,6,11,3,9,7,4,0] : List (Fin 12)).map T).prod := by
  have hvalid : movesValid comparisonMoves [0,1,2,3,4,5,6,7,8,9,10,11] = true := by
    decide +kernel
  have hout : performMoves comparisonMoves [0,1,2,3,4,5,6,7,8,9,10,11] =
      [2,1,8,10,5,6,11,3,9,7,4,0] := by decide +kernel
  simpa only [hout] using prod_moves T hc hs comparisonMoves _ hvalid

private theorem signed_top_order (S : Geometry K) (hrel : RootPairParameterRelations S)
    (rho : RationalRepresentation K V) (hr : IsRationalRepresentation rho)
    (negative : Bool) (n : ℕ) :
    topOperator S rho hr (signedRoot S negative) n =
      topOperator S rho hr (fun i => signedRoot S negative (convexOperatorOrder i)) n := by
  let T : Fin 12 → Module.End k V :=
    fun i => rootCoefficient S rho hr (signedRoot S negative i) (2 ^ n - 1)
  have hc (i j : Fin 12) (h : CommutePair i j) : Commute (T i) (T j) :=
    signed_coefficients_commute S hrel rho hr negative i j h _ _
  have hs (i j c : Fin 12) (h : SumTriple i j c) :
      T i * T j * T c = T j * T i * T c :=
    top_triple S hrel rho hr _ _ _ (signed_sum S negative i j c h) n
  change (([0,1,2,3,4,5,6,7,8,9,10,11] : List (Fin 12)).map T).prod =
    (([2,1,8,10,5,6,11,3,9,7,4,0] : List (Fin 12)).map T).prod
  exact finite_collection T hc hs

/-- The literal positive top-word comparison directly from the actual parameter relations. -/
theorem positive_topOperator_eq_convexOrder_of_relations (S : Geometry K)
    (hrel : RootPairParameterRelations S)
    (rho : RationalRepresentation K V) (hr : IsRationalRepresentation rho) (n : ℕ) :
    topOperator S rho hr (positiveCoordinateRoot S) n =
      topOperator S rho hr (fun i => positiveCoordinateRoot S (convexOperatorOrder i)) n :=
  signed_top_order S hrel rho hr false n

/-- The negative comparison retains the same actual relations and root parameters. -/
theorem negative_topOperator_eq_convexOrder_of_relations (S : Geometry K)
    (hrel : RootPairParameterRelations S)
    (rho : RationalRepresentation K V) (hr : IsRationalRepresentation rho) (n : ℕ) :
    topOperator S rho hr (negativeCoordinateRoot S) n =
      topOperator S rho hr (fun i => negativeCoordinateRoot S (convexOperatorOrder i)) n :=
  signed_top_order S hrel rho hr true n

/-- The positive top divided-power word agrees in literal height order and
in the reversed convex order. The equality holds on the whole module. -/
theorem positive_topOperator_eq_convexOrder (S : Geometry K)
    (hcharts : ∀ i : Fin 4, Nonempty
      (ClassBound.FixedOpposition.AmbientNormalizer.CorootRealization.SimpleRootSL2Chart S i))
    (hcomm : ClassBound.ConnectedCentralizer.Bruhat.Coordinates.Normalization.PositiveCommutatorContainment S)
    (hunique : ClassBound.ConnectedCentralizer.Normalizer.RootSubgroupUniqueness S)
    (rho : RationalRepresentation K V) (hr : IsRationalRepresentation rho) (n : ℕ) :
    topOperator S rho hr (positiveCoordinateRoot S) n =
      topOperator S rho hr (fun i => positiveCoordinateRoot S (convexOperatorOrder i)) n :=
  signed_top_order S (rootPairParameterRelations_of_geometry S hcharts hcomm hunique)
    rho hr false n

/-- The negative top word has the same order comparison, using the actual
negative parameters and their own root-string constants. -/
theorem negative_topOperator_eq_convexOrder (S : Geometry K)
    (hcharts : ∀ i : Fin 4, Nonempty
      (ClassBound.FixedOpposition.AmbientNormalizer.CorootRealization.SimpleRootSL2Chart S i))
    (hcomm : ClassBound.ConnectedCentralizer.Bruhat.Coordinates.Normalization.PositiveCommutatorContainment S)
    (hunique : ClassBound.ConnectedCentralizer.Normalizer.RootSubgroupUniqueness S)
    (rho : RationalRepresentation K V) (hr : IsRationalRepresentation rho) (n : ℕ) :
    topOperator S rho hr (negativeCoordinateRoot S) n =
      topOperator S rho hr (fun i => negativeCoordinateRoot S (convexOperatorOrder i)) n :=
  signed_top_order S (rootPairParameterRelations_of_geometry S hcharts hcomm hunique)
    rho hr true n

end
end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid.DividedPowerEndpoint
