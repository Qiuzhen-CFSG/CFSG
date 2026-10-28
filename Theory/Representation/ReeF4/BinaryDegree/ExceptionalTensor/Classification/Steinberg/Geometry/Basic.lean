module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Parameters
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.CoefficientFrobenius.Carrier
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.BasicMinimum.HighestWeight
public import Theory.AlgebraicGroup.Automorphisms.Steinberg

/-!
# Frobenius and descent on the concrete algebraic F4 carrier

The coefficient Frobenius action is a genuine algebraic-group morphism: every
presented coordinate is sent to its square. Root generation shows that an
endomorphism satisfying the exceptional long/short formula squares to this
morphism on points. This implies bijectivity over an algebraically closed field.
The same root formula determines the images of the actual normalizer and
positive-coroot words, including the four numbered simple coroots.

An exceptional fixed point is fixed by a power of Frobenius. The splitting
polynomial of the finite coefficient field therefore puts every coordinate in
that field's image. This also proves finiteness of the fixed set. Identifying
that set with the image of the concrete Ree group still requires descent into
the *root-generated* finite split group; the last assembly theorem retains
that premise explicitly. Neither exceptional-morphism existence nor the
semisimple, universal, or Borel geometry is asserted here.

Sources: GLS3, Theorem 1.15.4(b); Steinberg, *Lectures on Chevalley Groups*,
Theorem 7 and its third corollary, and Theorem 28
(`refs/KGroup/GLS3/Chapter1.tex`, `Chapter2St1.tex`); Steinberg,
*Representations of Algebraic Groups* (1963), Sections 10 and 12.
-/

public section

open Theory.AlgebraicGroup
open ReeF4.BinaryDegree.ExceptionalTensor.Classification.CoefficientFrobenius
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry
universe u
variable {F : Type u} [Field F] [IsAlgClosed F]

/-- Homomorphisms out of the literal carrier agree if they agree on every root curve. -/
theorem point_hom_ext {G : Type*} [Group G]
    (a b : PointGroup F →* G)
    (h : ∀ r t, a (algebraicRootElement r t) = b (algebraicRootElement r t)) : a = b := by
  apply MonoidHom.eq_of_eqOn_dense algebraicRootElements_generate
  rintro _ ⟨⟨r, t⟩, rfl⟩
  exact h r t

variable [CharP F 2]
/-- Coordinate squaring is an algebraic-group morphism of the actual closed carrier. -/
noncomputable def frobeniusMorphism :
    Theory.AlgebraicGroup.Morphism (F4Chevalley.Carrier (k := F)) (F4Chevalley.Carrier (k := F)) where
  toVariety :=
    { toFun := (carrierCoefficientAction (frobeniusEquiv F 2)).equiv
      regular := by
        intro i
        refine ⟨MvPolynomial.X i ^ 2, ?_⟩
        intro x
        rw [(carrierCoefficientAction (frobeniusEquiv F 2)).coordinate]
        simp [frobeniusEquiv_apply, frobenius_def, evalPolynomial] }
  map_one := map_one _
  map_mul := map_mul _

/-- The point endomorphism of the concrete coordinate Frobenius morphism. -/
@[expose] noncomputable def frobeniusEnd : Monoid.End (PointGroup F) :=
  frobeniusMorphism.onPoints

/-- The polynomial Frobenius induces the named point endomorphism. -/
@[simp] theorem frobeniusMorphism_onPoints :
    (frobeniusMorphism (F := F)).onPoints = frobeniusEnd := rfl

/-- Frobenius squares every coordinate of the presented closed variety. -/
theorem frobeniusEnd_coordinate (x : PointGroup F)
    (i : (F4Chevalley.Carrier (k := F)).Coordinates) :
    (frobeniusEnd x).val i = x.val i ^ 2 :=
  (carrierCoefficientAction (frobeniusEquiv F 2)).coordinate x i

/-- Coordinate Frobenius has the expected formula on the actual root elements. -/
theorem frobeniusEnd_root (r : F4Chevalley.Root) (t : F) :
    frobeniusEnd (algebraicRootElement r t) = algebraicRootElement r (t ^ 2) := by
  exact carrierCoefficient_root (frobeniusEquiv F 2) r t

/-- Frobenius is bijective on algebraically closed points; no regular inverse is claimed. -/
theorem frobeniusEnd_bijective : Function.Bijective (frobeniusEnd (F := F)) :=
  (carrierCoefficientAction (frobeniusEquiv F 2)).equiv.bijective

/-- The exceptional root formula forces the square identity on the whole point group. -/
theorem exceptional_square (ψ : Monoid.End (PointGroup F))
    (hψ : HasExceptionalRootFormula ψ) : ψ ^ 2 = frobeniusEnd := by
  apply point_hom_ext
  intro r t
  change ψ (ψ (algebraicRootElement r t)) = _
  rw [hψ, hψ, exceptionalParameter_twice, exceptionalRootPermutation_involutive]
  exact (frobeniusEnd_root r t).symm

/-- The exceptional root formula forces bijectivity on algebraically closed points. -/
theorem exceptional_bijective (ψ : Monoid.End (PointGroup F))
    (hψ : HasExceptionalRootFormula ψ) : Function.Bijective ψ := by
  have hsq (x : PointGroup F) : ψ (ψ x) = frobeniusEnd x :=
    DFunLike.congr_fun (exceptional_square ψ hψ) x
  constructor
  · intro x y h
    apply frobeniusEnd_bijective.1
    simpa only [hsq] using congrArg ψ h
  · intro y
    obtain ⟨x, hx⟩ := frobeniusEnd_bijective.2 y
    exact ⟨ψ x, (hsq x).trans hx⟩

omit [CharP F 2] in
/-- There is at most one point endomorphism with the specified exceptional root formula. -/
theorem exceptional_unique (ψ χ : Monoid.End (PointGroup F))
    (hψ : HasExceptionalRootFormula ψ) (hχ : HasExceptionalRootFormula χ) : ψ = χ := by
  apply point_hom_ext
  intro r t
  exact (hψ r t).trans (hχ r t).symm

/-- An exceptional endomorphism commutes with coordinate Frobenius. -/
theorem exceptional_commutes_frobenius (ψ : Monoid.End (PointGroup F))
    (hψ : HasExceptionalRootFormula ψ) : Commute ψ frobeniusEnd := by
  rw [← exceptional_square ψ hψ]
  exact Commute.self_pow ψ 2

/-- Every even exceptional power is a power of coordinate Frobenius. -/
theorem exceptional_even_power (ψ : Monoid.End (PointGroup F))
    (hψ : HasExceptionalRootFormula ψ) (n : ℕ) :
    ψ ^ (2 * n) = frobeniusEnd ^ n := by
  rw [pow_mul, exceptional_square ψ hψ]

/-- Every odd exceptional power is the exceptional map followed by Frobenius. -/
theorem exceptional_odd_power (ψ : Monoid.End (PointGroup F))
    (hψ : HasExceptionalRootFormula ψ) (n : ℕ) :
    ψ ^ (2 * n + 1) = ψ * frobeniusEnd ^ n := by
  rw [pow_succ', exceptional_even_power ψ hψ]

/-- An iterated Frobenius acts by the corresponding power on every coordinate. -/
theorem frobeniusEnd_pow_coordinate (n : ℕ) (x : PointGroup F)
    (i : (F4Chevalley.Carrier (k := F)).Coordinates) :
    ((frobeniusEnd ^ n) x).val i = x.val i ^ (2 ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ']
    change (frobeniusEnd ((frobeniusEnd ^ n) x)).val i = _
    rw [frobeniusEnd_coordinate, ih, ← pow_mul, ← pow_succ]

/-- An exceptional fixed point is fixed by the corresponding Frobenius power. -/
theorem exceptional_fixed_frobenius_fixed (ψ : Monoid.End (PointGroup F))
    (hψ : HasExceptionalRootFormula ψ) (n : ℕ) {x : PointGroup F}
    (hx : (ψ ^ n) x = x) : (frobeniusEnd ^ n) x = x := by
  rw [← exceptional_even_power ψ hψ n, Nat.mul_comm 2 n, pow_mul, pow_two]
  change (ψ ^ n) ((ψ ^ n) x) = x
  rw [hx, hx]

omit [IsAlgClosed F] [CharP F 2] in
/-- The image of the finite coefficient field is exactly the roots of its field polynomial. -/
theorem coefficient_mem_range_iff {k : ℕ} (f : CoefficientField k →+* F) (t : F) :
    t ∈ f.range ↔ t ^ (2 ^ (2 * k + 1)) = t := by
  constructor
  · rintro ⟨s, rfl⟩
    rw [← map_pow, field_pow]
  · intro ht
    let p : Polynomial (CoefficientField k) := Polynomial.X ^ (2 ^ (2 * k + 1)) - Polynomial.X
    have hp : p ≠ 0 := FiniteField.X_pow_card_pow_sub_X_ne_zero _ (by omega) (by omega)
    have hcard : Fintype.card (CoefficientField k) = 2 ^ (2 * k + 1) := by
      rw [← Nat.card_eq_fintype_card, field_card]
    have hs : p.Splits := by
      apply Polynomial.splits_iff_card_roots.mpr
      rw [show p = Polynomial.X ^ Fintype.card (CoefficientField k) - Polynomial.X by
        rw [hcard], FiniteField.roots_X_pow_card_sub_X]
      rw [Finset.card_val, Finset.card_univ,
        FiniteField.X_pow_card_sub_X_natDegree_eq _ Fintype.one_lt_card]
    apply hs.mem_range_of_isRoot hp
    simp [p, Polynomial.IsRoot, ht]

/-- All coordinates of an odd exceptional fixed point lie in the finite field image. -/
theorem fixed_coordinates_mem_range {k : ℕ} (f : CoefficientField k →+* F)
    (ψ : Monoid.End (PointGroup F)) (hψ : HasExceptionalRootFormula ψ)
    {x : PointGroup F} (hx : (ψ ^ (2 * k + 1)) x = x)
    (i : (F4Chevalley.Carrier (k := F)).Coordinates) : x.val i ∈ f.range := by
  apply (coefficient_mem_range_iff f _).mpr
  have he := congrArg (fun y : PointGroup F => y.val i)
    (exceptional_fixed_frobenius_fixed ψ hψ (2 * k + 1) hx)
  rwa [frobeniusEnd_pow_coordinate] at he

/-- Rational-point descent into the finite root-generated group gives full Ree fixed-point coverage. -/
theorem modelEmbedding_range_eq_fixed_of_descent {k : ℕ}
    (f : CoefficientField k →+* F)
    (hdescent : ∀ x : PointGroup F,
      (∀ i, x.val i ∈ f.range) → x ∈ (splitEmbedding f).range)
    (ψ : Monoid.End (PointGroup F)) (hψ : HasExceptionalRootFormula ψ) :
    ((modelEmbedding f).range : Set (PointGroup F)) =
      {x | (ψ ^ (2 * k + 1)) x = x} := by
  ext x
  constructor
  · intro hx
    exact ((mem_modelEmbedding_range f ψ hψ x).mp hx).2
  · intro hx
    exact (mem_modelEmbedding_range f ψ hψ x).mpr
      ⟨hdescent x (fixed_coordinates_mem_range f ψ hψ hx), hx⟩

omit [CharP F 2] in
/-- There are only finitely many points with all coordinates in the finite coefficient field. -/
theorem rational_coordinates_finite {k : ℕ} (f : CoefficientField k →+* F) :
    {x : PointGroup F | ∀ i, x.val i ∈ f.range}.Finite := by
  have hf : (f.range : Set F).Finite := Set.finite_range f
  have hpi : {v : (F4Chevalley.Carrier (k := F)).Coordinates → F |
      ∀ i, v i ∈ f.range}.Finite := Set.Finite.pi' (fun _ => hf)
  exact Set.Finite.preimage (f := fun x : PointGroup F => x.val)
    (fun _ _ _ _ h => Variety.Point.ext h) hpi

/-- For an actual exceptional algebraic morphism, the square identity holds as morphisms. -/
theorem exceptional_morphism_square
    (Ψ : Theory.AlgebraicGroup.Morphism
      (F4Chevalley.Carrier (k := F)) (F4Chevalley.Carrier (k := F)))
    (hΨ : HasExceptionalRootFormula Ψ.onPoints) : Ψ.comp Ψ = frobeniusMorphism := by
  apply Theory.AlgebraicGroup.Morphism.ext
  funext x
  exact DFunLike.congr_fun (exceptional_square Ψ.onPoints hΨ) x

/-- Every odd exceptional power has a finite fixed set, independently of rational-point descent. -/
theorem exceptional_odd_fixed_finite {k : ℕ} (f : CoefficientField k →+* F)
    (ψ : Monoid.End (PointGroup F)) (hψ : HasExceptionalRootFormula ψ) :
    {x : PointGroup F | (ψ ^ (2 * k + 1)) x = x}.Finite := by
  apply (rational_coordinates_finite f).subset
  intro x hx
  exact fixed_coordinates_mem_range f ψ hψ hx

/-- An algebraic morphism with the exceptional root formula is a Steinberg endomorphism. -/
theorem exceptional_isSteinberg
    (Ψ : Theory.AlgebraicGroup.Morphism
      (F4Chevalley.Carrier (k := F)) (F4Chevalley.Carrier (k := F)))
    (hΨ : HasExceptionalRootFormula Ψ.onPoints) : IsAlgebraicSteinbergEndomorphism Ψ := by
  refine ⟨(exceptional_bijective Ψ.onPoints hΨ).2, ?_⟩
  let ψ : Monoid.End (PointGroup F) := Ψ.onPoints
  have hfinite := exceptional_odd_fixed_finite (coefficientHom F 0) ψ hΨ
  change {x : PointGroup F | (ψ ^ 1) x = x}.Finite at hfinite
  rw [pow_one] at hfinite
  exact hfinite.to_subtype

/-- The exceptional formula propagates to the actual rank-one normalizer words. -/
theorem exceptional_normalizer (ψ : Monoid.End (PointGroup F))
    (hψ : HasExceptionalRootFormula ψ) (r : F4Chevalley.Root) (t : Fˣ) :
    ψ (algebraicNElement r t) =
      algebraicNElement (exceptionalRootPermutation r) (exceptionalParameter r t) := by
  let := StandardRootSystem.typeF4RootPairing.indexNeg
  change ∀ r t, ψ (algebraicRootElement r t) =
    algebraicRootElement (exceptionalRootPermutation r) (exceptionalParameter r t) at hψ
  simp only [algebraicNElement, map_mul]
  change ψ (algebraicRootElement r (t : F)) *
    ψ (algebraicRootElement (-r) (-((t : F)⁻¹))) * ψ (algebraicRootElement r (t : F)) = _
  rw [hψ, hψ, exceptionalRootPermutation_neg, exceptionalParameter_neg]
  by_cases hr : IsLongRoot r
  · simp only [exceptionalParameter_of_long hr]
  · simp only [exceptionalParameter_of_short hr, Units.val_pow_eq_pow_val]
    rw [CharTwo.neg_eq, CharTwo.neg_eq, inv_pow]

/-- The exceptional formula propagates to the chosen positive-coroot convention. -/
theorem exceptional_coroot (ψ : Monoid.End (PointGroup F))
    (hψ : HasExceptionalRootFormula ψ) (r : F4Chevalley.Root) (t : Fˣ) :
    ψ (algebraicCorootElement r t) =
      algebraicCorootElement (exceptionalRootPermutation r) (exceptionalParameter r t) := by
  have h1 : exceptionalParameter r (1 : Fˣ) = 1 := by
    by_cases hr : IsLongRoot r
    · rw [exceptionalParameter_of_long hr]
    · rw [exceptionalParameter_of_short hr, one_pow]
  simp only [algebraicCorootElement, map_mul, map_inv, exceptional_normalizer ψ hψ, h1]

/-- The four actual simple coroots are reversed, with the long/short parameter exponents. -/
theorem exceptional_simple_coroot (ψ : Monoid.End (PointGroup F))
    (hψ : HasExceptionalRootFormula ψ) (i : Fin 4) (t : Fˣ) :
    ψ (algebraicCorootElement (StandardRootSystem.typeF4SimpleRootIndex i) t) =
      algebraicCorootElement (StandardRootSystem.typeF4SimpleRootIndex (Fin.revPerm i))
        (exceptionalParameter (StandardRootSystem.typeF4SimpleRootIndex i) t) := by
  rw [exceptional_coroot ψ hψ, exceptionalRootPermutation_simple]

/-- Coordinate Frobenius agrees with finite split Frobenius under the actual embedding. -/
theorem frobeniusEnd_splitEmbedding {k : ℕ} (f : CoefficientField k →+* F)
    (x : SplitGroup k) : frobeniusEnd (splitEmbedding f x) =
      splitEmbedding f (splitFrobeniusEnd k x) := by
  have h : (frobeniusEnd (F := F)).comp (splitEmbedding f) =
      (splitEmbedding f).comp (splitFrobeniusEnd k) := by
    apply splitGroup_hom_ext
    intro r t
    change frobeniusEnd (splitEmbedding f (rootGeneratorInGroup k r t)) = _
    simp only [splitEmbedding_rootGenerator, frobeniusEnd_root, MonoidHom.comp_apply,
      splitFrobeniusEnd, splitFrobenius_rootGenerator, map_pow]
  exact DFunLike.congr_fun h x

end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry
