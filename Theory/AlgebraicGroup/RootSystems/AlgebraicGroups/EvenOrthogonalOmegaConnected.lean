module

public import Theory.AlgebraicGroup.RootSystems.AlgebraicGroups.EvenSpinIsogeny
public import Theory.AlgebraicGroup.Irreducible.Product
public import Theory.AlgebraicGroup.Tori.Power
public import Theory.AlgebraicGroup.Variety.AffineSpace
public import Theory.AlgebraicGroup.CoordinateRing.PolynomialFunction

/-!
# Connectedness of the split even-orthogonal Omega carrier

For a split finite-dimensional quadratic form of hyperbolic rank at least four,
this module proves that the closed image of the even Clifford Spin action is
connected.  The result is characteristic-free and sits below the semisimplicity
and type-D classification layers.

The proof first realizes the norm-minus-one locus in the split hyperbolic space
as an affine quadric.  Standard principal charts are products of a one-dimensional
split torus and affine space; their common point makes their union connected.
Conjugation symmetry in a quadric vector is then expressed by coordinate
polynomials, producing a regular family of general-linear points.  For any fixed
quadric point, the products of its symmetry with the varying symmetry form a
connected family in the Spin image and include the identity.

Finally, algebraic closure normalizes every anisotropic vector to norm minus one.
The split Cartan--Dieudonne/Clifford interfaces from `EvenSpinDerivedRange` give
an even symmetry factorization for every point of the image.  Grouping that word
in pairs puts every factor, and therefore every image point, in the identity
component.  No classification theorem or characteristic restriction is used.
-/

universe u

open scoped BigOperators

namespace Theory.AlgebraicGroup

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

variable {k V : Type u} [Field k] [IsAlgClosed k]
variable [AddCommGroup V] [Module k V] [FiniteDimensional k V]
variable {Q : QuadraticForm k V}

private abbrev SplitUnitQuadricCoordinates (r : Nat) :=
  ULift.{u} (Fin r) ⊕ ULift.{u} (Fin r)

private noncomputable def splitUnitQuadricPolynomial (r : Nat) :
    MvPolynomial (SplitUnitQuadricCoordinates r) k :=
  (∑ i : Fin r,
      MvPolynomial.X (Sum.inl (ULift.up i)) *
        MvPolynomial.X (Sum.inr (ULift.up i))) + 1

private noncomputable def splitUnitQuadric (r : Nat) : Variety k where
  Coordinates := SplitUnitQuadricCoordinates r
  finiteCoordinates := inferInstance
  equations := {splitUnitQuadricPolynomial r}

private lemma eval_splitUnitQuadricPolynomial (r : Nat)
    (x : SplitUnitQuadricCoordinates r → k) :
    evalPolynomial x (splitUnitQuadricPolynomial r) =
      (∑ i : Fin r,
        x (Sum.inl (ULift.up i)) * x (Sum.inr (ULift.up i))) + 1 := by
  rw [splitUnitQuadricPolynomial]
  rw [show evalPolynomial x
      ((∑ i : Fin r, MvPolynomial.X (Sum.inl (ULift.up i)) *
        MvPolynomial.X (Sum.inr (ULift.up i))) + 1) =
      evalPolynomial x
        (∑ i : Fin r, MvPolynomial.X (Sum.inl (ULift.up i)) *
          MvPolynomial.X (Sum.inr (ULift.up i))) + evalPolynomial x 1 by
    simp [evalPolynomial]]
  rw [evalPolynomial_sum]
  simp [evalPolynomial]

private def splitUnitQuadricHyperbolicPoint (r : Nat)
    (x : Variety.Point (splitUnitQuadric (k := k) r)) :
    HyperbolicSpace k r :=
  (fun i => x.val (Sum.inl (ULift.up i)),
    fun i => x.val (Sum.inr (ULift.up i)))

private lemma splitUnitQuadricHyperbolicPoint_norm (r : Nat)
    (x : Variety.Point (splitUnitQuadric (k := k) r)) :
    hyperbolicForm r (splitUnitQuadricHyperbolicPoint r x) = -1 := by
  have hx := x.isZero (splitUnitQuadricPolynomial r) (Set.mem_singleton _)
  have hx' :
      (∑ i : Fin r, x.val (Sum.inl (ULift.up i)) *
        x.val (Sum.inr (ULift.up i))) + 1 = 0 :=
    (eval_splitUnitQuadricPolynomial r x.val).symm.trans hx
  rw [hyperbolicForm_apply]
  dsimp [splitUnitQuadricHyperbolicPoint]
  linear_combination hx'

private def splitUnitQuadricVector (s : SplitQuadraticForm Q)
    (x : Variety.Point (splitUnitQuadric (k := k) s.rank)) : V :=
  s.isometry.symm (splitUnitQuadricHyperbolicPoint s.rank x)

private lemma splitUnitQuadricVector_norm (s : SplitQuadraticForm Q)
    (x : Variety.Point (splitUnitQuadric (k := k) s.rank)) :
    Q (splitUnitQuadricVector s x) = -1 := by
  rw [splitUnitQuadricVector, ← s.isometry.map_app]
  simp only [QuadraticMap.IsometryEquiv.apply_symm_apply]
  exact splitUnitQuadricHyperbolicPoint_norm s.rank x

private noncomputable def splitUnitQuadricChartPoint (r : Nat) (q : Fin r)
    (z : Variety.Point
      (Variety.prod (dVariety k 1)
        (affineSpaceVariety k (SplitUnitQuadricCoordinates r)))) :
    Variety.Point (splitUnitQuadric (k := k) r) := by
  let t := (Variety.prodPointEquiv _ _ z).1
  let y := (Variety.prodPointEquiv _ _ z).2
  let a0 : k := (-1 - ∑ i : Fin r,
      if i = q then 0 else
        y.val (Sum.inl (ULift.up i)) * y.val (Sum.inr (ULift.up i))) *
        dPointEntryInv 1 t 0
  let p : SplitUnitQuadricCoordinates r → k
    | Sum.inl i => if i.down = q then a0 else y.val (Sum.inl i)
    | Sum.inr i => if i.down = q then dPointEntry 1 t 0 else y.val (Sum.inr i)
  refine ⟨p, ?_⟩
  intro f hf
  have hf' : f = splitUnitQuadricPolynomial r := Set.mem_singleton_iff.mp hf
  subst f
  refine (eval_splitUnitQuadricPolynomial r p).trans ?_
  simp only [p]
  rw [show (∑ i : Fin r,
      (if i = q then a0 else y.val (Sum.inl (ULift.up i))) *
        (if i = q then dPointEntry 1 t 0 else y.val (Sum.inr (ULift.up i)))) =
      a0 * dPointEntry 1 t 0 +
        ∑ i : Fin r, if i = q then 0 else
          y.val (Sum.inl (ULift.up i)) * y.val (Sum.inr (ULift.up i)) by
    calc
      _ = ∑ i : Fin r, ((if i = q then a0 * dPointEntry 1 t 0 else 0) +
            (if i = q then 0 else
              y.val (Sum.inl (ULift.up i)) * y.val (Sum.inr (ULift.up i)))) := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : i = q <;> simp [hi]
      _ = _ := by rw [Finset.sum_add_distrib]; simp]
  dsimp only [a0]
  rw [mul_assoc, mul_comm (dPointEntryInv 1 t 0) (dPointEntry 1 t 0),
    dPoint_entry_mul_inv]
  ring

private noncomputable def splitUnitQuadricChart (r : Nat) (q : Fin r) :
    Variety.Morphism
      (Variety.prod (dVariety k 1)
        (affineSpaceVariety k (SplitUnitQuadricCoordinates r)))
      (splitUnitQuadric (k := k) r) where
  toFun := splitUnitQuadricChartPoint r q
  regular := by
    intro c
    let tailTerm : Fin r →
        MvPolynomial
          ((dVariety k 1).Coordinates ⊕
            (affineSpaceVariety k (SplitUnitQuadricCoordinates r)).Coordinates) k :=
      fun i => if i = q then 0 else
        MvPolynomial.X (Sum.inr (Sum.inl (ULift.up i))) *
          MvPolynomial.X (Sum.inr (Sum.inr (ULift.up i)))
    let a0 := (-1 - ∑ i, tailTerm i) *
      MvPolynomial.X (Sum.inl (Sum.inr (ULift.up (0 : Fin 1))))
    cases c with
    | inl i =>
        refine ⟨if i.down = q then a0 else
          MvPolynomial.X (Sum.inr (Sum.inl i)), ?_⟩
        intro z
        dsimp [splitUnitQuadricChartPoint]
        split_ifs with hi
        · have hi' : i = ULift.up q := by
            apply ULift.ext
            exact hi
          subst i
          change
            (-1 - ∑ j : Fin r, if j = q then 0 else
              z.val (Sum.inr (Sum.inl (ULift.up j))) *
                z.val (Sum.inr (Sum.inr (ULift.up j)))) *
                z.val (Sum.inl (Sum.inr (ULift.up (0 : Fin 1)))) =
              evalPolynomial z.val a0
          symm
          dsimp only [a0]
          rw [evalPolynomial_mul]
          rw [show evalPolynomial z.val (-1 - ∑ j : Fin r, tailTerm j) =
              -1 - evalPolynomial z.val (∑ j : Fin r, tailTerm j) by
            simp [evalPolynomial]]
          simp only [evalPolynomial_X]
          apply congrArg (fun w : k =>
            w * z.val (Sum.inl (Sum.inr (ULift.up (0 : Fin 1)))))
          apply congrArg (fun w : k => -1 - w)
          rw [evalPolynomial_sum]
          apply Finset.sum_congr rfl
          intro j _
          by_cases hj : j = q <;> simp [tailTerm, hj, evalPolynomial]
        · simp [evalPolynomial, Variety.prodPointEquiv]
    | inr i =>
        refine ⟨if i.down = q then
          MvPolynomial.X (Sum.inl (Sum.inl (ULift.up (0 : Fin 1))))
          else MvPolynomial.X (Sum.inr (Sum.inr i)), ?_⟩
        intro z
        dsimp [splitUnitQuadricChartPoint]
        split_ifs with hi
        · have hi' : i = ULift.up q := by
            apply ULift.ext
            exact hi
          subst i
          simp [dPointEntry, evalPolynomial, Variety.prodPointEquiv]
        · simp [evalPolynomial, Variety.prodPointEquiv]

private lemma splitUnitQuadricChart_range_iff (r : Nat) (q : Fin r)
    (x : Variety.Point (splitUnitQuadric (k := k) r)) :
    x ∈ Set.range (splitUnitQuadricChart r q).toFun ↔
      x.val (Sum.inr (ULift.up q)) ≠ 0 := by
  constructor
  · rintro ⟨z, rfl⟩
    let t := (Variety.prodPointEquiv _ _ z).1
    change (splitUnitQuadricChartPoint r q z).val
      (Sum.inr (ULift.up q)) ≠ 0
    dsimp only [splitUnitQuadricChartPoint]
    simp only [if_pos]
    change ((dPointEquiv 1
      ((Variety.prodPointEquiv _ _ z).1) 0 : kˣ) : k) ≠ 0
    exact Units.ne_zero _
  · intro hxq
    let bq : k := x.val (Sum.inr (ULift.up q))
    let tq : Variety.Point (dVariety k 1) :=
      (dPointEquiv 1).symm (fun _ => Units.mk0 bq hxq)
    let y : Variety.Point (affineSpaceVariety k (SplitUnitQuadricCoordinates r)) :=
      affineSpacePoint x.val
    let z : Variety.Point
        (Variety.prod (dVariety k 1)
          (affineSpaceVariety k (SplitUnitQuadricCoordinates r))) :=
      (Variety.prodPointEquiv _ _).symm (tq, y)
    refine ⟨z, ?_⟩
    have hx := x.isZero (splitUnitQuadricPolynomial r) (Set.mem_singleton _)
    have hx' :
        (∑ i : Fin r, x.val (Sum.inl (ULift.up i)) *
          x.val (Sum.inr (ULift.up i))) + 1 = 0 :=
      (eval_splitUnitQuadricPolynomial r x.val).symm.trans hx
    let tail : k := ∑ i : Fin r, if i = q then 0 else
      x.val (Sum.inl (ULift.up i)) * x.val (Sum.inr (ULift.up i))
    have hsum :
        (∑ i : Fin r, x.val (Sum.inl (ULift.up i)) *
          x.val (Sum.inr (ULift.up i))) =
          x.val (Sum.inl (ULift.up q)) * bq + tail := by
      calc
        _ = ∑ i : Fin r,
            ((if i = q then
                x.val (Sum.inl (ULift.up q)) * bq else 0) +
              (if i = q then 0 else
                x.val (Sum.inl (ULift.up i)) *
                  x.val (Sum.inr (ULift.up i)))) := by
          apply Finset.sum_congr rfl
          intro i _
          by_cases hi : i = q <;> simp [hi, bq]
        _ = _ := by rw [Finset.sum_add_distrib]; simp [tail]
    have haq :
        x.val (Sum.inl (ULift.up q)) = (-1 - tail) * bq⁻¹ := by
      field_simp [bq, hxq]
      rw [hsum] at hx'
      linear_combination hx'
    apply Variety.Point.ext
    funext c
    change (splitUnitQuadricChartPoint r q z).val c = x.val c
    cases c with
    | inl i =>
        by_cases hi : i.down = q
        · have hi' : i = ULift.up q := by
            apply ULift.ext
            exact hi
          subst i
          dsimp only [splitUnitQuadricChartPoint]
          simp only [if_pos, z, Equiv.apply_symm_apply, y, tq,
            dPointEntryInv, dPointEquiv_symm_val_inr]
          change (-1 - ∑ j : Fin r, if j = q then 0 else
              x.val (Sum.inl (ULift.up j)) * x.val (Sum.inr (ULift.up j))) *
              bq⁻¹ = x.val (Sum.inl (ULift.up q))
          simpa only [tail] using haq.symm
        · dsimp only [splitUnitQuadricChartPoint]
          simp only [hi, z, Equiv.apply_symm_apply, y]
          change (affineSpacePoint x.val).val (Sum.inl i) = x.val (Sum.inl i)
          rfl
    | inr i =>
        by_cases hi : i.down = q
        · have hi' : i = ULift.up q := by
            apply ULift.ext
            exact hi
          subst i
          dsimp only [splitUnitQuadricChartPoint]
          simp only [if_pos, z, Equiv.apply_symm_apply, tq,
            dPointEntry, dPointEquiv_symm_val_inl]
          change bq = x.val (Sum.inr (ULift.up q))
          rfl
        · dsimp only [splitUnitQuadricChartPoint]
          simp only [hi, z, Equiv.apply_symm_apply, y]
          change (affineSpacePoint x.val).val (Sum.inr i) = x.val (Sum.inr i)
          rfl

private theorem splitUnitQuadricChart_range_isConnected (r : Nat) (q : Fin r) :
    IsConnected (Set.range (splitUnitQuadricChart (k := k) r q).toFun) := by
  have hd : IsIrreducible
      (Set.univ : Set (Variety.Point (dVariety k 1))) :=
    connectedAlgebraicGroup_irreducible (dVariety k 1) (dVariety_isConnected 1)
  letI : Nonempty (Variety.Point
      (affineSpaceVariety k (SplitUnitQuadricCoordinates r))) :=
    ⟨affineSpacePoint (fun _ => 0)⟩
  have ha : IsIrreducible
      (Set.univ : Set (Variety.Point
        (affineSpaceVariety k (SplitUnitQuadricCoordinates r)))) := by
    apply isIrreducible_univ_of_prime_vanishingIdeal
    rw [affineSpaceVariety_vanishingIdeal_eq_bot]
    exact Ideal.isPrime_bot
  have hp := prodSet_irreducible_of_irreducible hd ha
  have hprod : Variety.prodSet
      (Set.univ : Set (Variety.Point (dVariety k 1)))
      (Set.univ : Set (Variety.Point
        (affineSpaceVariety k (SplitUnitQuadricCoordinates r)))) =
      (Set.univ : Set (Variety.Point
        (Variety.prod (dVariety k 1)
          (affineSpaceVariety k (SplitUnitQuadricCoordinates r))))) := by
    ext z
    simp [Variety.prodSet]
  rw [hprod] at hp
  rw [← Set.image_univ]
  exact hp.isConnected.image _ (splitUnitQuadricChart r q).continuous.continuousOn

private noncomputable def splitUnitQuadricCommonPoint (r : Nat) [NeZero r] :
    Variety.Point (splitUnitQuadric (k := k) r) := by
  let p : SplitUnitQuadricCoordinates r → k
    | Sum.inl i => if i.down = 0 then -1 else 0
    | Sum.inr _ => 1
  refine ⟨p, ?_⟩
  intro f hf
  have hf' : f = splitUnitQuadricPolynomial r := Set.mem_singleton_iff.mp hf
  subst f
  refine (eval_splitUnitQuadricPolynomial r p).trans ?_
  simp [p]

private lemma splitUnitQuadricCommonPoint_second (r : Nat) [NeZero r]
    (q : Fin r) :
    (splitUnitQuadricCommonPoint (k := k) r).val
      (Sum.inr (ULift.up q)) = 1 := by
  rfl

private theorem splitUnitQuadric_isConnected (r : Nat) [NeZero r] :
    IsConnected (Set.univ : Set (Variety.Point (splitUnitQuadric (k := k) r))) := by
  let U : Fin r → Set (Variety.Point (splitUnitQuadric (k := k) r)) :=
    fun q => Set.range (splitUnitQuadricChart r q).toFun
  have hcover : (⋃ q, U q) = Set.univ := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    have hx := x.isZero (splitUnitQuadricPolynomial r) (Set.mem_singleton _)
    have hx' :
        (∑ i : Fin r, x.val (Sum.inl (ULift.up i)) *
          x.val (Sum.inr (ULift.up i))) + 1 = 0 :=
      (eval_splitUnitQuadricPolynomial r x.val).symm.trans hx
    have hnonzero : ∃ q : Fin r, x.val (Sum.inr (ULift.up q)) ≠ 0 := by
      by_contra h
      push Not at h
      simp [h] at hx'
    obtain ⟨q, hq⟩ := hnonzero
    exact ⟨q, (splitUnitQuadricChart_range_iff r q x).2 hq⟩
  let w := splitUnitQuadricCommonPoint (k := k) r
  have hw (q : Fin r) : w ∈ U q := by
    apply (splitUnitQuadricChart_range_iff r q w).2
    rw [splitUnitQuadricCommonPoint_second]
    exact one_ne_zero
  rw [← hcover]
  refine ⟨⟨w, Set.mem_iUnion.2 ⟨(0 : Fin r), hw 0⟩⟩, ?_⟩
  apply isPreconnected_iUnion
  · exact ⟨w, Set.mem_iInter.2 hw⟩
  · intro q
    exact (splitUnitQuadricChart_range_isConnected r q).isPreconnected

private noncomputable def splitUnitQuadricLeftCoordinateVector
    (s : SplitQuadraticForm Q) (j : Fin s.rank) : V :=
  s.isometry.symm (Pi.single j 1, 0)

private noncomputable def splitUnitQuadricRightCoordinateVector
    (s : SplitQuadraticForm Q) (j : Fin s.rank) : V :=
  s.isometry.symm (0, Pi.single j 1)

private lemma splitUnitQuadricVector_eq_sum
    (s : SplitQuadraticForm Q)
    (x : Variety.Point (splitUnitQuadric (k := k) s.rank)) :
    splitUnitQuadricVector s x =
      (∑ j : Fin s.rank, x.val (Sum.inl (ULift.up j)) •
        splitUnitQuadricLeftCoordinateVector s j) +
      ∑ j : Fin s.rank, x.val (Sum.inr (ULift.up j)) •
        splitUnitQuadricRightCoordinateVector s j := by
  change s.isometry.symm
      (splitUnitQuadricHyperbolicPoint s.rank x) = _
  simp only [splitUnitQuadricLeftCoordinateVector,
    splitUnitQuadricRightCoordinateVector, ← map_smul, ← map_sum, ← map_add]
  apply congrArg s.isometry.symm
  apply Prod.ext
  · simp only [splitUnitQuadricHyperbolicPoint, Prod.fst_add, Prod.fst_sum,
      Prod.smul_fst, smul_zero, Finset.sum_const_zero, add_zero]
    simpa only [← Pi.single_smul, smul_eq_mul, mul_one] using
      (Finset.univ_sum_single
        (fun j : Fin s.rank => x.val (Sum.inl (ULift.up j)))).symm
  · simp only [splitUnitQuadricHyperbolicPoint, Prod.snd_add, Prod.snd_sum,
      Prod.smul_snd, smul_zero, Finset.sum_const_zero, zero_add]
    simpa only [← Pi.single_smul, smul_eq_mul, mul_one] using
      (Finset.univ_sum_single
        (fun j : Fin s.rank => x.val (Sum.inr (ULift.up j)))).symm

private noncomputable def splitUnitQuadricVectorCoordinatePolynomial
    (s : SplitQuadraticForm Q) (i : Fin (Module.finrank k V)) :
    MvPolynomial (SplitUnitQuadricCoordinates s.rank) k :=
  (∑ j : Fin s.rank,
    MvPolynomial.C ((Module.finBasis k V).repr
      (splitUnitQuadricLeftCoordinateVector s j) i) *
        MvPolynomial.X (Sum.inl (ULift.up j))) +
  ∑ j : Fin s.rank,
    MvPolynomial.C ((Module.finBasis k V).repr
      (splitUnitQuadricRightCoordinateVector s j) i) *
        MvPolynomial.X (Sum.inr (ULift.up j))

private lemma eval_splitUnitQuadricVectorCoordinatePolynomial_raw
    (s : SplitQuadraticForm Q) (i : Fin (Module.finrank k V))
    (x : SplitUnitQuadricCoordinates s.rank → k) :
    evalPolynomial x (splitUnitQuadricVectorCoordinatePolynomial s i) =
      (∑ j : Fin s.rank,
        (Module.finBasis k V).repr
            (splitUnitQuadricLeftCoordinateVector s j) i *
          x (Sum.inl (ULift.up j))) +
      ∑ j : Fin s.rank,
        (Module.finBasis k V).repr
            (splitUnitQuadricRightCoordinateVector s j) i *
          x (Sum.inr (ULift.up j)) := by
  rw [splitUnitQuadricVectorCoordinatePolynomial]
  rw [show evalPolynomial x
        ((∑ j : Fin s.rank,
            MvPolynomial.C ((Module.finBasis k V).repr
              (splitUnitQuadricLeftCoordinateVector s j) i) *
              MvPolynomial.X (Sum.inl (ULift.up j))) +
          ∑ j : Fin s.rank,
            MvPolynomial.C ((Module.finBasis k V).repr
              (splitUnitQuadricRightCoordinateVector s j) i) *
              MvPolynomial.X (Sum.inr (ULift.up j))) =
        evalPolynomial x
          (∑ j : Fin s.rank,
            MvPolynomial.C ((Module.finBasis k V).repr
              (splitUnitQuadricLeftCoordinateVector s j) i) *
              MvPolynomial.X (Sum.inl (ULift.up j))) +
        evalPolynomial x
          (∑ j : Fin s.rank,
            MvPolynomial.C ((Module.finBasis k V).repr
              (splitUnitQuadricRightCoordinateVector s j) i) *
              MvPolynomial.X (Sum.inr (ULift.up j))) by
      simp [evalPolynomial]]
  rw [evalPolynomial_sum, evalPolynomial_sum]
  simp [evalPolynomial]

private lemma eval_splitUnitQuadricVectorCoordinatePolynomial
    (s : SplitQuadraticForm Q) (i : Fin (Module.finrank k V))
    (x : Variety.Point (splitUnitQuadric (k := k) s.rank)) :
    evalPolynomial x.val (splitUnitQuadricVectorCoordinatePolynomial s i) =
      (Module.finBasis k V).repr (splitUnitQuadricVector s x) i := by
  calc
    _ = (∑ j : Fin s.rank,
          (Module.finBasis k V).repr
              (splitUnitQuadricLeftCoordinateVector s j) i *
            x.val (Sum.inl (ULift.up j))) +
        ∑ j : Fin s.rank,
          (Module.finBasis k V).repr
              (splitUnitQuadricRightCoordinateVector s j) i *
            x.val (Sum.inr (ULift.up j)) :=
      eval_splitUnitQuadricVectorCoordinatePolynomial_raw s i x.val
    _ = (∑ j : Fin s.rank,
          x.val (Sum.inl (ULift.up j)) *
            (Module.finBasis k V).repr
              (splitUnitQuadricLeftCoordinateVector s j) i) +
        ∑ j : Fin s.rank,
          x.val (Sum.inr (ULift.up j)) *
            (Module.finBasis k V).repr
              (splitUnitQuadricRightCoordinateVector s j) i := by
      apply congrArg₂ (· + ·) <;>
        apply Finset.sum_congr rfl <;> intro j _ <;> ring
    _ = _ := by
      rw [splitUnitQuadricVector_eq_sum, map_add, map_sum, map_sum]
      simp only [map_smul]
      rw [Finsupp.add_apply]
      rw [show (∑ j : Fin s.rank,
          x.val (Sum.inl (ULift.up j)) •
            (Module.finBasis k V).repr
              (splitUnitQuadricLeftCoordinateVector s j)) i =
          ∑ j : Fin s.rank,
            (x.val (Sum.inl (ULift.up j)) •
              (Module.finBasis k V).repr
                (splitUnitQuadricLeftCoordinateVector s j)) i by
        have h := congrFun
          (Finsupp.coe_finsetSum (Finset.univ : Finset (Fin s.rank))
            (fun j => x.val (Sum.inl (ULift.up j)) •
              (Module.finBasis k V).repr
                (splitUnitQuadricLeftCoordinateVector s j))) i
        simpa only [Finset.sum_apply] using h]
      rw [show (∑ j : Fin s.rank,
          x.val (Sum.inr (ULift.up j)) •
            (Module.finBasis k V).repr
              (splitUnitQuadricRightCoordinateVector s j)) i =
          ∑ j : Fin s.rank,
            (x.val (Sum.inr (ULift.up j)) •
              (Module.finBasis k V).repr
                (splitUnitQuadricRightCoordinateVector s j)) i by
        have h := congrFun
          (Finsupp.coe_finsetSum (Finset.univ : Finset (Fin s.rank))
            (fun j => x.val (Sum.inr (ULift.up j)) •
              (Module.finBasis k V).repr
                (splitUnitQuadricRightCoordinateVector s j))) i
        simpa only [Finset.sum_apply] using h]
      simp only [Finsupp.smul_apply, smul_eq_mul]

private noncomputable def splitUnitQuadricPolarPolynomial
    (s : SplitQuadraticForm Q) (j : Fin (Module.finrank k V)) :
    MvPolynomial (SplitUnitQuadricCoordinates s.rank) k :=
  ∑ i : Fin (Module.finrank k V),
    MvPolynomial.C (QuadraticMap.polar Q ((Module.finBasis k V) i)
      ((Module.finBasis k V) j)) *
        splitUnitQuadricVectorCoordinatePolynomial s i

private lemma eval_splitUnitQuadricPolarPolynomial_raw
    (s : SplitQuadraticForm Q) (j : Fin (Module.finrank k V))
    (x : SplitUnitQuadricCoordinates s.rank → k) :
    evalPolynomial x (splitUnitQuadricPolarPolynomial s j) =
      ∑ i : Fin (Module.finrank k V),
        QuadraticMap.polar Q ((Module.finBasis k V) i)
            ((Module.finBasis k V) j) *
          evalPolynomial x (splitUnitQuadricVectorCoordinatePolynomial s i) := by
  rw [splitUnitQuadricPolarPolynomial]
  rw [evalPolynomial_sum]
  simp [evalPolynomial]

private lemma eval_splitUnitQuadricPolarPolynomial
    (s : SplitQuadraticForm Q) (j : Fin (Module.finrank k V))
    (x : Variety.Point (splitUnitQuadric (k := k) s.rank)) :
    evalPolynomial x.val (splitUnitQuadricPolarPolynomial s j) =
      QuadraticMap.polar Q (splitUnitQuadricVector s x)
        ((Module.finBasis k V) j) := by
  calc
    _ = ∑ i : Fin (Module.finrank k V),
          QuadraticMap.polar Q ((Module.finBasis k V) i)
              ((Module.finBasis k V) j) *
            evalPolynomial x.val
              (splitUnitQuadricVectorCoordinatePolynomial s i) :=
      eval_splitUnitQuadricPolarPolynomial_raw s j x.val
    _ = _ := by
      simp_rw [eval_splitUnitQuadricVectorCoordinatePolynomial]
      conv_rhs => rw [← (Module.finBasis k V).sum_repr (splitUnitQuadricVector s x)]
      change _ = Q.polarBilin
        (∑ i, ((Module.finBasis k V).repr (splitUnitQuadricVector s x)) i •
          (Module.finBasis k V) i) ((Module.finBasis k V) j)
      rw [map_sum]
      rw [LinearMap.sum_apply]
      apply Finset.sum_congr rfl
      intro i hi
      rw [map_smul]
      rw [LinearMap.smul_apply]
      change _ = ((Module.finBasis k V).repr (splitUnitQuadricVector s x)) i *
        QuadraticMap.polar Q ((Module.finBasis k V) i) ((Module.finBasis k V) j)
      ring

private noncomputable def splitUnitQuadricSymmetry
    (s : SplitQuadraticForm Q)
    (x : Variety.Point (splitUnitQuadric (k := k) s.rank)) :
    LinearMap.GeneralLinearGroup k V :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv k V).symm
    (conjugationSymmetry Q (splitUnitQuadricVector s x)
      (by rw [splitUnitQuadricVector_norm]; exact neg_ne_zero.mpr one_ne_zero)).toLinearEquiv

private lemma splitUnitQuadricSymmetry_apply
    (s : SplitQuadraticForm Q)
    (x : Variety.Point (splitUnitQuadric (k := k) s.rank)) (v : V) :
    (splitUnitQuadricSymmetry s x : Module.End k V) v =
      conjugationSymmetry Q (splitUnitQuadricVector s x)
        (by rw [splitUnitQuadricVector_norm]; exact neg_ne_zero.mpr one_ne_zero) v := by
  have h := (LinearMap.GeneralLinearGroup.generalLinearEquiv k V).apply_symm_apply
    (conjugationSymmetry Q (splitUnitQuadricVector s x)
      (by rw [splitUnitQuadricVector_norm]; exact neg_ne_zero.mpr one_ne_zero)).toLinearEquiv
  exact DFunLike.congr_fun h v

private noncomputable def splitUnitQuadricSymmetryMatrixPolynomial
    (s : SplitQuadraticForm Q)
    (i j : Fin (Module.finrank k V)) :
    MvPolynomial (SplitUnitQuadricCoordinates s.rank) k :=
  -(splitUnitQuadricPolarPolynomial s j) *
      splitUnitQuadricVectorCoordinatePolynomial s i -
    MvPolynomial.C ((Module.finBasis k V).repr ((Module.finBasis k V) j) i)

private lemma eval_splitUnitQuadricSymmetryMatrixPolynomial_raw
    (s : SplitQuadraticForm Q) (i j : Fin (Module.finrank k V))
    (x : SplitUnitQuadricCoordinates s.rank → k) :
    evalPolynomial x (splitUnitQuadricSymmetryMatrixPolynomial s i j) =
      -evalPolynomial x (splitUnitQuadricPolarPolynomial s j) *
          evalPolynomial x (splitUnitQuadricVectorCoordinatePolynomial s i) -
        (Module.finBasis k V).repr ((Module.finBasis k V) j) i := by
  rw [splitUnitQuadricSymmetryMatrixPolynomial]
  simp [evalPolynomial]

private lemma eval_splitUnitQuadricSymmetryMatrixPolynomial
    (s : SplitQuadraticForm Q) (i j : Fin (Module.finrank k V))
    (x : Variety.Point (splitUnitQuadric (k := k) s.rank)) :
    evalPolynomial x.val (splitUnitQuadricSymmetryMatrixPolynomial s i j) =
      LinearMap.toMatrix (Module.finBasis k V) (Module.finBasis k V)
        (splitUnitQuadricSymmetry s x : Module.End k V) i j := by
  rw [LinearMap.toMatrix_apply]
  rw [splitUnitQuadricSymmetry_apply]
  rw [conjugationSymmetry_apply, splitUnitQuadricVector_norm]
  simp only [inv_neg, inv_one]
  rw [map_sub, map_smul]
  simp only [Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul]
  calc
    _ = -evalPolynomial x.val (splitUnitQuadricPolarPolynomial s j) *
          evalPolynomial x.val (splitUnitQuadricVectorCoordinatePolynomial s i) -
        (Module.finBasis k V).repr ((Module.finBasis k V) j) i :=
      eval_splitUnitQuadricSymmetryMatrixPolynomial_raw s i j x.val
    _ = _ := by
      rw [eval_splitUnitQuadricPolarPolynomial,
        eval_splitUnitQuadricVectorCoordinatePolynomial]
      ring

private lemma splitUnitQuadricSymmetry_sq
    (s : SplitQuadraticForm Q)
    (x : Variety.Point (splitUnitQuadric (k := k) s.rank)) :
    splitUnitQuadricSymmetry s x * splitUnitQuadricSymmetry s x = 1 := by
  apply Units.ext
  ext v
  change (splitUnitQuadricSymmetry s x : Module.End k V)
      ((splitUnitQuadricSymmetry s x : Module.End k V) v) = v
  rw [splitUnitQuadricSymmetry_apply, splitUnitQuadricSymmetry_apply]
  exact conjugationSymmetry_involutive Q (splitUnitQuadricVector s x) _ v

private lemma splitUnitQuadricSymmetry_inv
    (s : SplitQuadraticForm Q)
    (x : Variety.Point (splitUnitQuadric (k := k) s.rank)) :
    (splitUnitQuadricSymmetry s x)⁻¹ = splitUnitQuadricSymmetry s x := by
  exact (eq_inv_iff_mul_eq_one.mpr (splitUnitQuadricSymmetry_sq s x)).symm

private noncomputable def splitUnitQuadricSymmetryMorphism
    (s : SplitQuadraticForm Q) :
    Variety.Morphism (splitUnitQuadric (k := k) s.rank) (glVarietyOf k V) where
  toFun := fun x => generalLinearRepresentationPoint (Module.finBasis k V)
    (splitUnitQuadricSymmetry s x)
  regular := by
    intro c
    cases c with
    | inl ij =>
        rcases ij with ⟨i, j⟩
        refine ⟨splitUnitQuadricSymmetryMatrixPolynomial s i j, fun x => ?_⟩
        calc
          _ = (Module.finBasis k V).repr
                ((splitUnitQuadricSymmetry s x : Module.End k V)
                  ((Module.finBasis k V) j)) i :=
            generalLinearRepresentationPoint_matrix (Module.finBasis k V)
              (splitUnitQuadricSymmetry s x) i j
          _ = LinearMap.toMatrix (Module.finBasis k V) (Module.finBasis k V)
                (splitUnitQuadricSymmetry s x : Module.End k V) i j := by
            rw [LinearMap.toMatrix_apply]
          _ = _ := (eval_splitUnitQuadricSymmetryMatrixPolynomial s i j x).symm
    | inr q =>
        cases q
        let M : Matrix (Fin (Module.finrank k V)) (Fin (Module.finrank k V))
            (MvPolynomial (SplitUnitQuadricCoordinates s.rank) k) :=
          fun i j => splitUnitQuadricSymmetryMatrixPolynomial s i j
        refine ⟨Matrix.det M, fun x => ?_⟩
        calc
          _ = (LinearMap.toMatrix (Module.finBasis k V) (Module.finBasis k V)
                (splitUnitQuadricSymmetry s x : Module.End k V)).det⁻¹ :=
            generalLinearRepresentationPoint_scalar (Module.finBasis k V)
              (splitUnitQuadricSymmetry s x)
          _ = (LinearMap.toMatrix (Module.finBasis k V) (Module.finBasis k V)
                (((splitUnitQuadricSymmetry s x)⁻¹ :
                  LinearMap.GeneralLinearGroup k V) : Module.End k V)).det :=
            (generalLinear_toMatrix_inv_det (Module.finBasis k V)
              (splitUnitQuadricSymmetry s x)).symm
          _ = (LinearMap.toMatrix (Module.finBasis k V) (Module.finBasis k V)
                (splitUnitQuadricSymmetry s x : Module.End k V)).det := by
            rw [splitUnitQuadricSymmetry_inv]
          _ = evalPolynomial x.val (Matrix.det M) := by
            let ev : MvPolynomial (SplitUnitQuadricCoordinates s.rank) k →+* k :=
              MvPolynomial.eval₂Hom (RingHom.id k) x.val
            change _ = ev (Matrix.det M)
            rw [RingHom.map_det]
            congr 1
            funext i j
            exact (eval_splitUnitQuadricSymmetryMatrixPolynomial s i j x).symm

private lemma splitUnitQuadricSymmetryMorphism_apply
    (s : SplitQuadraticForm Q)
    (x : Variety.Point (splitUnitQuadric (k := k) s.rank)) :
    (splitUnitQuadricSymmetryMorphism s).toFun x =
      generalLinearRepresentationPoint (Module.finBasis k V)
        (splitUnitQuadricSymmetry s x) :=
  rfl

private noncomputable def splitGeneralLinearPointMulEquiv :
    Variety.Point (glVarietyOf k V) ≃*
      LinearMap.GeneralLinearGroup k V := by
  let eGL : GL (Fin (Module.finrank k V)) k ≃*
      LinearMap.GeneralLinearGroup k
        (Fin (Module.finrank k V) → k) :=
    Matrix.GeneralLinearGroup.toLin
  let eLin : LinearMap.GeneralLinearGroup k
      (Fin (Module.finrank k V) → k) ≃*
        LinearMap.GeneralLinearGroup k V :=
    LinearMap.GeneralLinearGroup.congrLinearEquiv
      (Module.finBasis k V).equivFun.symm
  exact (translationGLPointMulEquiv (k := k)
    (Module.finrank k V)).trans (eGL.trans eLin)

private lemma splitGeneralLinearPointMulEquiv_apply
    (x : Variety.Point (glVarietyOf k V)) :
    splitGeneralLinearPointMulEquiv (k := k) (V := V) x =
      glPointEquivOf k V (Module.finBasis k V) x :=
  rfl

private lemma splitGeneralLinearPointMulEquiv_symmetryMorphism
    (s : SplitQuadraticForm Q)
    (x : Variety.Point (splitUnitQuadric (k := k) s.rank)) :
    splitGeneralLinearPointMulEquiv (k := k) (V := V)
        ((splitUnitQuadricSymmetryMorphism s).toFun x) =
      splitUnitQuadricSymmetry s x := by
  rw [splitGeneralLinearPointMulEquiv_apply,
    splitUnitQuadricSymmetryMorphism_apply,
    glPointEquivOf_generalLinearRepresentationPoint]

private noncomputable def splitUnitQuadricAnisotropicVector
    (s : SplitQuadraticForm Q)
    (x : Variety.Point (splitUnitQuadric (k := k) s.rank)) :
    AnisotropicVector Q :=
  ⟨splitUnitQuadricVector s x,
    by rw [splitUnitQuadricVector_norm]; exact neg_ne_zero.mpr one_ne_zero⟩

private lemma splitUnitQuadricSymmetry_linearEquiv
    (s : SplitQuadraticForm Q)
    (x : Variety.Point (splitUnitQuadric (k := k) s.rank)) :
    LinearMap.GeneralLinearGroup.generalLinearEquiv k V
        (splitUnitQuadricSymmetry s x) =
      (conjugationSymmetry Q (splitUnitQuadricVector s x)
        (by
          rw [splitUnitQuadricVector_norm]
          exact neg_ne_zero.mpr one_ne_zero)).toLinearEquiv := by
  exact (LinearMap.GeneralLinearGroup.generalLinearEquiv k V).apply_symm_apply _

private lemma splitUnitQuadricSymmetryPoint_linearEquiv
    (s : SplitQuadraticForm Q)
    (x : Variety.Point (splitUnitQuadric (k := k) s.rank)) :
    (symmetryPoint (splitUnitQuadricAnisotropicVector s x)).1 =
      LinearMap.GeneralLinearGroup.generalLinearEquiv k V
        (splitUnitQuadricSymmetry s x) := by
  apply LinearEquiv.ext
  intro v
  rw [symmetryPoint_apply, splitUnitQuadricSymmetry_linearEquiv]
  rfl

private lemma splitUnitQuadricSymmetry_pair_mem_image
    (s : SplitQuadraticForm Q) (hrank : 4 ≤ s.rank)
    (x y : Variety.Point (splitUnitQuadric (k := k) s.rank)) :
    (splitUnitQuadricSymmetryMorphism s).toFun x *
        (splitUnitQuadricSymmetryMorphism s).toFun y ∈
      (evenSpinActionImageClosedSubgroup Q s).toSubgroup := by
  rw [evenSpinActionImageClosedSubgroup_commutator_carrier Q s hrank]
  let a := splitUnitQuadricAnisotropicVector s x
  let b := splitUnitQuadricAnisotropicVector s y
  refine ⟨⟨symmetryPoint a * symmetryPoint b,
    symmetryPair_mem_commutator s a b⟩, ?_⟩
  rw [← splitGeneralLinearPointMulEquiv_apply]
  rw [map_mul]
  rw [splitGeneralLinearPointMulEquiv_apply,
    splitGeneralLinearPointMulEquiv_apply,
    splitUnitQuadricSymmetryMorphism_apply,
    splitUnitQuadricSymmetryMorphism_apply,
    glPointEquivOf_generalLinearRepresentationPoint,
    glPointEquivOf_generalLinearRepresentationPoint]
  change (symmetryPoint a).1 * (symmetryPoint b).1 = _
  rw [splitUnitQuadricSymmetryPoint_linearEquiv,
    splitUnitQuadricSymmetryPoint_linearEquiv]
  exact ((LinearMap.GeneralLinearGroup.generalLinearEquiv k V).map_mul
    (splitUnitQuadricSymmetry s x) (splitUnitQuadricSymmetry s y)).symm

private def morphismCodRestrictClosedSubgroup
    {X G : Variety k} [AlgebraicGroup G]
    (f : Variety.Morphism X G) (H : ClosedSubgroup G)
    (hmap : ∀ x, f.toFun x ∈ H.toSubgroup) :
    Variety.Morphism X H.carrierVariety where
  toFun := fun x => H.pointEquiv.symm ⟨f.toFun x, hmap x⟩
  regular := by
    intro i
    rcases f.regular i with ⟨p, hp⟩
    refine ⟨p, ?_⟩
    intro x
    change (H.pointEquiv (H.pointEquiv.symm ⟨f.toFun x, hmap x⟩)).val.val i =
      evalPolynomial x.val p
    rw [H.pointEquiv.apply_symm_apply]
    exact hp x

omit [IsAlgClosed k] in
private lemma morphismCodRestrictClosedSubgroup_inclusion
    {X G : Variety k} [AlgebraicGroup G]
    (f : Variety.Morphism X G) (H : ClosedSubgroup G)
    (hmap : ∀ x, f.toFun x ∈ H.toSubgroup) (x : Variety.Point X) :
    H.inclusion.onPoints
        ((morphismCodRestrictClosedSubgroup f H hmap).toFun x) =
      f.toFun x := by
  change (H.pointEquiv (H.pointEquiv.symm ⟨f.toFun x, hmap x⟩)).val = f.toFun x
  rw [H.pointEquiv.apply_symm_apply]

private noncomputable def splitUnitQuadricSymmetryRightMorphism
    (s : SplitQuadraticForm Q) (hrank : 4 ≤ s.rank)
    (y : Variety.Point (splitUnitQuadric (k := k) s.rank)) :
    Variety.Morphism (splitUnitQuadric (k := k) s.rank)
      (evenSpinActionImageClosedSubgroup Q s).carrierVariety := by
  let f := (AlgebraicGroup.rightMulMorphism (glVarietyOf k V)
    ((splitUnitQuadricSymmetryMorphism s).toFun y)).comp
      (splitUnitQuadricSymmetryMorphism s)
  apply morphismCodRestrictClosedSubgroup f
    (evenSpinActionImageClosedSubgroup Q s)
  intro x
  simpa [f, Variety.Morphism.comp, AlgebraicGroup.rightMulMorphism_apply] using
    splitUnitQuadricSymmetry_pair_mem_image s hrank x y

private lemma splitUnitQuadricSymmetryRightMorphism_inclusion
    (s : SplitQuadraticForm Q) (hrank : 4 ≤ s.rank)
    (x y : Variety.Point (splitUnitQuadric (k := k) s.rank)) :
    (evenSpinActionImageClosedSubgroup Q s).inclusion.onPoints
        ((splitUnitQuadricSymmetryRightMorphism s hrank y).toFun x) =
      (splitUnitQuadricSymmetryMorphism s).toFun x *
        (splitUnitQuadricSymmetryMorphism s).toFun y := by
  unfold splitUnitQuadricSymmetryRightMorphism
  change _ = ((AlgebraicGroup.rightMulMorphism (glVarietyOf k V)
    ((splitUnitQuadricSymmetryMorphism s).toFun y)).comp
      (splitUnitQuadricSymmetryMorphism s)).toFun x
  rw [morphismCodRestrictClosedSubgroup_inclusion]

private lemma splitUnitQuadricSymmetryRightMorphism_self
    (s : SplitQuadraticForm Q) (hrank : 4 ≤ s.rank)
    (y : Variety.Point (splitUnitQuadric (k := k) s.rank)) :
    (splitUnitQuadricSymmetryRightMorphism s hrank y).toFun y = 1 := by
  apply (evenSpinActionImageClosedSubgroup Q s).inclusion_injective
  rw [splitUnitQuadricSymmetryRightMorphism_inclusion]
  apply (splitGeneralLinearPointMulEquiv (k := k) (V := V)).injective
  rw [map_mul]
  rw [splitGeneralLinearPointMulEquiv_symmetryMorphism]
  exact (splitUnitQuadricSymmetry_sq s y).trans
    ((splitGeneralLinearPointMulEquiv (k := k) (V := V)).map_one.symm)

private lemma splitUnitQuadricSymmetry_pair_mem_identityComponent
    (s : SplitQuadraticForm Q) (hrank : 4 ≤ s.rank)
    (x y : Variety.Point (splitUnitQuadric (k := k) s.rank)) :
    (splitUnitQuadricSymmetryRightMorphism s hrank y).toFun x ∈
      AlgebraicGroup.identityComponent
        (evenSpinActionImageClosedSubgroup Q s).carrierVariety := by
  let f := splitUnitQuadricSymmetryRightMorphism s hrank y
  letI : NeZero s.rank := ⟨by omega⟩
  letI : ConnectedSpace
      (Variety.Point (splitUnitQuadric (k := k) s.rank)) :=
    connectedSpace_iff_univ.mpr (splitUnitQuadric_isConnected (k := k) s.rank)
  have hrange : IsConnected (Set.range f.toFun) :=
    isConnected_range f.continuous
  have hone : (1 : Variety.Point
      (evenSpinActionImageClosedSubgroup Q s).carrierVariety) ∈
      Set.range f.toFun := by
    refine ⟨y, ?_⟩
    exact splitUnitQuadricSymmetryRightMorphism_self s hrank y
  exact hrange.subset_connectedComponent hone ⟨x, rfl⟩

private noncomputable def omegaNormalizingScalar
    (a : AnisotropicVector Q) : k :=
  Classical.choose (IsAlgClosed.exists_eq_mul_self (-(Q a.1)⁻¹))

omit [FiniteDimensional k V] in
private lemma omegaNormalizingScalar_spec (a : AnisotropicVector Q) :
    -(Q a.1)⁻¹ = omegaNormalizingScalar a * omegaNormalizingScalar a :=
  Classical.choose_spec (IsAlgClosed.exists_eq_mul_self (-(Q a.1)⁻¹))

omit [FiniteDimensional k V] in
private lemma omegaNormalizingScalar_ne_zero (a : AnisotropicVector Q) :
    omegaNormalizingScalar a ≠ 0 := by
  intro h
  have hzero : -(Q a.1)⁻¹ = 0 := by
    rw [omegaNormalizingScalar_spec, h, zero_mul]
  exact (neg_ne_zero.mpr (inv_ne_zero a.2)) hzero

private noncomputable def omegaNormalizedVector
    (a : AnisotropicVector Q) : V :=
  omegaNormalizingScalar a • a.1

omit [FiniteDimensional k V] in
private lemma omegaNormalizedVector_norm (a : AnisotropicVector Q) :
    Q (omegaNormalizedVector a) = -1 := by
  rw [omegaNormalizedVector, QuadraticMap.map_smul]
  simp only [smul_eq_mul]
  rw [← omegaNormalizingScalar_spec a, neg_mul, inv_mul_cancel₀ a.2]

omit [IsAlgClosed k] [FiniteDimensional k V] in
private lemma omega_conjugationSymmetry_smul
    (a : AnisotropicVector Q) (c : k) (hc : c ≠ 0) (v : V) :
    conjugationSymmetry Q (c • a.1)
        (by simp [QuadraticMap.map_smul, hc, a.2]) v =
      conjugationSymmetry Q a.1 a.2 v := by
  rw [conjugationSymmetry_apply, conjugationSymmetry_apply]
  simp only [QuadraticMap.map_smul, QuadraticMap.polar_smul_left, smul_smul]
  apply congrArg (fun z : k => z • a.1 - v)
  field_simp [hc, a.2]
  ring

private noncomputable def splitUnitQuadricPointOfNorm
    (s : SplitQuadraticForm Q) (v : V) (hv : Q v = -1) :
    Variety.Point (splitUnitQuadric (k := k) s.rank) := by
  let w := s.isometry v
  refine ⟨fun c => match c with
    | Sum.inl i => w.1 i.down
    | Sum.inr i => w.2 i.down, ?_⟩
  intro f hf
  have hf' : f = splitUnitQuadricPolynomial s.rank :=
    Set.mem_singleton_iff.mp hf
  subst f
  unfold splitUnitQuadric
  rw [eval_splitUnitQuadricPolynomial]
  simp only
  rw [← hyperbolicForm_apply]
  dsimp only [w]
  rw [s.isometry.map_app, hv]
  ring

private lemma splitUnitQuadricVector_pointOfNorm
    (s : SplitQuadraticForm Q) (v : V) (hv : Q v = -1) :
    splitUnitQuadricVector s (splitUnitQuadricPointOfNorm s v hv) = v := by
  have heq : splitUnitQuadricHyperbolicPoint s.rank
      (splitUnitQuadricPointOfNorm s v hv) = s.isometry v := by
    unfold splitUnitQuadricHyperbolicPoint splitUnitQuadricPointOfNorm
    apply Prod.ext <;> funext i <;> rfl
  calc
    _ = s.isometry.symm (s.isometry v) := congrArg s.isometry.symm heq
    _ = v := s.isometry.symm_apply_apply v

private noncomputable def omegaNormalizedQuadricPoint
    (s : SplitQuadraticForm Q) (a : AnisotropicVector Q) :
    Variety.Point (splitUnitQuadric (k := k) s.rank) :=
  splitUnitQuadricPointOfNorm s (omegaNormalizedVector a)
    (omegaNormalizedVector_norm a)

private lemma omegaNormalizedQuadricPoint_symmetryPoint
    (s : SplitQuadraticForm Q) (a : AnisotropicVector Q) :
    symmetryPoint (splitUnitQuadricAnisotropicVector s
        (omegaNormalizedQuadricPoint s a)) = symmetryPoint a := by
  have ha : splitUnitQuadricAnisotropicVector s
      (omegaNormalizedQuadricPoint s a) =
        (⟨omegaNormalizedVector a,
          by rw [omegaNormalizedVector_norm]; exact neg_ne_zero.mpr one_ne_zero⟩ :
            AnisotropicVector Q) := by
    apply Subtype.ext
    exact splitUnitQuadricVector_pointOfNorm s (omegaNormalizedVector a)
      (omegaNormalizedVector_norm a)
  rw [ha]
  apply Subtype.ext
  ext v
  rw [symmetryPoint_apply, symmetryPoint_apply]
  exact omega_conjugationSymmetry_smul a (omegaNormalizingScalar a)
    (omegaNormalizingScalar_ne_zero a) v

private lemma splitUnitQuadricSymmetry_pair_linear_points
    (s : SplitQuadraticForm Q)
    (x y : Variety.Point (splitUnitQuadric (k := k) s.rank)) :
    LinearMap.GeneralLinearGroup.generalLinearEquiv k V
        (glPointEquivOf k V (Module.finBasis k V)
          ((splitUnitQuadricSymmetryMorphism s).toFun x *
            (splitUnitQuadricSymmetryMorphism s).toFun y)) =
      (symmetryPoint (splitUnitQuadricAnisotropicVector s x) *
        symmetryPoint (splitUnitQuadricAnisotropicVector s y)).1 := by
  rw [← splitGeneralLinearPointMulEquiv_apply]
  rw [map_mul, splitGeneralLinearPointMulEquiv_symmetryMorphism,
    splitGeneralLinearPointMulEquiv_symmetryMorphism]
  rw [(LinearMap.GeneralLinearGroup.generalLinearEquiv k V).map_mul]
  change _ = (symmetryPoint (splitUnitQuadricAnisotropicVector s x)).1 *
    (symmetryPoint (splitUnitQuadricAnisotropicVector s y)).1
  rw [splitUnitQuadricSymmetryPoint_linearEquiv,
    splitUnitQuadricSymmetryPoint_linearEquiv]

private lemma splitUnitQuadricSymmetryRightMorphism_points
    (s : SplitQuadraticForm Q) (hrank : 4 ≤ s.rank)
    (x y : Variety.Point (splitUnitQuadric (k := k) s.rank)) :
    evenSpinActionImageClosedSubgroupPoints Q s hrank
        ((splitUnitQuadricSymmetryRightMorphism s hrank y).toFun x) =
      (⟨symmetryPoint (splitUnitQuadricAnisotropicVector s x) *
          symmetryPoint (splitUnitQuadricAnisotropicVector s y),
        symmetryPair_mem_commutator s
          (splitUnitQuadricAnisotropicVector s x)
          (splitUnitQuadricAnisotropicVector s y)⟩ :
        commutator (quadraticIsometrySubgroup Q)) := by
  apply Subtype.ext
  apply Subtype.ext
  rw [← evenSpinActionImageClosedSubgroup_linear_points Q s hrank]
  rw [splitUnitQuadricSymmetryRightMorphism_inclusion]
  exact splitUnitQuadricSymmetry_pair_linear_points s x y

private noncomputable def omegaIdentityImageSubgroup
    (s : SplitQuadraticForm Q) (hrank : 4 ≤ s.rank) :
    Subgroup (commutator (quadraticIsometrySubgroup Q)) :=
  (AlgebraicGroup.identityComponentSubgroup
      (evenSpinActionImageClosedSubgroup Q s).carrierVariety).map
    (evenSpinActionImageClosedSubgroupPoints Q s hrank).toMonoidHom

private lemma symmetryPair_mem_omegaIdentityImage
    (s : SplitQuadraticForm Q) (hrank : 4 ≤ s.rank)
    (a b : AnisotropicVector Q) :
    (⟨symmetryPoint a * symmetryPoint b,
      symmetryPair_mem_commutator s a b⟩ :
        commutator (quadraticIsometrySubgroup Q)) ∈
      omegaIdentityImageSubgroup s hrank := by
  let x := omegaNormalizedQuadricPoint s a
  let y := omegaNormalizedQuadricPoint s b
  let p := (splitUnitQuadricSymmetryRightMorphism s hrank y).toFun x
  refine ⟨p, splitUnitQuadricSymmetry_pair_mem_identityComponent
    s hrank x y, ?_⟩
  change evenSpinActionImageClosedSubgroupPoints Q s hrank p = _
  rw [show evenSpinActionImageClosedSubgroupPoints Q s hrank p =
      (⟨symmetryPoint (splitUnitQuadricAnisotropicVector s x) *
          symmetryPoint (splitUnitQuadricAnisotropicVector s y),
        symmetryPair_mem_commutator s
          (splitUnitQuadricAnisotropicVector s x)
          (splitUnitQuadricAnisotropicVector s y)⟩ :
            commutator (quadraticIsometrySubgroup Q)) by
      exact splitUnitQuadricSymmetryRightMorphism_points s hrank x y]
  have hx : symmetryPoint (splitUnitQuadricAnisotropicVector s x) =
      symmetryPoint a := omegaNormalizedQuadricPoint_symmetryPoint s a
  have hy : symmetryPoint (splitUnitQuadricAnisotropicVector s y) =
      symmetryPoint b := omegaNormalizedQuadricPoint_symmetryPoint s b
  apply Subtype.ext
  exact congrArg₂ (· * ·) hx hy

private lemma evenSymmetryProductPoint_mem_omegaIdentityImage
    (s : SplitQuadraticForm Q) (hrank : 4 ≤ s.rank) :
    ∀ (as : List (AnisotropicVector Q)), Even as.length →
      ∃ hmem : symmetryProductPoint as ∈
          commutator (quadraticIsometrySubgroup Q),
        (⟨symmetryProductPoint as, hmem⟩ :
            commutator (quadraticIsometrySubgroup Q)) ∈
          omegaIdentityImageSubgroup s hrank
  | [], _ => by
      have hmem : symmetryProductPoint ([] : List (AnisotropicVector Q)) ∈
          commutator (quadraticIsometrySubgroup Q) := by
        rw [symmetryProductPoint_nil]
        exact (commutator (quadraticIsometrySubgroup Q)).one_mem
      refine ⟨hmem, ?_⟩
      have heq :
          (⟨symmetryProductPoint ([] : List (AnisotropicVector Q)), hmem⟩ :
              commutator (quadraticIsometrySubgroup Q)) = 1 := by
        apply Subtype.ext
        exact symmetryProductPoint_nil
      rw [heq]
      exact (omegaIdentityImageSubgroup s hrank).one_mem
  | [a], has => by simp at has
  | a :: b :: as, has => by
      obtain ⟨n, hn⟩ := has
      have has' : Even as.length := by
        refine ⟨n - 1, ?_⟩
        simp only [List.length_cons] at hn
        omega
      obtain ⟨htail, htailImage⟩ :=
        evenSymmetryProductPoint_mem_omegaIdentityImage s hrank as has'
      have hword : symmetryProductPoint (a :: b :: as) ∈
          commutator (quadraticIsometrySubgroup Q) := by
        rw [symmetryProductPoint_cons, symmetryProductPoint_cons]
        rw [← mul_assoc]
        exact mul_mem (symmetryPair_mem_commutator s a b) htail
      refine ⟨hword, ?_⟩
      have hmul := (omegaIdentityImageSubgroup s hrank).mul_mem
        (symmetryPair_mem_omegaIdentityImage s hrank a b) htailImage
      have heq :
          (⟨symmetryProductPoint (a :: b :: as), hword⟩ :
              commutator (quadraticIsometrySubgroup Q)) =
            (⟨symmetryPoint a * symmetryPoint b,
                symmetryPair_mem_commutator s a b⟩ :
              commutator (quadraticIsometrySubgroup Q)) *
            (⟨symmetryProductPoint as, htail⟩ :
              commutator (quadraticIsometrySubgroup Q)) := by
        apply Subtype.ext
        calc
          symmetryProductPoint (a :: b :: as) =
              symmetryPoint a * symmetryProductPoint (b :: as) :=
            symmetryProductPoint_cons a (b :: as)
          _ = symmetryPoint a *
              (symmetryPoint b * symmetryProductPoint as) :=
            congrArg (symmetryPoint a * ·)
              (symmetryProductPoint_cons b as)
          _ = (symmetryPoint a * symmetryPoint b) *
              symmetryProductPoint as :=
            (mul_assoc (symmetryPoint a) (symmetryPoint b)
              (symmetryProductPoint as)).symm
      rw [heq]
      exact hmul

/-- The split even Spin action image is connected in every characteristic. -/
public theorem evenSpinActionImageClosedSubgroup_isConnected
    (s : SplitQuadraticForm Q) (hrank : 4 ≤ s.rank) :
    IsConnected (Set.univ : Set (Variety.Point
      (evenSpinActionImageClosedSubgroup Q s).carrierVariety)) := by
  let I := evenSpinActionImageClosedSubgroup Q s
  let e := evenSpinActionImageClosedSubgroupPoints Q s hrank
  have hsubset : Set.univ ⊆ AlgebraicGroup.identityComponent I.carrierVariety := by
    intro g _
    let qg := e g
    obtain ⟨as, hasEven, hasProduct⟩ :=
      exists_even_symmetryFactorization_of_mem_commutator s hrank qg.property
    obtain ⟨hword, hwordImage⟩ :=
      evenSymmetryProductPoint_mem_omegaIdentityImage s hrank as hasEven
    have hqImage : qg ∈ omegaIdentityImageSubgroup s hrank := by
      have heq :
          (⟨symmetryProductPoint as, hword⟩ :
              commutator (quadraticIsometrySubgroup Q)) = qg := by
        apply Subtype.ext
        exact hasProduct
      rw [heq] at hwordImage
      exact hwordImage
    change qg ∈ (AlgebraicGroup.identityComponentSubgroup I.carrierVariety).map
      e.toMonoidHom at hqImage
    obtain ⟨x, hx, hxeq⟩ := hqImage
    have hxg : x = g := by
      apply e.injective
      exact hxeq.trans rfl
    rwa [hxg] at hx
  have hid : AlgebraicGroup.identityComponent I.carrierVariety = Set.univ := by
    apply Set.Subset.antisymm
    · exact Set.subset_univ _
    · exact hsubset
  rw [← hid]
  exact AlgebraicGroup.identityComponent_isConnected I.carrierVariety

end Theory.AlgebraicGroup
