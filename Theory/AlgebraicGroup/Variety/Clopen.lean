module

public import Mathlib.RingTheory.Nullstellensatz
public import Theory.AlgebraicGroup.Morphism.Basic
public import Theory.AlgebraicGroup.Variety.CoordinateRing

universe u

/-! Clopen subsets of an affine variety have polynomial characteristic functions. -/

namespace Theory.AlgebraicGroup

section
variable {k : Type u} [Field k] [IsAlgClosed k]

public lemma exists_polynomial_eq_one_on_of_isClopen
    (V : Variety k) (C : Set (Variety.Point V)) (hC : IsClopen C) :
    ∃ p : MvPolynomial V.Coordinates k,
      (∀ x ∈ C, evalPolynomial x.val p = 1) ∧
      ∀ x ∉ C, evalPolynomial x.val p = 0 := by
  let I := vanishingIdeal C
  let J := vanishingIdeal Cᶜ
  have hCZ : IsZariskiClosed V C := by
    rw [← Variety.isClosed_iff_isZariskiClosed]
    exact hC.1
  have hCcZ : IsZariskiClosed V Cᶜ := by
    rw [← Variety.isClosed_iff_isZariskiClosed]
    exact hC.2.isClosed_compl
  have hz : MvPolynomial.zeroLocus k (I ⊔ J) = ∅ := by
    rw [← Set.not_nonempty_iff_eq_empty]
    rintro ⟨x, hx⟩
    have hxV : ∀ q ∈ V.equations, evalPolynomial x q = 0 := by
      intro q hq
      exact hx q (Ideal.mem_sup_left (by
        intro y hy
        exact y.isZero q hq))
    let y : Variety.Point V := ⟨x, hxV⟩
    have hyI : ∀ q ∈ I, evalPolynomial y.val q = 0 := by
      intro q hq
      exact hx q (Ideal.mem_sup_left hq)
    have hyJ : ∀ q ∈ J, evalPolynomial y.val q = 0 := by
      intro q hq
      exact hx q (Ideal.mem_sup_right hq)
    have hyC : y ∈ C := by
      rw [← zeroLocus_vanishingIdeal hCZ]
      exact hyI
    have hyCc : y ∈ Cᶜ := by
      rw [← zeroLocus_vanishingIdeal hCcZ]
      exact hyJ
    exact hyCc hyC
  have htop : I ⊔ J = ⊤ := by
    rw [← Ideal.radical_eq_top]
    rw [← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := k)]
    rw [hz, MvPolynomial.vanishingIdeal_empty]
  have hone : (1 : MvPolynomial V.Coordinates k) ∈ I ⊔ J := by
    rw [htop]
    exact Submodule.mem_top
  obtain ⟨q, hqI, p, hpJ, hsum⟩ := Submodule.mem_sup.mp hone
  refine ⟨p, ?_, ?_⟩
  · intro x hxC
    have hq0 : evalPolynomial x.val q = 0 := hqI x hxC
    have heq := congrArg (evalPolynomial x.val) hsum
    change evalPolynomial x.val (q + p) = evalPolynomial x.val 1 at heq
    simp [evalPolynomial] at heq
    change MvPolynomial.eval x.val q = 0 at hq0
    rw [hq0, zero_add] at heq
    exact heq
  · intro x hxC
    exact hpJ x hxC

end

/-! Gluing scalar polynomial functions across finite clopen partitions. -/

section

variable {k : Type u} [Field k] [IsAlgClosed k]

public lemma Variety.exists_polynomialFunction_of_finite_clopen
    {V : Variety k} {ι : Type u} [Finite ι]
    (c : Variety.Point V → ι)
    (hc : ∀ i, IsClopen {x | c x = i})
    (F : Variety.Point V → k)
    (p : ι → MvPolynomial V.Coordinates k)
    (hp : ∀ i x, c x = i → F x = evalPolynomial x.val (p i)) :
    ∃ f : V.PolynomialFunction, ∀ x, f x = F x := by
  classical
  let := Fintype.ofFinite ι
  let s : ι → MvPolynomial V.Coordinates k := fun i =>
    Classical.choose (exists_polynomial_eq_one_on_of_isClopen V {x | c x = i} (hc i))
  have hs_one (i) (x : Variety.Point V) (hx : c x = i) :
      evalPolynomial x.val (s i) = 1 :=
    (Classical.choose_spec
      (exists_polynomial_eq_one_on_of_isClopen V {x | c x = i} (hc i))).1 x hx
  have hs_zero (i) (x : Variety.Point V) (hx : c x ≠ i) :
      evalPolynomial x.val (s i) = 0 :=
    (Classical.choose_spec
      (exists_polynomial_eq_one_on_of_isClopen V {x | c x = i} (hc i))).2 x hx
  let polynomial := ∑ i, s i * p i
  let f := Variety.PolynomialFunction.ofPolynomial V polynomial
  refine ⟨f, fun x => ?_⟩
  change evalPolynomial x.val polynomial = F x
  rw [show polynomial = ∑ i, s i * p i by rfl, evalPolynomial_sum]
  rw [Finset.sum_eq_single (c x)]
  · rw [evalPolynomial_mul, hs_one (c x) x rfl, one_mul]
    exact (hp (c x) x rfl).symm
  · intro i hi hne
    rw [evalPolynomial_mul, hs_zero i x hne.symm, zero_mul]
  · intro hnot
    exact (hnot (Finset.mem_univ (c x))).elim

end

/-! Gluing coordinate formulas across a finite clopen partition. -/

section
variable {k : Type u} [Field k] [IsAlgClosed k]

/-- A point map whose coordinates are polynomial on every fiber of a finite
clopen classifier is a morphism of affine varieties. -/
public lemma Variety.exists_morphism_of_finite_clopen_coordinatewise
    {V W : Variety k} {ι : Type u} [Finite ι]
    (c : Variety.Point V → ι)
    (hc : ∀ i, IsClopen {x | c x = i})
    (F : Variety.Point V → Variety.Point W)
    (p : ι → W.Coordinates → MvPolynomial V.Coordinates k)
    (hp : ∀ i x, c x = i → ∀ j,
      (F x).val j = evalPolynomial x.val (p i j)) :
    ∃ f : Variety.Morphism V W, f.toFun = F := by
  classical
  let := Fintype.ofFinite ι
  let s : ι → MvPolynomial V.Coordinates k := fun i =>
    Classical.choose (exists_polynomial_eq_one_on_of_isClopen V {x | c x = i} (hc i))
  have hs_one (i) (x : Variety.Point V) (hx : c x = i) :
      evalPolynomial x.val (s i) = 1 := by
    exact (Classical.choose_spec
      (exists_polynomial_eq_one_on_of_isClopen V {x | c x = i} (hc i))).1 x hx
  have hs_zero (i) (x : Variety.Point V) (hx : c x ≠ i) :
      evalPolynomial x.val (s i) = 0 := by
    exact (Classical.choose_spec
      (exists_polynomial_eq_one_on_of_isClopen V {x | c x = i} (hc i))).2 x hx
  let f : Variety.Morphism V W :=
    { toFun := F
      regular := by
        intro j
        refine ⟨∑ i, s i * p i j, ?_⟩
        intro x
        rw [evalPolynomial_sum]
        rw [Finset.sum_eq_single (c x)]
        · rw [evalPolynomial_mul, hs_one (c x) x rfl, one_mul]
          exact hp (c x) x rfl j
        · intro i hi hne
          rw [evalPolynomial_mul, hs_zero i x hne.symm, zero_mul]
        · intro hnot
          exact (hnot (Finset.mem_univ (c x))).elim }
  exact ⟨f, rfl⟩

end

/-!
An algebraic-group wrapper for finite-clopen coordinatewise morphism gluing.
This is the minimal descent bridge needed by the quotient-presentation route.
-/

section

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- A point map with finite-clopen coordinatewise polynomial formulas and
compatible group laws lifts to an algebraic-group morphism. -/
private lemma exists_morphism_of_finite_clopen_coordinatewise
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    {ι : Type u} [Finite ι]
    (c : Variety.Point G → ι)
    (hc : ∀ i, IsClopen {x | c x = i})
    (F : Variety.Point G → Variety.Point H)
    (p : ι → H.Coordinates → MvPolynomial G.Coordinates k)
    (hp : ∀ i x, c x = i → ∀ j,
      (F x).val j = evalPolynomial x.val (p i j))
    (h1 : F 1 = 1)
    (hmul : ∀ x y, F (x * y) = F x * F y) :
    ∃ f : AlgebraicGroup.Morphism G H, f.onPoints = F := by
  obtain ⟨f, hf⟩ :=
    Variety.exists_morphism_of_finite_clopen_coordinatewise c hc F p hp
  let g : AlgebraicGroup.Morphism G H :=
    { toVariety := f,
      map_one := by simpa [hf] using h1,
      map_mul := by simpa [hf] using hmul }
  refine ⟨g, ?_⟩
  simpa [g, AlgebraicGroup.Morphism.onPoints] using hf

end

end Theory.AlgebraicGroup
