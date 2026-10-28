module

public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Theory.AlgebraicGroup.Dimension.Algebraic
public import Theory.AlgebraicGroup.Dimension.Defs

universe u v

/-! Irreducibility, coordinate domains, and component-dimension bounds. -/

namespace Theory.AlgebraicGroup

open scoped TensorProduct Cardinal

open LinearMap Submodule

variable {k : Type u} [Field k]

/-- An irreducible point space has prime vanishing ideal (group-free version,
needed for the irreducible components of a variety). -/
public theorem isPrime_vanishingIdeal_of_isIrreducible (V : Variety k)
    (h : IsIrreducible (Set.univ : Set (Variety.Point V))) :
    (vanishingIdeal (Set.univ : Set (Variety.Point V))).IsPrime := by
  constructor
  · intro htop
    have hone : (1 : MvPolynomial V.Coordinates k) ∈ vanishingIdeal (Set.univ : Set (Variety.Point V)) := by
      rw [htop]
      exact Submodule.mem_top
    have hg : ¬ (Set.univ : Set (Variety.Point V)).Nonempty := by
      intro hne
      rcases hne with ⟨x, hx⟩
      have hzero : evalPolynomial x.val (1 : MvPolynomial V.Coordinates k) = 0 := hone x hx
      have honez : evalPolynomial x.val (1 : MvPolynomial V.Coordinates k) = 1 := by simp [evalPolynomial]
      exact zero_ne_one (honez ▸ hzero.symm)
    exact hg h.1
  · intro a b hab
    by_contra hnot
    have ha : a ∉ vanishingIdeal (Set.univ : Set (Variety.Point V)) := by
      intro ha'; exact hnot (Or.inl ha')
    have hb : b ∉ vanishingIdeal (Set.univ : Set (Variety.Point V)) := by
      intro hb'; exact hnot (Or.inr hb')
    have hax : ∃ x : Variety.Point V, evalPolynomial x.val a ≠ 0 := by
      by_contra h0
      apply ha
      intro x hx
      by_contra hx0
      exact h0 ⟨x, hx0⟩
    have hbx : ∃ x : Variety.Point V, evalPolynomial x.val b ≠ 0 := by
      by_contra h0
      apply hb
      intro x hx
      by_contra hx0
      exact h0 ⟨x, hx0⟩
    let u : Set (Variety.Point V) := {x | evalPolynomial x.val a ≠ 0}
    let v : Set (Variety.Point V) := {x | evalPolynomial x.val b ≠ 0}
    have hu : IsOpen u := by
      have hza : IsZariskiClosed V {x : Variety.Point V | evalPolynomial x.val a = 0} :=
        ⟨{a}, by ext x; simp⟩
      have hc : IsClosed {x : Variety.Point V | evalPolynomial x.val a = 0} :=
        Variety.isClosed_iff_isZariskiClosed.mpr hza
      exact (isOpen_compl_iff.mpr hc)
    have hv : IsOpen v := by
      have hzb : IsZariskiClosed V {x : Variety.Point V | evalPolynomial x.val b = 0} :=
        ⟨{b}, by ext x; simp⟩
      have hc : IsClosed {x : Variety.Point V | evalPolynomial x.val b = 0} :=
        Variety.isClosed_iff_isZariskiClosed.mpr hzb
      exact (isOpen_compl_iff.mpr hc)
    rcases hax with ⟨xa, hxa⟩
    rcases hbx with ⟨xb, hxb⟩
    have huniv : ((Set.univ : Set (Variety.Point V)) ∩ u).Nonempty :=
      ⟨xa, ⟨Set.mem_univ xa, hxa⟩⟩
    have hvuniv : ((Set.univ : Set (Variety.Point V)) ∩ v).Nonempty :=
      ⟨xb, ⟨Set.mem_univ xb, hxb⟩⟩
    have hcase := h.2 u v hu hv huniv hvuniv
    rcases hcase with ⟨x, hx, hxu, hxv⟩
    have hxab : evalPolynomial x.val a * evalPolynomial x.val b = 0 := by
      simpa [evalPolynomial] using (hab x (by trivial))
    exact hxv ((mul_eq_zero.mp hxab).resolve_left hxu)

/-- An irreducible point space has an integral-domain coordinate ring
(group-free version). -/
public theorem isDomain_coordinateRing_of_isIrreducible (V : Variety k)
    (h : IsIrreducible (Set.univ : Set (Variety.Point V))) :
    IsDomain (coordinateRing V) :=
  (Ideal.Quotient.isDomain_iff_prime (I := vanishingIdeal (Set.univ : Set (Variety.Point V)))).mpr
    (isPrime_vanishingIdeal_of_isIrreducible V h)

/-- The vanishing ideal of an irreducible closed subset is prime. -/
public theorem isPrime_vanishingIdeal_of_isIrreducible_set {V : Variety k}
    {S : Set (Variety.Point V)} (_hS : IsZariskiClosed V S) (h : IsIrreducible S) :
    (vanishingIdeal S).IsPrime := by
  constructor
  · intro htop
    have hone : (1 : MvPolynomial V.Coordinates k) ∈ vanishingIdeal S := by
      rw [htop]
      exact Submodule.mem_top
    have hg : ¬ S.Nonempty := by
      intro hne
      rcases hne with ⟨x, hx⟩
      have hzero : evalPolynomial x.val (1 : MvPolynomial V.Coordinates k) = 0 := hone x hx
      have honez : evalPolynomial x.val (1 : MvPolynomial V.Coordinates k) = 1 := by simp [evalPolynomial]
      exact zero_ne_one (honez ▸ hzero.symm)
    exact hg h.1
  · intro a b hab
    by_contra hnot
    have ha : a ∉ vanishingIdeal S := by
      intro ha'; exact hnot (Or.inl ha')
    have hb : b ∉ vanishingIdeal S := by
      intro hb'; exact hnot (Or.inr hb')
    have hax : ∃ x : Variety.Point V, x ∈ S ∧ evalPolynomial x.val a ≠ 0 := by
      by_contra h0
      apply ha
      intro x hx
      by_contra hx0
      exact h0 ⟨x, ⟨hx, hx0⟩⟩
    have hbx : ∃ x : Variety.Point V, x ∈ S ∧ evalPolynomial x.val b ≠ 0 := by
      by_contra h0
      apply hb
      intro x hx
      by_contra hx0
      exact h0 ⟨x, ⟨hx, hx0⟩⟩
    let u : Set (Variety.Point V) := {x | evalPolynomial x.val a ≠ 0}
    let v : Set (Variety.Point V) := {x | evalPolynomial x.val b ≠ 0}
    have hu : IsOpen u := by
      have hza : IsZariskiClosed V {x : Variety.Point V | evalPolynomial x.val a = 0} :=
        ⟨{a}, by ext x; simp⟩
      have hc : IsClosed {x : Variety.Point V | evalPolynomial x.val a = 0} :=
        Variety.isClosed_iff_isZariskiClosed.mpr hza
      exact (isOpen_compl_iff.mpr hc)
    have hv : IsOpen v := by
      have hzb : IsZariskiClosed V {x : Variety.Point V | evalPolynomial x.val b = 0} :=
        ⟨{b}, by ext x; simp⟩
      have hc : IsClosed {x : Variety.Point V | evalPolynomial x.val b = 0} :=
        Variety.isClosed_iff_isZariskiClosed.mpr hzb
      exact (isOpen_compl_iff.mpr hc)
    rcases hax with ⟨xa, hxa⟩
    rcases hbx with ⟨xb, hxb⟩
    have huS : (S ∩ u).Nonempty := ⟨xa, ⟨hxa.1, hxa.2⟩⟩
    have hvS : (S ∩ v).Nonempty := ⟨xb, ⟨hxb.1, hxb.2⟩⟩
    have hcase := h.2 u v hu hv huS hvS
    rcases hcase with ⟨x, hx, hxu, hxv⟩
    have hxab : evalPolynomial x.val a * evalPolynomial x.val b = 0 := by
      simpa [evalPolynomial] using (hab x hx)
    exact hxv ((mul_eq_zero.mp hxab).resolve_left hxu)

/-- The coordinate ring of the closed subvariety of an irreducible component
is an integral domain. -/
public theorem isDomain_coordinateRing_component {V : Variety k}
    (C : Set (Variety.Point V)) (hC : C ∈ irreducibleComponents (Variety.Point V)) :
    IsDomain (coordinateRing (Variety.closedSubvariety
      (Variety.isClosed_iff_isZariskiClosed.mp (isClosed_of_mem_irreducibleComponents
        C hC)))) := by
  let hz : IsZariskiClosed V C := Variety.isClosed_iff_isZariskiClosed.mp
    (isClosed_of_mem_irreducibleComponents C hC)
  have hI : vanishingIdeal (Set.univ : Set (Variety.Point (Variety.closedSubvariety hz))) =
      vanishingIdeal C := by
    ext p
    constructor
    · intro hp x hx
      let y : Variety.Point (Variety.closedSubvariety hz) :=
        (Variety.closedSubvarietyPointEquiv hz).symm ⟨x, hx⟩
      have hyx : y.val = x.val := by
        rfl
      have hval : evalPolynomial y.val p = 0 :=
        hp y (Set.mem_univ _)
      rw [← hyx]
      exact hval
    · intro hp x hx
      have hyx : (Variety.closedSubvarietyPointEquiv hz x).1.val = x.val := by
        rfl
      rw [← hyx]
      exact hp (Variety.closedSubvarietyPointEquiv hz x).1
        (Variety.closedSubvarietyPointEquiv hz x).2
  have hC' : IsIrreducible C := hC.1
  have hprim : (vanishingIdeal (Set.univ : Set (Variety.Point (Variety.closedSubvariety hz)))).IsPrime := by
    rw [hI]
    exact isPrime_vanishingIdeal_of_isIrreducible_set hz hC'
  exact (Ideal.Quotient.isDomain_iff_prime (I := vanishingIdeal
    (Set.univ : Set (Variety.Point (Variety.closedSubvariety hz))))).mpr hprim

/-- The dimension of an irreducible component is bounded by the number of
coordinates. -/
public theorem componentDimension_le_coordinates (V : Variety k)
    (C : Set (Variety.Point V)) (hC : C ∈ irreducibleComponents (Variety.Point V)) :
    Variety.componentDimension V C hC ≤ #(V.Coordinates) := by
  classical
  let hz : IsZariskiClosed V C := Variety.isClosed_iff_isZariskiClosed.mp
    (isClosed_of_mem_irreducibleComponents C hC)
  let W : Variety k := Variety.closedSubvariety hz
  have : IsDomain (coordinateRing W) := by
    simpa [W, hz] using isDomain_coordinateRing_component C hC
  let x : W.Coordinates → FractionRing (coordinateRing W) := fun i =>
    algebraMap (coordinateRing W) (FractionRing (coordinateRing W))
      (Ideal.Quotient.mk (vanishingIdeal (Set.univ : Set (Variety.Point W))) (MvPolynomial.X i))
  have hAlg : Algebra.IsAlgebraic (Algebra.adjoin k (Set.range x))
      (FractionRing (coordinateRing W)) := by
    simpa [x] using fractionRing_isAlgebraic_of_coordinates W
  have htrdeg : Algebra.trdeg k (FractionRing (coordinateRing W)) ≤ #(Set.range x) := by
    have : Algebra.IsAlgebraic (Algebra.adjoin k (Set.range x))
        (FractionRing (coordinateRing W)) := by simpa [x] using hAlg
    have : NoZeroDivisors (FractionRing (coordinateRing W)) := by infer_instance
    exact Algebra.IsAlgebraic.trdeg_le_cardinalMk k (Set.range x)
  have hrange : #(Set.range x) ≤ #(W.Coordinates) := Cardinal.mk_range_le
  have hcomp : Variety.componentDimension V C hC =
      Algebra.trdeg k (FractionRing (coordinateRing W)) := by
    simp [Variety.componentDimension, W]
  rw [hcomp]
  exact htrdeg.trans (by simpa [W] using hrange)

end Theory.AlgebraicGroup
