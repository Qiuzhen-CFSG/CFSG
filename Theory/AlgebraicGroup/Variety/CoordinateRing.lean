module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.Topology.NoetherianSpace
public import Theory.AlgebraicGroup.Variety.PolynomialFunction
public import Theory.AlgebraicGroup.Variety.Zariski

universe u

/-!
Vanishing ideals, Noetherianity, and the reduced coordinate ring of a presented affine variety.
-/

namespace Theory.AlgebraicGroup

open scoped TensorProduct

open LinearMap Submodule

variable {k : Type u} [Field k]

/-- The vanishing ideal of a set of rational points: all polynomials that
vanish on every point of the set. -/
@[reducible, expose]
public def vanishingIdeal {V : Variety k} (S : Set (Variety.Point V)) :
    Ideal (MvPolynomial V.Coordinates k) where
  carrier := {p | ∀ x ∈ S, evalPolynomial x.val p = 0}
  zero_mem' := by
    intro x hx
    simp [evalPolynomial]
  add_mem' := by
    intro p q hp hq x hx
    have h1 := hp x hx
    have h2 := hq x hx
    rw [show evalPolynomial x.val (p + q) =
        evalPolynomial x.val p + evalPolynomial x.val q by
      simp [evalPolynomial]]
    rw [h1, h2]
    simp
  smul_mem' := by
    intro c p hp x hx
    have h1 := hp x hx
    rw [show evalPolynomial x.val (c • p) =
        evalPolynomial x.val c * evalPolynomial x.val p by
      simp [evalPolynomial]]
    rw [h1]
    simp

/-- A closed set is exactly the zero locus of its vanishing ideal. -/
public theorem zeroLocus_vanishingIdeal {V : Variety k}
    {S : Set (Variety.Point V)} (hS : IsZariskiClosed V S) :
    {x : Variety.Point V | ∀ p ∈ vanishingIdeal S, evalPolynomial x.val p = 0} = S := by
  apply Set.Subset.antisymm
  · intro x hx
    by_contra hxS
    rcases hS with ⟨E, hE⟩
    have hxE : ¬ ∀ p ∈ E, evalPolynomial x.val p = 0 := by
      intro hpall
      exact hxS (by simpa [hE] using hpall)
    push Not at hxE
    rcases hxE with ⟨p, hpE, hpneq⟩
    have hpvan : p ∈ vanishingIdeal S := by
      intro y hyS
      rw [hE] at hyS
      exact hyS p hpE
    exact hpneq (hx p hpvan)
  · intro x hx p hp
    exact hp x hx

/-- The vanishing ideal is strictly antitone on closed sets. -/
public theorem vanishingIdeal_strict_antitone {V : Variety k}
    {S T : Set (Variety.Point V)}
    (hS : IsZariskiClosed V S) (hT : IsZariskiClosed V T) (h : T ⊂ S) :
    vanishingIdeal S < vanishingIdeal T := by
  have hle : vanishingIdeal S ≤ vanishingIdeal T := by
    intro p hp x hxT
    exact hp x (h.1 hxT)
  refine ⟨hle, ?_⟩
  intro hle'
  have hEq : vanishingIdeal S = vanishingIdeal T := le_antisymm hle hle'
  have hT' : T = {x : Variety.Point V | ∀ p ∈ vanishingIdeal T,
      evalPolynomial x.val p = 0} := by
    symm
    exact zeroLocus_vanishingIdeal hT
  have hS' : {x : Variety.Point V | ∀ p ∈ vanishingIdeal S,
      evalPolynomial x.val p = 0} = S := zeroLocus_vanishingIdeal hS
  have : T = S := by
    calc
      T = {x : Variety.Point V | ∀ p ∈ vanishingIdeal T,
          evalPolynomial x.val p = 0} := hT'
      _ = {x : Variety.Point V | ∀ p ∈ vanishingIdeal S,
          evalPolynomial x.val p = 0} := by
        congr 1
        funext p
        apply propext
        constructor
        · intro hp
          simpa [← hEq] using hp
        · intro hp
          simpa [hEq] using hp
      _ = S := hS'
  exact h.2 (by rw [this])

/-- The Zariski-closed point space of a presented variety is Noetherian:
the vanishing-ideal correspondence transfers the ascending chain condition of
the polynomial coordinate ring to descending chains of closed sets. -/
public instance Variety.noetherianSpace_point (V : Variety k) :
    TopologicalSpace.NoetherianSpace (Variety.Point V) := by
  have hwf : WellFounded (fun a b : TopologicalSpace.Closeds (Variety.Point V) => a < b) := by
    rw [wellFounded_iff_isEmpty_descending_chain]
    apply IsEmpty.mk
    intro f
    let g : ℕ → Ideal (MvPolynomial V.Coordinates k) :=
      fun n => vanishingIdeal (f.1 n : Set (Variety.Point V))
    have hg : ∀ n, g n < g (n + 1) := by
      intro n
      apply vanishingIdeal_strict_antitone
      · rw [← Variety.isClosed_iff_isZariskiClosed]
        exact (f.1 n).isClosed
      · rw [← Variety.isClosed_iff_isZariskiClosed]
        exact (f.1 (n + 1)).isClosed
      · -- (f.1 (n+1) : Set) ⊂ (f.1 n : Set), from f.2 n : f.1 (n+1) < f.1 n (as Closeds)
        constructor
        · simpa using (f.2 n).1
        · intro hEqSet
          exact (f.2 n).2 (by simpa using hEqSet)
    have hacc : IsEmpty {g' : ℕ → Ideal (MvPolynomial V.Coordinates k) //
        ∀ n, g' (n + 1) > g' n} :=
      (wellFounded_iff_isEmpty_descending_chain
        (α := Ideal (MvPolynomial V.Coordinates k)) (r := (· > ·))).mp
        (wellFounded_gt (α := Ideal (MvPolynomial V.Coordinates k)))
    exact (hacc.false ⟨g, fun n => hg n⟩).elim
  have hiff : WellFoundedLT (TopologicalSpace.Closeds (Variety.Point V)) ↔
      TopologicalSpace.NoetherianSpace (Variety.Point V) :=
    (TopologicalSpace.noetherianSpace_TFAE (Variety.Point V)).out 1 0
  exact hiff.1 ⟨hwf⟩

/-- The canonical surjection from the coordinate polynomial ring to the
polynomial functions on a presented variety: evaluation at the rational
points. -/
@[expose]
public def evaluationRingHom {V : Variety k} :
    MvPolynomial V.Coordinates k →+* Variety.PolynomialFunction V where
  toFun := fun p => Variety.PolynomialFunction.ofPolynomial V p
  map_one' := by
    apply Variety.PolynomialFunction.ext
    intro x
    simp [Variety.PolynomialFunction.ofPolynomial, Variety.PolynomialFunction.toFun,
      evalPolynomial]
  map_mul' := by
    intro p q
    apply Variety.PolynomialFunction.ext
    intro x
    simp [Variety.PolynomialFunction.ofPolynomial, Variety.PolynomialFunction.toFun,
      evalPolynomial]
  map_zero' := by
    apply Variety.PolynomialFunction.ext
    intro x
    simp [Variety.PolynomialFunction.ofPolynomial, Variety.PolynomialFunction.toFun,
      evalPolynomial]
  map_add' := by
    intro p q
    apply Variety.PolynomialFunction.ext
    intro x
    simp [Variety.PolynomialFunction.ofPolynomial, Variety.PolynomialFunction.toFun,
      evalPolynomial]

/-- The kernel of evaluation is exactly the vanishing ideal of the whole
rational point space. -/
public theorem evaluationRingHom_ker_eq_vanishingIdeal (V : Variety k) :
    RingHom.ker (evaluationRingHom (V := V)) = vanishingIdeal (Set.univ : Set (Variety.Point V)) := by
  ext p
  constructor
  · intro hp x hx
    have := congrArg (fun f : Variety.PolynomialFunction V => f x) hp
    simpa [evaluationRingHom, Variety.PolynomialFunction.ofPolynomial,
      Variety.PolynomialFunction.toFun] using this
  · intro hp
    apply Subtype.ext
    funext x
    simpa [evaluationRingHom, Variety.PolynomialFunction.ofPolynomial,
      Variety.PolynomialFunction.toFun] using hp x (Set.mem_univ x)

/-- The affine algebra of the book: the coordinate ring of a presented
variety is the quotient of the multivariate polynomial ring by the vanishing
ideal, and it is canonically isomorphic to the ring of polynomial functions
on the rational points (first isomorphism theorem).  Over the algebraically
closed base field of the book this is the coordinate ring `k[V]` of
Definition 1.1.1, since then the rational points determine the zero locus. -/
public abbrev coordinateRing (V : Variety k) : Type u :=
  MvPolynomial V.Coordinates k ⧸ vanishingIdeal (Set.univ : Set (Variety.Point V))

/-- The coordinate ring is the ring of polynomial functions on the rational
points (first isomorphism theorem, cf. Proposition 1.1.2(c)). -/
@[expose]
public noncomputable def coordinateRingEquivPolynomialFunction (V : Variety k) :
    coordinateRing V ≃+* Variety.PolynomialFunction V := by
  change MvPolynomial V.Coordinates k ⧸ vanishingIdeal (Set.univ : Set (Variety.Point V)) ≃+*
      Variety.PolynomialFunction V
  let φ : MvPolynomial V.Coordinates k ⧸ vanishingIdeal (Set.univ : Set (Variety.Point V)) →+*
      Variety.PolynomialFunction V :=
    Ideal.Quotient.lift (vanishingIdeal (Set.univ : Set (Variety.Point V)))
      (evaluationRingHom (V := V)) (by
        intro p hp
        apply Subtype.ext
        funext x
        exact hp x (Set.mem_univ x))
  refine RingEquiv.ofBijective φ ?_
  constructor
  · intro a b hab
    refine (Quotient.inductionOn₂ a b (motive := fun x y => φ x = φ y → x = y) ?_) hab
    intro p q hpq
    have hpminusq : p - q ∈ vanishingIdeal (Set.univ : Set (Variety.Point V)) := by
      change ∀ x : Variety.Point V, x ∈ (Set.univ : Set (Variety.Point V)) →
        evalPolynomial x.val (p - q) = 0
      intro x hx
      have hEqx : evalPolynomial x.val p = evalPolynomial x.val q := by
        have h := congrArg (fun f : Variety.PolynomialFunction V => f x) hpq
        have hφp : φ ⟦p⟧ = evaluationRingHom (V := V) p := rfl
        have hφq : φ ⟦q⟧ = evaluationRingHom (V := V) q := rfl
        rw [hφp, hφq] at h
        simpa [evaluationRingHom, Variety.PolynomialFunction.ofPolynomial,
          Variety.PolynomialFunction.toFun] using h
      rw [show evalPolynomial x.val (p - q) =
          evalPolynomial x.val p - evalPolynomial x.val q by
        simp [evalPolynomial]]
      rw [hEqx]
      ring
    exact (Ideal.Quotient.eq (I := vanishingIdeal (Set.univ : Set (Variety.Point V)))).mpr hpminusq
  · intro f
    rcases f.representedBy with ⟨p, hp⟩
    refine ⟨Ideal.Quotient.mk (vanishingIdeal (Set.univ : Set (Variety.Point V))) p, ?_⟩
    apply Variety.PolynomialFunction.ext
    intro x
    simp [φ, Ideal.Quotient.lift_mk, evaluationRingHom,
      Variety.PolynomialFunction.ofPolynomial, Variety.PolynomialFunction.toFun]
    exact (hp x).symm

/-- The coordinate-ring equivalence sends the class of a polynomial to its
polynomial function. -/
@[simp] public theorem coordinateRingEquivPolynomialFunction_mk
    (V : Variety k) (p : MvPolynomial V.Coordinates k) :
    coordinateRingEquivPolynomialFunction V
        (Ideal.Quotient.mk (vanishingIdeal (Set.univ : Set (Variety.Point V))) p) =
      evaluationRingHom p := by
  rfl

end Theory.AlgebraicGroup
