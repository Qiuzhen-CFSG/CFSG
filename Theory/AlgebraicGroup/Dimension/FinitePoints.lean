module

public import Theory.AlgebraicGroup.Semisimple.Components.ComponentFamily

/-!
Zero-dimensional presented affine varieties have finitely many rational points. A Noetherian
point space has finitely many irreducible components. On each component, zero transcendence
degree of the coordinate fraction field makes every coordinate algebraic; a nonzero polynomial
therefore confines that coordinate to a finite root set. The component embeds into the finite
product of these root sets. This is the finiteness bridge for proper normal subgroups of simple
components.
-/

set_option warningAsError false

namespace Theory.AlgebraicGroup

public theorem Variety.finite_points_of_dimension_zero {k : Type*} [Field k] [IsAlgClosed k] (V : Variety k) (hV : Variety.dimension V = 0) : Finite (Variety.Point V) := by
  classical
  have component_finite (C : Set (Variety.Point V))
      (hC : C ∈ irreducibleComponents (Variety.Point V)) : C.Finite := by
    let hz : IsZariskiClosed V C := Variety.isClosed_iff_isZariskiClosed.mp
      (isClosed_of_mem_irreducibleComponents C hC)
    let W : Variety k := Variety.closedSubvariety hz
    letI : IsDomain (coordinateRing W) := by
      simpa [W, hz] using isDomain_coordinateRing_component C hC
    have hdim : Variety.componentDimension V C hC = 0 := by
      apply le_zero_iff.mp
      exact (le_ciSup Cardinal.bddAbove_of_small
        (⟨C, hC⟩ : {D : Set (Variety.Point V) //
          D ∈ irreducibleComponents (Variety.Point V)})).trans (le_of_eq hV)
    have halg : Algebra.IsAlgebraic k (FractionRing (coordinateRing W)) :=
      trdeg_eq_zero_iff.mp (by
        simpa [Variety.componentDimension, W, hz] using hdim)
    have hroot (i : V.Coordinates) :
        ∃ p : Polynomial k, p ≠ 0 ∧
          ∀ x : Variety.Point V, x ∈ C → p.IsRoot (x.val i) := by
      let a : coordinateRing W :=
        Ideal.Quotient.mk (vanishingIdeal (Set.univ : Set (Variety.Point W)))
          (MvPolynomial.X i)
      have ha : IsAlgebraic k a :=
        (isAlgebraic_algebraMap_iff (R := k) (a := a)
          (IsFractionRing.injective (coordinateRing W) (FractionRing (coordinateRing W)))).mp
          (halg.1 (algebraMap (coordinateRing W) (FractionRing (coordinateRing W)) a))
      obtain ⟨p, hp, hpa⟩ := ha
      refine ⟨p, hp, ?_⟩
      intro x hx
      let y : Variety.Point W :=
        (Variety.closedSubvarietyPointEquiv hz).symm ⟨x, hx⟩
      have hpq : Ideal.Quotient.mk
          (vanishingIdeal (Set.univ : Set (Variety.Point W)))
          (Polynomial.aeval (MvPolynomial.X (R := k) i) p) = 0 := by
        simpa [a, aeval_quotient_X] using hpa
      have hpy : evalPolynomial y.val
          (Polynomial.aeval (MvPolynomial.X (R := k) i) p) = 0 :=
        (Ideal.Quotient.eq_zero_iff_mem.mp hpq) y (Set.mem_univ y)
      have hyx : y.val = x.val := by rfl
      change p.eval (x.val i) = 0
      simpa only [evalPolynomial_aeval_X, hyx] using hpy
    choose p hp hpoints using hroot
    let f : C → (i : V.Coordinates) →
        {a : k // (p i).IsRoot a} :=
      fun x i => ⟨x.1.val i, hpoints i x.1 x.2⟩
    haveI : ∀ i : V.Coordinates, Finite {a : k // (p i).IsRoot a} :=
      fun i => (Polynomial.finite_setOfPred_isRoot (hp i)).to_subtype
    haveI : Finite ((i : V.Coordinates) → {a : k // (p i).IsRoot a}) :=
      Pi.finite
    have hfin : Finite C := Finite.of_injective f (by
      intro x y hxy
      apply Subtype.ext
      apply Variety.Point.ext
      funext i
      exact congrArg Subtype.val (congrFun hxy i))
    exact Set.finite_coe_iff.mpr hfin
  have hcomps : (irreducibleComponents (Variety.Point V)).Finite :=
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
  have hunion : (⋃₀ irreducibleComponents (Variety.Point V)).Finite :=
    hcomps.sUnion component_finite
  exact Set.finite_univ_iff.mp (by simpa [sUnion_irreducibleComponents] using hunion)

end Theory.AlgebraicGroup
