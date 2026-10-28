module

public import Theory.AlgebraicGroup.Dimension.Basic

universe u

/-! Finite and zero-dimensional affine varieties. -/

namespace Theory.AlgebraicGroup

open scoped TensorProduct Cardinal

open LinearMap Submodule

variable {k : Type u} [Field k]

variable {k : Type u} [Field k]

public theorem variety_dimension_lt_aleph0 (V : Variety k) :
    Variety.dimension V < ℵ₀ := by
  have hle : ∀ C : {C : Set (Variety.Point V) // C ∈ irreducibleComponents (Variety.Point V)},
      Variety.componentDimension V C.1 C.2 ≤ #(V.Coordinates) := by
    intro C
    exact componentDimension_le_coordinates V C.1 C.2
  have hdim : Variety.dimension V ≤ #(V.Coordinates) := by
    unfold Variety.dimension
    exact ciSup_le' hle
  exact lt_of_le_of_lt hdim (Cardinal.lt_aleph0_iff_finite.mpr inferInstance)

/-- The coordinate images in the coordinate ring are algebraic over `k` as soon
as each coordinate takes values in a fixed finite set. -/
public theorem coordinateRing_coordinate_isAlgebraic_of_finiteValues (V : Variety k)
    (vals : V.Coordinates → Finset k)
    (hvals : ∀ (i : V.Coordinates) (x : Variety.Point V), x.val i ∈ vals i)
    (_hne : ∀ i : V.Coordinates, (vals i).Nonempty) :
    ∀ i : V.Coordinates,
      IsAlgebraic k (Ideal.Quotient.mk (vanishingIdeal (Set.univ : Set (Variety.Point V)))
        (MvPolynomial.X i)) := by
  classical
  intro i
  let p : Polynomial k := (vals i).prod (fun a => Polynomial.X - Polynomial.C a)
  have hp0 : p ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr (fun a ha => sub_ne_zero.mpr (Polynomial.X_ne_C a))
  refine ⟨p, hp0, ?_⟩
  -- aeval xᵢ p = 0
  have hmk : (Ideal.Quotient.mk (vanishingIdeal (Set.univ : Set (Variety.Point V)))
      ((vals i).prod (fun a => MvPolynomial.X (R := k) i - MvPolynomial.C a))) = 0 := by
    apply (Submodule.Quotient.mk_eq_zero
      (p := vanishingIdeal (Set.univ : Set (Variety.Point V)))
      (x := ((vals i).prod (fun a => MvPolynomial.X (R := k) i - MvPolynomial.C a)))).mpr
    intro x hx
    have hxmem : x.val i ∈ vals i := hvals i x
    rw [evalPolynomial]
    simp
    exact Finset.prod_eq_zero hxmem (by simp)
  calc
    Polynomial.aeval (Ideal.Quotient.mk (vanishingIdeal (Set.univ : Set (Variety.Point V)))
        (MvPolynomial.X i)) p =
        Ideal.Quotient.mk (vanishingIdeal (Set.univ : Set (Variety.Point V)))
          (Polynomial.aeval (MvPolynomial.X (R := k) i) p) :=
      aeval_quotient_X V i p
    _ = Ideal.Quotient.mk (vanishingIdeal (Set.univ : Set (Variety.Point V)))
          ((vals i).prod (fun a => MvPolynomial.X (R := k) i - MvPolynomial.C a)) := by
      congr 1
      simp [p, map_prod]
    _ = 0 := hmk

/-- A point whose coordinates are roots of nonzero polynomials has finitely many
possibilities: the fraction ring of the coordinate ring has transcendence
degree zero (Proposition 1.1.6(b), forward direction, at the level of the
coordinate ring). -/
public theorem finite_of_fractionRing_trdeg_eq_zero (V : Variety k)
    (h : Algebra.trdeg k (FractionRing (coordinateRing V)) = 0) : Finite (Variety.Point V) := by
  classical
  have hAlgFrac : Algebra.IsAlgebraic k (FractionRing (coordinateRing V)) :=
    (trdeg_eq_zero_iff (R := k) (A := FractionRing (coordinateRing V))).mp (by exact h)
  have hInj : Function.Injective (algebraMap (coordinateRing V) (FractionRing (coordinateRing V))) :=
    IsFractionRing.injective (coordinateRing V) (FractionRing (coordinateRing V))
  have hcoords : ∀ i : V.Coordinates, IsAlgebraic k
      (Ideal.Quotient.mk (vanishingIdeal (Set.univ : Set (Variety.Point V))) (MvPolynomial.X i)) := by
    intro i
    let xᵢ : coordinateRing V := Ideal.Quotient.mk
      (vanishingIdeal (Set.univ : Set (Variety.Point V))) (MvPolynomial.X i)
    have hx : IsAlgebraic k (algebraMap (coordinateRing V) (FractionRing (coordinateRing V)) xᵢ) :=
      hAlgFrac.1 (algebraMap (coordinateRing V) (FractionRing (coordinateRing V)) xᵢ)
    rcases hx with ⟨p, hp0, hp⟩
    refine ⟨p, hp0, ?_⟩
    -- aeval xᵢ p = 0, pulled back along the injective algebra map
    apply hInj
    rw [aeval_algebraMap_fractionRing (coordinateRing V) xᵢ p]
    exact hp.trans (by simp)
  have hroot : ∀ (i : V.Coordinates) (x : Variety.Point V),
      (Classical.choose (hcoords i)).eval (x.val i) = 0 := by
    intro i x
    have hp : Polynomial.aeval (Ideal.Quotient.mk
        (vanishingIdeal (Set.univ : Set (Variety.Point V))) (MvPolynomial.X i))
        (Classical.choose (hcoords i)) = 0 := (Classical.choose_spec (hcoords i)).2
    have hmem : Polynomial.aeval (MvPolynomial.X (R := k) i) (Classical.choose (hcoords i)) ∈
        vanishingIdeal (Set.univ : Set (Variety.Point V)) := by
      exact (Submodule.Quotient.mk_eq_zero
        (p := vanishingIdeal (Set.univ : Set (Variety.Point V)))
        (x := Polynomial.aeval (MvPolynomial.X (R := k) i) (Classical.choose (hcoords i)))).mp
        ((aeval_quotient_X V i (Classical.choose (hcoords i))).symm.trans hp)
    have hEv := evalPolynomial_aeval_X V x i (Classical.choose (hcoords i))
    exact hEv.symm.trans (hmem x (Set.mem_univ x))
  let vals : V.Coordinates → Finset k := fun i =>
    ((Polynomial.finite_setOfPred_isRoot (R := k) (p := Classical.choose (hcoords i))
      (Classical.choose_spec (hcoords i)).1).toFinset)
  have hvals : ∀ (i : V.Coordinates) (x : Variety.Point V), x.val i ∈ vals i := by
    intro i x
    exact (Polynomial.finite_setOfPred_isRoot (R := k) (p := Classical.choose (hcoords i))
      (Classical.choose_spec (hcoords i)).1).mem_toFinset.mpr (by
        simpa [Polynomial.IsRoot] using hroot i x)
  exact Finite.of_injective
    (fun x : Variety.Point V => (fun i : V.Coordinates =>
      (⟨x.val i, hvals i x⟩ : {a : k // a ∈ vals i})))
    (by
      intro x y h
      apply Variety.Point.ext
      funext i
      exact congrArg (fun f : (i : V.Coordinates) → {a : k // a ∈ vals i} => (f i).1) h)

/-- Finitely many rational points force the fraction ring of the coordinate
ring to have transcendence degree zero (Proposition 1.1.6(b), backward
direction, at the level of the coordinate ring). -/
public theorem fractionRing_trdeg_eq_zero_of_finite (V : Variety k) [Finite (Variety.Point V)] :
    Algebra.trdeg k (FractionRing (coordinateRing V)) = 0 := by
  classical
  let A := coordinateRing V
  by_cases hEmpty : Nonempty (Variety.Point V)
  · have : Fintype (Variety.Point V) := Fintype.ofFinite _
    let vals : V.Coordinates → Finset k := fun i =>
      Finset.univ.image (fun x : Variety.Point V => x.val i)
    have hvals : ∀ (i : V.Coordinates) (x : Variety.Point V), x.val i ∈ vals i := by
      intro i x
      exact Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩
    have hne : ∀ i : V.Coordinates, (vals i).Nonempty := by
      intro i
      rcases hEmpty with ⟨x⟩
      exact ⟨x.val i, Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩⟩
    have hcoord : ∀ i : V.Coordinates, IsAlgebraic k
        (Ideal.Quotient.mk (vanishingIdeal (Set.univ : Set (Variety.Point V)))
          (MvPolynomial.X i)) :=
      coordinateRing_coordinate_isAlgebraic_of_finiteValues V vals hvals hne
    have hAlg : Algebra.IsAlgebraic k A := by
      let x : V.Coordinates → A := fun i =>
        Ideal.Quotient.mk (vanishingIdeal (Set.univ : Set (Variety.Point V)))
          (MvPolynomial.X i)
      have hAdj : (Algebra.adjoin k (Set.range x)).IsAlgebraic := by
        exact (Algebra.isAlgebraic_adjoin_iff (R := k) (s := Set.range x)).mpr (by
          intro a ha
          rcases Set.mem_range.mp ha with ⟨i, rfl⟩
          exact hcoord i)
      have hsurj : ∀ b : A, ∃ p : MvPolynomial V.Coordinates k, MvPolynomial.aeval x p = b := by
        intro b
        refine ⟨Classical.choose (Ideal.Quotient.mk_surjective b), ?_⟩
        have heq : MvPolynomial.aeval x (Classical.choose (Ideal.Quotient.mk_surjective b)) =
            Ideal.Quotient.mk (vanishingIdeal (Set.univ : Set (Variety.Point V)))
              (Classical.choose (Ideal.Quotient.mk_surjective b)) := by
          refine (MvPolynomial.induction_on
            (Classical.choose (Ideal.Quotient.mk_surjective b))
            (motive := fun p => MvPolynomial.aeval x p =
              Ideal.Quotient.mk (vanishingIdeal (Set.univ : Set (Variety.Point V))) p)) ?_ ?_ ?_
          · intro r
            rw [show MvPolynomial.aeval x (MvPolynomial.C r) = algebraMap k A r from by simp]
            rw [show algebraMap k A r =
                Ideal.Quotient.mk (vanishingIdeal (Set.univ : Set (Variety.Point V)))
                  (MvPolynomial.C r) from rfl]
          · intro p q hp hq
            simp [map_add, hp, hq]
          · intro i p hp
            simp [x, hp]
        rw [heq]
        exact Classical.choose_spec (Ideal.Quotient.mk_surjective b)
      have hTop : Algebra.adjoin k (Set.range x) = ⊤ := by
        rw [Algebra.adjoin_range_eq_range_aeval]
        apply Subalgebra.ext
        intro a
        constructor
        · intro _; exact by simp
        · intro _
          refine (AlgHom.mem_range (MvPolynomial.aeval x)).mpr
            ⟨Classical.choose (hsurj a), Classical.choose_spec (hsurj a)⟩
      exact ⟨fun a => hAdj a (hTop ▸ Set.mem_univ a)⟩
    have hAlgFrac : Algebra.IsAlgebraic k (FractionRing A) := fractionRing_isAlgebraic_of_algebraic hAlg
    have : Algebra.IsAlgebraic k (FractionRing (coordinateRing V)) := by
      simpa [A] using hAlgFrac
    have h0 : Algebra.trdeg k (FractionRing (coordinateRing V)) = 0 :=
      trdeg_eq_zero (R := k) (A := FractionRing (coordinateRing V))
    exact h0
  · let : IsEmpty (Variety.Point V) := ⟨fun x => hEmpty ⟨x⟩⟩
    -- the empty point space makes the coordinate ring the zero ring
    have hI : vanishingIdeal (Set.univ : Set (Variety.Point V)) = ⊤ := by
      ext p
      constructor <;> intro
      · exact Submodule.mem_top
      · intro x hx
        exact False.elim (‹IsEmpty (Variety.Point V)›.elim x)
    have h0 : Algebra.trdeg k (FractionRing (coordinateRing V)) = 0 := by
      have : Subsingleton (MvPolynomial V.Coordinates k ⧸ vanishingIdeal (Set.univ : Set (Variety.Point V))) := by
        have hinst : Subsingleton (MvPolynomial V.Coordinates k ⧸
            (⊤ : Ideal (MvPolynomial V.Coordinates k))) := by
          infer_instance
        have htype : (MvPolynomial V.Coordinates k ⧸ vanishingIdeal (Set.univ : Set (Variety.Point V))) =
            (MvPolynomial V.Coordinates k ⧸ (⊤ : Ideal (MvPolynomial V.Coordinates k))) := by
          exact congrArg (fun I : Ideal (MvPolynomial V.Coordinates k) => MvPolynomial V.Coordinates k ⧸ I) hI
        exact htype ▸ hinst
      have : Subsingleton (FractionRing (coordinateRing V)) := by
        infer_instance
      apply trdeg_eq_zero_of_not_injective
      intro hinj
      have hEq : (1 : k) = 0 :=
        hinj (Subsingleton.elim (algebraMap k (FractionRing (coordinateRing V)) 1)
          (algebraMap k (FractionRing (coordinateRing V)) 0))
      exact one_ne_zero hEq
    exact h0

/-- Proposition 1.1.6(b): a presented variety has dimension zero if and only if
it has finitely many rational points (the dimension is the maximum over the
irreducible components, so it vanishes exactly when every component is
zero-dimensional, i.e. finite). -/
public theorem dimension_zero_iff_finite_points (V : Variety k) :
    Variety.dimension V = 0 ↔ Finite (Variety.Point V) := by
  constructor
  · intro hdim
    -- every component has dimension 0
    have hC0 : ∀ C : {C : Set (Variety.Point V) // C ∈ irreducibleComponents (Variety.Point V)},
        Variety.componentDimension V C.1 C.2 = 0 := by
      intro C
      have hb : BddAbove (Set.range (fun D : {D : Set (Variety.Point V) //
          D ∈ irreducibleComponents (Variety.Point V)} => Variety.componentDimension V D.1 D.2)) := by
        exact ⟨#(V.Coordinates), by
          intro x hx
          rcases hx with ⟨D, rfl⟩
          exact componentDimension_le_coordinates V D.1 D.2⟩
      exact le_antisymm (le_trans (le_ciSup hb C) (le_of_eq hdim)) zero_le
    -- each component is finite
    have hCfin : ∀ C, C ∈ irreducibleComponents (Variety.Point V) → Finite C := by
      intro C hC
      let hz : IsZariskiClosed V C := Variety.isClosed_iff_isZariskiClosed.mp
        (isClosed_of_mem_irreducibleComponents C hC)
      let W : Variety k := Variety.closedSubvariety hz
      have hfr : Algebra.trdeg k (FractionRing (coordinateRing W)) = 0 := by
        have hc0 := hC0 ⟨C, hC⟩
        simpa [Variety.componentDimension, W, hz] using hc0
      have hfinSub : Finite (Variety.Point W) := finite_of_fractionRing_trdeg_eq_zero W hfr
      exact (Equiv.finite_iff (Variety.closedSubvarietyPointEquiv hz)).mp hfinSub
    -- the point space is the (finite) union of the components
    have hcompFin : (irreducibleComponents (Variety.Point V)).Finite :=
      TopologicalSpace.NoetherianSpace.finite_irreducibleComponents (α := Variety.Point V)
    have hunion : ⋃₀ irreducibleComponents (Variety.Point V) = Set.univ :=
      sUnion_irreducibleComponents (X := Variety.Point V)
    have hsetFin : (⋃₀ irreducibleComponents (Variety.Point V)).Finite := by
      exact Set.Finite.sUnion hcompFin (fun C hC => by
        let : Finite C := hCfin C hC
        exact Set.finite_def.mpr (nonempty_fintype (α := C)))
    exact Set.finite_univ_iff.mp (hsetFin.subset (by rw [hunion]))
  · intro hfin
    -- every component is finite (it is contained in the whole space)
    have hCfin : ∀ C, C ∈ irreducibleComponents (Variety.Point V) → Finite C := by
      intro C hC
      exact ((Set.finite_univ (α := Variety.Point V)).subset (by
        intro x hx
        exact Set.mem_univ x)).to_subtype
    -- each component has dimension 0
    have hC0 : ∀ C : {C : Set (Variety.Point V) // C ∈ irreducibleComponents (Variety.Point V)},
        Variety.componentDimension V C.1 C.2 = 0 := by
      intro C
      let hz : IsZariskiClosed V C.1 := Variety.isClosed_iff_isZariskiClosed.mp
        (isClosed_of_mem_irreducibleComponents C.1 C.2)
      let W : Variety k := Variety.closedSubvariety hz
      have hfinSub : Finite (Variety.Point W) :=
        (Equiv.finite_iff (Variety.closedSubvarietyPointEquiv hz)).mpr (hCfin C.1 C.2)
      have hfr : Algebra.trdeg k (FractionRing (coordinateRing W)) = 0 :=
        fractionRing_trdeg_eq_zero_of_finite W
      simp [Variety.componentDimension, W, hfr]
    -- the supremum of the (zero) component dimensions vanishes
    unfold Variety.dimension
    exact le_antisymm (ciSup_le' (fun C => le_of_eq (hC0 C))) zero_le

end Theory.AlgebraicGroup
