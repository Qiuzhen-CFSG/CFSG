module

public import Theory.AlgebraicGroup.RootSystems.G2ChevalleyBruhatCover
public import Theory.AlgebraicGroup.Dimension.Product
public import Theory.AlgebraicGroup.Dimension.Torus
public import Theory.AlgebraicGroup.Dimension.Fiber

/-!
# G2 Chevalley carrier dimension bound

For an algebraically closed field, this module bounds the dimension of the
closed `G2` Chevalley carrier by fourteen.  The explicit Bruhat cover from the
preceding module has twelve cells, each with six negative-root coordinates,
the two-dimensional split torus, and six positive-root coordinates.

The proof first computes the exact dimension of the cell domain
`A^6 x dVariety k 2 x A^6`.  An irreducible component of the carrier is
covered by finitely many closed cell closures, so irreducibility places that
component inside one cell closure.  The resulting dense morphism from the
corresponding closed subvariety of the cell domain gives the component
dimension bound by injectivity of pullback on polynomial functions.

The construction uses only the characteristic-free explicit root curves,
split-torus parametrization, and matrix-checked Chevalley/Bruhat relations
packaged by the cover module.  In particular, it does not use root
exhaustiveness, semisimplicity, center calculations, or any general
classification theorem.
-/

universe u

@[expose] public section

namespace Theory.AlgebraicGroup.G2Chevalley

open Theory.AlgebraicGroup
open scoped Cardinal

variable {k : Type u} [Field k] [IsAlgClosed k]

noncomputable section

private lemma affineSpace_isIrreducible (sigma : Type u) [Finite sigma] :
    IsIrreducible
      (Set.univ : Set (Variety.Point (affineSpaceVariety k sigma))) := by
  let : Nonempty (Variety.Point (affineSpaceVariety k sigma)) :=
    ⟨affineSpacePoint (fun _ => 0)⟩
  apply isIrreducible_univ_of_prime_vanishingIdeal
  rw [affineSpaceVariety_vanishingIdeal_eq_bot]
  exact Ideal.isPrime_bot

private lemma bruhatCellDomain_isIrreducible :
    IsIrreducible
      (Set.univ : Set (Variety.Point (BruhatCellDomain k))) := by
  have hneg := affineSpace_isIrreducible (k := k) BruhatSix
  have hpos := affineSpace_isIrreducible (k := k) BruhatSix
  have ht :
      IsIrreducible
        (Set.univ : Set (Variety.Point (dVariety k 2))) :=
    connectedAlgebraicGroup_irreducible (dVariety k 2)
      (dVariety_isConnected (k := k) 2)
  have hmiddle :
      IsIrreducible
        (Variety.prodSet
          (Set.univ : Set (Variety.Point (dVariety k 2)))
          (Set.univ : Set (Variety.Point (affineSpaceVariety k BruhatSix)))) :=
    prodSet_irreducible_of_irreducible ht hpos
  have hall :
      IsIrreducible
        (Variety.prodSet
          (Set.univ : Set (Variety.Point (affineSpaceVariety k BruhatSix)))
          (Variety.prodSet
            (Set.univ : Set (Variety.Point (dVariety k 2)))
            (Set.univ : Set (Variety.Point (affineSpaceVariety k BruhatSix))))) :=
    prodSet_irreducible_of_irreducible hneg hmiddle
  simpa [BruhatCellDomain, Variety.prodSet] using hall

private theorem affineSpace_dimension (sigma : Type u) [Finite sigma] :
    Variety.dimension (affineSpaceVariety k sigma) = Cardinal.mk sigma := by
  let : Nonempty (Variety.Point (affineSpaceVariety k sigma)) :=
    ⟨affineSpacePoint (fun _ => 0)⟩
  let : IsDomain (coordinateRing (affineSpaceVariety k sigma)) :=
    (Ideal.Quotient.isDomain_iff_prime
      (I := vanishingIdeal (Set.univ : Set
        (Variety.Point (affineSpaceVariety k sigma)) ))).mpr (by
          rw [affineSpaceVariety_vanishingIdeal_eq_bot]
          exact Ideal.isPrime_bot)
  have hirreducible := isIrreducible_univ_of_prime_vanishingIdeal
    (affineSpaceVariety k sigma) (by
      rw [affineSpaceVariety_vanishingIdeal_eq_bot]
      exact Ideal.isPrime_bot)
  rw [dimension_eq_fractionRing_of_isIrreducible
    (affineSpaceVariety k sigma) hirreducible, trdeg_fractionRing_eq]
  change Algebra.trdeg k (MvPolynomial sigma k ⧸
    vanishingIdeal (Set.univ : Set
      (Variety.Point (affineSpaceVariety k sigma)))) = Cardinal.mk sigma
  rw [affineSpaceVariety_vanishingIdeal_eq_bot]
  calc
    Algebra.trdeg k (MvPolynomial sigma k ⧸
        (⊥ : Ideal (MvPolynomial sigma k))) =
        Algebra.trdeg k (MvPolynomial sigma k) :=
      (AlgEquiv.quotientBot k (MvPolynomial sigma k)).trdeg_eq
    _ = Cardinal.mk sigma := by
      simpa only [Cardinal.lift_id] using
        (MvPolynomial.trdeg_of_isDomain :
          Algebra.trdeg k (MvPolynomial sigma k) = Cardinal.lift.{u} #sigma)

private lemma bruhatCellDomain_dimension_eq_fourteen :
    Variety.dimension (BruhatCellDomain k) = 14 := by
  let : Nonempty
      (Variety.Point (affineSpaceVariety k BruhatSix)) :=
    ⟨affineSpacePoint (fun _ => 0)⟩
  let : Nonempty (Variety.Point (dVariety k 2)) :=
    ⟨(dPointEquiv (k := k) 2).symm 1⟩
  let : Nonempty
      (Variety.Point
        (Variety.prod (dVariety k 2) (affineSpaceVariety k BruhatSix))) :=
    ⟨(Variety.prodPointEquiv (dVariety k 2)
        (affineSpaceVariety k BruhatSix)).symm
      ((dPointEquiv (k := k) 2).symm 1, affineSpacePoint (fun _ => 0))⟩
  rw [dimension_product_additive, dimension_product_additive,
    affineSpace_dimension, dVariety_dimension_eq]
  rw [Cardinal.mk_uLift, Cardinal.lift_mk_fin]
  norm_num

omit [IsAlgClosed k] in
private lemma dimension_eq_trdeg_polynomialFunction_of_isIrreducible
    (V : Variety k) (hV : IsIrreducible
      (Set.univ : Set (Variety.Point V))) :
    Variety.dimension V = Algebra.trdeg k (Variety.PolynomialFunction V) := by
  let : IsDomain (coordinateRing V) :=
    isDomain_coordinateRing_of_isIrreducible V hV
  let : IsDomain (Variety.PolynomialFunction V) :=
    (coordinateRingAlgEquivPolynomialFunction V).toRingEquiv.isDomain_iff.mp
      inferInstance
  rw [dimension_eq_fractionRing_of_isIrreducible V hV,
    trdeg_fractionRing_eq]
  exact (coordinateRingAlgEquivPolynomialFunction V).trdeg_eq

omit [IsAlgClosed k] in
private lemma dimension_le_of_dense_morphism
    {U W : Variety k} (f : Variety.Morphism U W)
    (hU : IsIrreducible (Set.univ : Set (Variety.Point U)))
    (hW : IsIrreducible (Set.univ : Set (Variety.Point W)))
    (hf : Dense (Set.range f.toFun)) :
    Variety.dimension W ≤ Variety.dimension U := by
  rw [dimension_eq_trdeg_polynomialFunction_of_isIrreducible W hW,
    dimension_eq_trdeg_polynomialFunction_of_isIrreducible U hU]
  apply trdeg_le_of_injective f.pullbackAlgHom
  intro p q hpq
  rcases p.representedBy with ⟨pp, hpp⟩
  rcases q.representedBy with ⟨qq, hqq⟩
  let Z : Set (Variety.Point W) :=
    {y | evalPolynomial y.val (pp - qq) = 0}
  have hZclosed : IsClosed Z := by
    rw [Variety.isClosed_iff_isZariskiClosed]
    refine ⟨{pp - qq}, ?_⟩
    ext y
    simp [Z]
  have hrange : Set.range f.toFun ⊆ Z := by
    rintro y ⟨x, rfl⟩
    have hxy := congrArg (fun r : Variety.PolynomialFunction U => r x) hpq
    change p (f.toFun x) = q (f.toFun x) at hxy
    have hxy' : evalPolynomial (f.toFun x).val pp =
        evalPolynomial (f.toFun x).val qq := by
      rw [← hpp, ← hqq]
      exact hxy
    simpa [Z, evalPolynomial] using sub_eq_zero.mpr hxy'
  have hcl : closure (Set.range f.toFun) = Set.univ :=
    dense_iff_closure_eq.mp hf
  have hZuniv : Z = Set.univ := by
    apply Set.eq_univ_of_forall
    intro y
    exact closure_minimal hrange hZclosed (by
      rw [hcl]
      exact Set.mem_univ _)
  apply Variety.PolynomialFunction.ext
  intro y
  rw [hpp y, hqq y]
  apply sub_eq_zero.mp
  have hyzero : evalPolynomial y.val (pp - qq) = 0 := by
    have hyZ : y ∈ Z := hZuniv ▸ Set.mem_univ _
    simpa [Z] using hyZ
  simpa [evalPolynomial] using hyzero

private lemma component_dimension_le_fourteen
    (C : {C : Set (Variety.Point (Carrier (k := k))) //
      C ∈ irreducibleComponents (Variety.Point (Carrier (k := k)))}) :
    Variety.componentDimension (Carrier (k := k)) C.1 C.2 ≤ 14 := by
  classical
  let t : Finset (Set (Variety.Point (Carrier (k := k)))) :=
    (Finset.univ : Finset (Fin 12)).image
      (fun j => closure (Set.range
        (bruhatCellMorphism (k := k) j).toFun))
  have htclosed : ∀ Z ∈ t, IsClosed Z := by
    intro Z hZ
    rcases Finset.mem_image.mp hZ with ⟨j, -, rfl⟩
    exact isClosed_closure
  have htcover : C.1 ⊆ ⋃₀ (t : Set (Set (Variety.Point (Carrier (k := k))))) := by
    intro x hx
    obtain ⟨j, z, hz⟩ := carrier_bruhatCell_cover (k := k) x
    refine Set.mem_sUnion_of_mem
      (subset_closure (show x ∈ Set.range
        (bruhatCellMorphism (k := k) j).toFun from ⟨z, hz.symm⟩)) ?_
    exact Finset.mem_coe.mpr
      (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)
  obtain ⟨Z, hZt, hCZ⟩ :=
    isIrreducible_iff_sUnion_isClosed.mp C.2.1 t htclosed htcover
  rcases Finset.mem_image.mp hZt with ⟨j, -, rfl⟩
  let f : Variety.Morphism (BruhatCellDomain k) (Carrier (k := k)) :=
    bruhatCellMorphism (k := k) j
  have hRirr : IsIrreducible (Set.range f.toFun) := by
    simpa only [Set.image_univ] using
      (bruhatCellDomain_isIrreducible.image f.toFun f.continuous.continuousOn)
  have hZirr : IsIrreducible (closure (Set.range f.toFun)) :=
    hRirr.closure
  have hZC : closure (Set.range f.toFun) ⊆ C.1 :=
    irreducible_subset_of_contains_component C.2 hCZ hZirr
  have hclosure : closure (Set.range f.toFun) = C.1 :=
    Set.Subset.antisymm hZC hCZ
  have hCclosed : IsClosed C.1 :=
    isClosed_of_mem_irreducibleComponents C.1 C.2
  let hzC : IsZariskiClosed (Carrier (k := k)) C.1 :=
    Variety.isClosed_iff_isZariskiClosed.mp hCclosed
  let W : Variety k := Variety.closedSubvariety hzC
  let xC : Variety.Point (Carrier (k := k)) :=
    Classical.choose C.2.1.nonempty
  have hxC : xC ∈ C.1 := Classical.choose_spec C.2.1.nonempty
  let : Nonempty (Variety.Point W) :=
    ⟨(Variety.closedSubvarietyPointEquiv hzC).symm ⟨xC, hxC⟩⟩
  have hWdom : IsDomain (coordinateRing W) := by
    simpa [W, hzC] using isDomain_coordinateRing_component C.1 C.2
  have hWirr : IsIrreducible
      (Set.univ : Set (Variety.Point W)) :=
    isIrreducible_univ_of_prime_vanishingIdeal W
      (isPrime_of_isDomain_coordinateRing W hWdom)
  let e : Variety.Point W ≃ₜ
      {x : Variety.Point (Carrier (k := k)) // x ∈ C.1} :=
    Variety.closedSubvarietyPointHomeomorph hzC
  let fC : Variety.Morphism (BruhatCellDomain k) W :=
    { toFun := fun x =>
        (Variety.closedSubvarietyPointEquiv hzC).symm
          ⟨f.toFun x, hZC (subset_closure ⟨x, rfl⟩)⟩
      regular := by
        intro i
        rcases f.regular i with ⟨p, hp⟩
        refine ⟨p, ?_⟩
        intro x
        change (f.toFun x).val i = evalPolynomial x.val p
        exact hp x }
  have heval (x : Variety.Point (BruhatCellDomain k)) :
      Subtype.val (e (fC.toFun x)) = f.toFun x := by
    change ((Variety.closedSubvarietyPointEquiv hzC) (fC.toFun x)).1 =
      f.toFun x
    rfl
  have hval_image :
      Subtype.val '' (e '' Set.range fC.toFun) = Set.range f.toFun := by
    ext y
    constructor
    · intro h
      rcases h with ⟨z, hz, hy⟩
      rcases hz with ⟨w, hw, hzw⟩
      rcases hw with ⟨x, hx⟩
      refine ⟨x, ?_⟩
      calc
        f.toFun x = Subtype.val (e (fC.toFun x)) := (heval x).symm
        _ = Subtype.val (e w) := by rw [hx]
        _ = Subtype.val z := by rw [hzw]
        _ = y := hy
    · rintro ⟨x, rfl⟩
      refine ⟨e (fC.toFun x), ?_, heval x⟩
      exact ⟨fC.toFun x, ⟨x, rfl⟩, rfl⟩
  have hval_closure :
      closure (Subtype.val '' (e '' Set.range fC.toFun)) = C.1 := by
    rw [hval_image, hclosure]
  have hfCdense : Dense (Set.range fC.toFun) := by
    rw [dense_iff_closure_eq]
    apply Set.eq_univ_of_forall
    intro y
    have heydense : e y ∈ closure (e '' Set.range fC.toFun) := by
      rw [closure_subtype, hval_closure]
      exact (e y).property
    rw [e.isClosedEmbedding.closure_image_eq] at heydense
    rcases heydense with
      ⟨z, hz, hzy⟩
    have hzy' : z = y := e.injective hzy
    simpa [hzy'] using hz
  have hdimW : Variety.dimension W ≤
      Variety.dimension (BruhatCellDomain k) :=
    dimension_le_of_dense_morphism fC bruhatCellDomain_isIrreducible hWirr hfCdense
  have hcomp :
      Variety.componentDimension (Carrier (k := k)) C.1 C.2 =
        Variety.dimension W := by
    rw [dimension_eq_fractionRing_of_isIrreducible W hWirr]
    simp [Variety.componentDimension, W]
  rw [hcomp]
  exact hdimW.trans_eq bruhatCellDomain_dimension_eq_fourteen

private lemma carrier_dimension_le_fourteen_cardinal :
    Variety.dimension (Carrier (k := k)) ≤ 14 := by
  unfold Variety.dimension
  apply ciSup_le'
  intro C
  exact component_dimension_le_fourteen C

theorem carrier_dimension_le_fourteen :
    Cardinal.toNat (Variety.dimension (Carrier (k := k))) ≤ 14 := by
  apply (Cardinal.toNat_le_iff_of_lt_aleph0 14
    (variety_dimension_lt_aleph0 (Carrier (k := k)))).2
  exact carrier_dimension_le_fourteen_cardinal

end

end Theory.AlgebraicGroup.G2Chevalley
