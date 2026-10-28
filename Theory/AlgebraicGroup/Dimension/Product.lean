module

public import Theory.AlgebraicGroup.Irreducible.Product

universe u

/-! Dimension and irreducible-component behavior of products of affine varieties. -/

namespace Theory.AlgebraicGroup

open scoped TensorProduct Cardinal

open LinearMap Submodule

variable {k : Type u} [Field k]

public theorem tensorProduct_trdeg_add
    (k A B : Type u) [Field k] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] [IsDomain A] [IsDomain B]
    [IsDomain (A ⊗[k] B)] :
    Algebra.trdeg k (A ⊗[k] B) =
      Algebra.trdeg k A + Algebra.trdeg k B := by
  let C := A ⊗[k] B
  let : Algebra A C := Algebra.TensorProduct.leftAlgebra
  have : IsScalarTower k A C := inferInstance
  have hAfaithful : FaithfulSMul k A :=
    (faithfulSMul_iff_algebraMap_injective (R := k) (A := A)).mpr
      (algebraMap k A).injective
  let : FaithfulSMul k A := hAfaithful
  have hCfaithful : FaithfulSMul A C :=
    (faithfulSMul_iff_algebraMap_injective (R := A) (A := C)).mpr
      (Algebra.TensorProduct.includeLeft_injective
        (R := k) (S := A) (A := A) (B := B) (algebraMap k B).injective)
  let : FaithfulSMul A C := hCfaithful
  obtain ⟨J, y, hy⟩ := exists_isTranscendenceBasis' k B
  let yC : J → C := fun j ↦ Algebra.TensorProduct.includeRight (y j)
  have hyC_ind : AlgebraicIndependent A yC := by
    rw [algebraicIndependent_iff_injective_aeval]
    let e : A ⊗[k] MvPolynomial J k ≃ₐ[A] MvPolynomial J A :=
      MvPolynomial.algebraTensorAlgEquiv k A
    let F : A ⊗[k] MvPolynomial J k →ₐ[A] C :=
      Algebra.TensorProduct.map (AlgHom.id A A) (MvPolynomial.aeval y)
    have hyinj : Function.Injective (MvPolynomial.aeval y) :=
      algebraicIndependent_iff_injective_aeval.mp hy.1
    have hFinj : Function.Injective F := by
      exact TensorProduct.map_injective_of_flat_flat
        ((AlgHom.id A A).toLinearMap.restrictScalars k)
        (MvPolynomial.aeval y).toLinearMap Function.injective_id hyinj
    have hcomp : MvPolynomial.aeval yC = F.comp e.symm.toAlgHom := by
      ext j
      simp only [MvPolynomial.aeval_X, AlgHom.comp_apply]
      change (1 ⊗ₜ[k] y j : C) =
        F ((MvPolynomial.algebraTensorAlgEquiv k A).symm (MvPolynomial.X j))
      rw [MvPolynomial.algebraTensorAlgEquiv_symm_X]
      rw [Algebra.TensorProduct.map_tmul]
      simp
    rw [hcomp]
    exact hFinj.comp e.symm.injective
  let D : Subalgebra A C := Algebra.adjoin A (Set.range yC)
  have hyC_alg : Algebra.IsAlgebraic D C := by
    refine ⟨fun z ↦ ?_⟩
    induction z using TensorProduct.induction_on with
    | zero => exact isAlgebraic_zero
    | tmul a b =>
        have ha : IsAlgebraic D (algebraMap A C a) := by
          simpa using isAlgebraic_algebraMap (R := D) (A := C)
            (⟨algebraMap A C a, D.algebraMap_mem a⟩ : D)
        let By : Subalgebra k B := Algebra.adjoin k (Set.range y)
        let f0 : By →ₐ[k] C :=
          (Algebra.TensorProduct.includeRight : B →ₐ[k] C).comp By.val
        have hf0 : ∀ b : By, f0 b ∈ D := by
          intro b'
          refine Algebra.adjoin_induction
            (p := fun b _ ↦ f0 ⟨b, by assumption⟩ ∈ D) ?_ ?_ ?_ ?_ b'.2
          · intro b hb
            rcases hb with ⟨j, rfl⟩
            exact Algebra.subset_adjoin ⟨j, rfl⟩
          · intro r
            change f0 (algebraMap k By r) ∈ D
            rw [f0.commutes r]
            rw [show algebraMap k C r = algebraMap A C (algebraMap k A r) from rfl]
            exact D.algebraMap_mem _
          · intro x x' hx hx' hmx hmx'
            change f0 (⟨x, hx⟩ + ⟨x', hx'⟩) ∈ D
            rw [map_add]
            exact D.add_mem hmx hmx'
          · intro x x' hx hx' hmx hmx'
            change f0 (⟨x, hx⟩ * ⟨x', hx'⟩) ∈ D
            rw [map_mul]
            exact D.mul_mem hmx hmx'
        let f : By →+* D := RingHom.codRestrict f0.toRingHom D hf0
        have hf : Function.Injective f := by
          intro x x' hxx'
          apply Subtype.ext
          apply Algebra.TensorProduct.includeRight_injective (algebraMap k A).injective
          exact congrArg Subtype.val hxx'
        have hcomp : RingHom.comp (algebraMap D C) f =
            RingHom.comp Algebra.TensorProduct.includeRight.toRingHom
              (algebraMap By B) := by
          ext x
          rfl
        have hb0 : IsAlgebraic By b := hy.isAlgebraic.1 b
        have hb : IsAlgebraic D (Algebra.TensorProduct.includeRight b : C) :=
          hb0.ringHom_of_comp_eq f Algebra.TensorProduct.includeRight.toRingHom
            hf hcomp
        simpa [C, Algebra.TensorProduct.includeLeft_apply,
          Algebra.TensorProduct.includeRight_apply] using ha.mul hb
    | add x z hx hz => exact hx.add hz
  have hyC : IsTranscendenceBasis A yC :=
    isTranscendenceBasis_iff_algebraicIndependent_isAlgebraic.mpr
      ⟨hyC_ind, hyC_alg⟩
  have hrel : Algebra.trdeg A C = Algebra.trdeg k B := by
    rw [← hyC.cardinalMk_eq_trdeg, ← hy.cardinalMk_eq_trdeg]
  have hadd : Algebra.trdeg k A + Algebra.trdeg A C = Algebra.trdeg k C :=
    trdeg_add_eq k A
  rw [hrel] at hadd
  simpa [C] using hadd.symm

/-! ## Irreducible components of products -/

/-- A product of irreducible components is an irreducible component of the
affine product. -/
public theorem prodSet_mem_irreducibleComponents {V W : Variety k}
    {C : Set (Variety.Point V)} {D : Set (Variety.Point W)}
    (hC : C ∈ irreducibleComponents (Variety.Point V))
    (hD : D ∈ irreducibleComponents (Variety.Point W)) :
    Variety.prodSet C D ∈ irreducibleComponents
      (Variety.Point (Variety.prod V W)) := by
  let f := Variety.Morphism.fst V W
  let g := Variety.Morphism.snd V W
  refine ⟨prodSet_irreducible_of_irreducible hC.1 hD.1, ?_⟩
  intro Z hZ hprodZ
  have hfZ : IsIrreducible (f.toFun '' Z) :=
    hZ.image f.toFun f.continuous.continuousOn
  have hgZ : IsIrreducible (g.toFun '' Z) :=
    hZ.image g.toFun g.continuous.continuousOn
  have hCfZ : C ⊆ f.toFun '' Z := by
    rcases hD.1.1 with ⟨y, hyD⟩
    intro x hxC
    let z : Variety.Point (Variety.prod V W) :=
      (Variety.prodPointEquiv V W).symm (x, y)
    refine ⟨z, hprodZ ?_, ?_⟩
    · change (Variety.prodPointEquiv V W z).1 ∈ C ∧
        (Variety.prodPointEquiv V W z).2 ∈ D
      simpa [z] using And.intro hxC hyD
    · simp [f, z, Variety.Morphism.fst]
  have hDgZ : D ⊆ g.toFun '' Z := by
    rcases hC.1.1 with ⟨x, hxC⟩
    intro y hyD
    let z : Variety.Point (Variety.prod V W) :=
      (Variety.prodPointEquiv V W).symm (x, y)
    refine ⟨z, hprodZ ?_, ?_⟩
    · change (Variety.prodPointEquiv V W z).1 ∈ C ∧
        (Variety.prodPointEquiv V W z).2 ∈ D
      simpa [z] using And.intro hxC hyD
    · simp [g, z, Variety.Morphism.snd]
  have hfC : f.toFun '' Z ⊆ C :=
    irreducible_subset_of_contains_component hC hCfZ hfZ
  have hgD : g.toFun '' Z ⊆ D :=
    irreducible_subset_of_contains_component hD hDgZ hgZ
  intro z hz
  exact ⟨hfC ⟨z, hz, rfl⟩, hgD ⟨z, hz, rfl⟩⟩

/-- Every irreducible component of an affine product is the product of a
component of each factor. -/
public theorem exists_eq_prodSet_of_mem_irreducibleComponents {V W : Variety k}
    {Z : Set (Variety.Point (Variety.prod V W))}
    (hZ : Z ∈ irreducibleComponents (Variety.Point (Variety.prod V W))) :
    ∃ C : Set (Variety.Point V),
      C ∈ irreducibleComponents (Variety.Point V) ∧
      ∃ D : Set (Variety.Point W),
        D ∈ irreducibleComponents (Variety.Point W) ∧
        Z = Variety.prodSet C D := by
  let f := Variety.Morphism.fst V W
  let g := Variety.Morphism.snd V W
  have hfZ : IsIrreducible (f.toFun '' Z) :=
    hZ.1.image f.toFun f.continuous.continuousOn
  have hgZ : IsIrreducible (g.toFun '' Z) :=
    hZ.1.image g.toFun g.continuous.continuousOn
  rcases exists_mem_irreducibleComponents_subset_of_isIrreducible
      (f.toFun '' Z) hfZ with ⟨C, hC, hfC⟩
  rcases exists_mem_irreducibleComponents_subset_of_isIrreducible
      (g.toFun '' Z) hgZ with ⟨D, hD, hgD⟩
  refine ⟨C, hC, D, hD, ?_⟩
  have hZprod : Z ⊆ Variety.prodSet C D := by
    intro z hz
    change (Variety.prodPointEquiv V W z).1 ∈ C ∧
      (Variety.prodPointEquiv V W z).2 ∈ D
    exact ⟨hfC ⟨z, hz, rfl⟩, hgD ⟨z, hz, rfl⟩⟩
  have hprodZ : Variety.prodSet C D ⊆ Z :=
    irreducible_subset_of_contains_component hZ hZprod
      (prodSet_irreducible_of_irreducible hC.1 hD.1)
  exact Set.eq_of_subset_of_subset hZprod hprodZ

/-- The closed subvariety cut out by a product of closed point sets has the
same rational points, with the same coordinates, as the product of the two
closed subvarieties. -/
@[expose]
public noncomputable def Variety.closedSubvarietyProdSetPointEquiv
    {V W : Variety k} {C : Set (Variety.Point V)} {D : Set (Variety.Point W)}
    (hC : IsZariskiClosed V C) (hD : IsZariskiClosed W D)
    (hP : IsZariskiClosed (Variety.prod V W) (Variety.prodSet C D)) :
    Variety.Point (Variety.closedSubvariety hP) ≃
      Variety.Point (Variety.prod (Variety.closedSubvariety hC)
        (Variety.closedSubvariety hD)) where
  toFun := fun z ↦ by
    let zp := Variety.closedSubvarietyPointEquiv hP z
    let xy := Variety.prodPointEquiv V W zp.1
    exact (Variety.prodPointEquiv (Variety.closedSubvariety hC)
      (Variety.closedSubvariety hD)).symm
        ((Variety.closedSubvarietyPointEquiv hC).symm ⟨xy.1, zp.2.1⟩,
          (Variety.closedSubvarietyPointEquiv hD).symm ⟨xy.2, zp.2.2⟩)
  invFun := fun z ↦ by
    let xy := Variety.prodPointEquiv (Variety.closedSubvariety hC)
      (Variety.closedSubvariety hD) z
    let x := Variety.closedSubvarietyPointEquiv hC xy.1
    let y := Variety.closedSubvarietyPointEquiv hD xy.2
    let p := (Variety.prodPointEquiv V W).symm (x.1, y.1)
    have hp : p ∈ Variety.prodSet C D := by
      change (Variety.prodPointEquiv V W p).1 ∈ C ∧
        (Variety.prodPointEquiv V W p).2 ∈ D
      simp [p, x, y]
    exact (Variety.closedSubvarietyPointEquiv hP).symm ⟨p, hp⟩
  left_inv := by
    intro z
    apply Variety.Point.ext
    funext i
    cases i <;> rfl
  right_inv := by
    intro z
    apply Variety.Point.ext
    funext i
    cases i <;> rfl

public theorem Variety.closedSubvarietyProdSetPointEquiv_val
    {V W : Variety k} {C : Set (Variety.Point V)} {D : Set (Variety.Point W)}
    (hC : IsZariskiClosed V C) (hD : IsZariskiClosed W D)
    (hP : IsZariskiClosed (Variety.prod V W) (Variety.prodSet C D))
    (z : Variety.Point (Variety.closedSubvariety hP)) :
    (Variety.closedSubvarietyProdSetPointEquiv hC hD hP z).val = z.val := by
  funext i
  cases i <;> rfl

public theorem Variety.closedSubvarietyProdSetPointEquiv_symm_val
    {V W : Variety k} {C : Set (Variety.Point V)} {D : Set (Variety.Point W)}
    (hC : IsZariskiClosed V C) (hD : IsZariskiClosed W D)
    (hP : IsZariskiClosed (Variety.prod V W) (Variety.prodSet C D))
    (z : Variety.Point (Variety.prod (Variety.closedSubvariety hC)
      (Variety.closedSubvariety hD))) :
    ((Variety.closedSubvarietyProdSetPointEquiv hC hD hP).symm z).val = z.val := by
  have h := Variety.closedSubvarietyProdSetPointEquiv_val hC hD hP
    ((Variety.closedSubvarietyProdSetPointEquiv hC hD hP).symm z)
  simpa using h.symm

/-- The two presentations of a product of closed subvarieties have the same
vanishing ideal. -/
public theorem vanishingIdeal_closedSubvariety_prodSet_eq
    {V W : Variety k} {C : Set (Variety.Point V)} {D : Set (Variety.Point W)}
    (hC : IsZariskiClosed V C) (hD : IsZariskiClosed W D)
    (hP : IsZariskiClosed (Variety.prod V W) (Variety.prodSet C D)) :
    vanishingIdeal (Set.univ : Set (Variety.Point (Variety.closedSubvariety hP))) =
      vanishingIdeal (Set.univ : Set (Variety.Point
        (Variety.prod (Variety.closedSubvariety hC)
          (Variety.closedSubvariety hD)))) := by
  ext p
  constructor
  · intro hp z hz
    have hzero := hp ((Variety.closedSubvarietyProdSetPointEquiv hC hD hP).symm z)
      (Set.mem_univ _)
    rw [Variety.closedSubvarietyProdSetPointEquiv_symm_val] at hzero
    exact hzero
  · intro hp z hz
    have hzero := hp (Variety.closedSubvarietyProdSetPointEquiv hC hD hP z)
      (Set.mem_univ _)
    rw [Variety.closedSubvarietyProdSetPointEquiv_val] at hzero
    exact hzero

/-- The coordinate ring of the closed product set is the coordinate ring of
the product of the two closed subvarieties. -/
public noncomputable def coordinateRing_closedSubvariety_prodSet_algEquiv
    {V W : Variety k} {C : Set (Variety.Point V)} {D : Set (Variety.Point W)}
    (hC : IsZariskiClosed V C) (hD : IsZariskiClosed W D)
    (hP : IsZariskiClosed (Variety.prod V W) (Variety.prodSet C D)) :
    coordinateRing (Variety.closedSubvariety hP) ≃ₐ[k]
      coordinateRing (Variety.prod (Variety.closedSubvariety hC)
        (Variety.closedSubvariety hD)) := by
  unfold coordinateRing
  rw [vanishingIdeal_closedSubvariety_prodSet_eq hC hD hP]

/-- The transcendence degree over `k` of the fraction ring of a domain equals
the transcendence degree of the domain itself (the fraction ring is algebraic
over the domain, and trdeg is additive along algebraic towers). -/
public theorem trdeg_fractionRing_eq (R : Type u) [CommRing R] [Algebra k R]
    [IsDomain R] :
    Algebra.trdeg k (FractionRing R) = Algebra.trdeg k R := by
  have hAlg : Algebra.IsAlgebraic R (FractionRing R) := by
    rw [Algebra.isAlgebraic_def]
    intro x
    rcases (IsLocalization.mk'_surjective (R := R) (M := nonZeroDivisors R)
        (S := FractionRing R)) x with ⟨⟨a, s⟩, hx⟩
    refine ⟨Polynomial.C (s.1 : R) * Polynomial.X - Polynomial.C a, ?ne, ?root⟩
    · intro hp
      have hs0 : (s.1 : R) ≠ 0 := nonZeroDivisors.coe_ne_zero s
      have hc : (Polynomial.C (s.1 : R) * Polynomial.X - Polynomial.C a).coeff 1 = s.1 := by
        simp
      exact hs0 (by rw [← hc]; exact congrArg (fun q : Polynomial R => q.coeff 1) hp)
    · rw [← hx]
      simp only [map_sub, map_mul]
      rw [Polynomial.aeval_C, Polynomial.aeval_X]
      rw [Polynomial.aeval_C]
      have hmul : (algebraMap R (FractionRing R) (s.1 : R)) *
          IsLocalization.mk' (FractionRing R) a s = algebraMap R (FractionRing R) a := by
        exact IsLocalization.mk'_spec' (R := R) (M := nonZeroDivisors R) (S := FractionRing R) a s
      rw [hmul, sub_self]
  have hfaithful1 : FaithfulSMul k R := by
    refine (faithfulSMul_iff_algebraMap_injective (R := k) (A := R)).mpr ?_
    rw [injective_iff_map_eq_zero]
    intro a ha
    by_contra h
    have hmul : algebraMap k R (a * a⁻¹) = (0 : R) := by
      rw [map_mul, ha, zero_mul]
    have h1 : (1 : R) = 0 := by
      rw [mul_inv_cancel₀ h] at hmul
      simpa only [map_one] using hmul
    exact one_ne_zero h1
  have hfaithful2 : FaithfulSMul R (FractionRing R) := by
    refine (faithfulSMul_iff_algebraMap_injective (R := R) (A := FractionRing R)).mpr ?_
    exact IsFractionRing.injective R (FractionRing R)
  have htrdeg : Algebra.trdeg k R + Algebra.trdeg R (FractionRing R) =
      Algebra.trdeg k (FractionRing R) := by
    exact trdeg_add_eq (R := k) (S := R) (A := FractionRing R)
  have htrdeg0 : Algebra.trdeg R (FractionRing R) = 0 := by
    exact trdeg_eq_zero (R := R) (A := FractionRing R)
  rw [← htrdeg, htrdeg0, add_zero]

/-- The dimension of a product component is the sum of the dimensions of its
two factor components. -/
public theorem componentDimension_prodSet {V W : Variety k}
    {C : Set (Variety.Point V)} {D : Set (Variety.Point W)}
    (hC : C ∈ irreducibleComponents (Variety.Point V))
    (hD : D ∈ irreducibleComponents (Variety.Point W)) :
    Variety.componentDimension (Variety.prod V W) (Variety.prodSet C D)
        (prodSet_mem_irreducibleComponents hC hD) =
      Variety.componentDimension V C hC + Variety.componentDimension W D hD := by
  let hzC : IsZariskiClosed V C := Variety.isClosed_iff_isZariskiClosed.mp
    (isClosed_of_mem_irreducibleComponents C hC)
  let hzD : IsZariskiClosed W D := Variety.isClosed_iff_isZariskiClosed.mp
    (isClosed_of_mem_irreducibleComponents D hD)
  let hP := prodSet_mem_irreducibleComponents hC hD
  let hzP : IsZariskiClosed (Variety.prod V W) (Variety.prodSet C D) :=
    Variety.isClosed_iff_isZariskiClosed.mp
      (isClosed_of_mem_irreducibleComponents (Variety.prodSet C D) hP)
  let A := Variety.closedSubvariety hzC
  let B := Variety.closedSubvariety hzD
  let P := Variety.closedSubvariety hzP
  let : IsDomain (coordinateRing A) := by
    simpa [A, hzC] using isDomain_coordinateRing_component C hC
  let : IsDomain (coordinateRing B) := by
    simpa [B, hzD] using isDomain_coordinateRing_component D hD
  let : IsDomain (coordinateRing P) := by
    simpa [P, hzP, hP] using
      isDomain_coordinateRing_component (Variety.prodSet C D) hP
  let eClosed : coordinateRing P ≃ₐ[k]
      coordinateRing (Variety.prod A B) := by
    simpa [P, A, B] using
      coordinateRing_closedSubvariety_prodSet_algEquiv hzC hzD hzP
  let : IsDomain (coordinateRing (Variety.prod A B)) :=
    eClosed.toRingEquiv.isDomain_iff.mp inferInstance
  let eProd := coordinateRing_prod_equiv_tensorProduct A B
  let : IsDomain (coordinateRing A ⊗[k] coordinateRing B) :=
    eProd.toRingEquiv.isDomain_iff.mpr inferInstance
  change Algebra.trdeg k (FractionRing (coordinateRing P)) =
    Algebra.trdeg k (FractionRing (coordinateRing A)) +
      Algebra.trdeg k (FractionRing (coordinateRing B))
  calc
    Algebra.trdeg k (FractionRing (coordinateRing P)) =
        Algebra.trdeg k (coordinateRing P) := trdeg_fractionRing_eq _
    _ = Algebra.trdeg k (coordinateRing (Variety.prod A B)) := eClosed.trdeg_eq
    _ = Algebra.trdeg k (coordinateRing A ⊗[k] coordinateRing B) :=
      eProd.trdeg_eq.symm
    _ = Algebra.trdeg k (coordinateRing A) + Algebra.trdeg k (coordinateRing B) :=
      tensorProduct_trdeg_add k (coordinateRing A) (coordinateRing B)
    _ = Algebra.trdeg k (FractionRing (coordinateRing A)) +
        Algebra.trdeg k (FractionRing (coordinateRing B)) := by
      rw [trdeg_fractionRing_eq, trdeg_fractionRing_eq]

/-- Proposition 1.1.6(f): dimensions add under direct products. -/
public theorem dimension_product_additive (V W : Variety k)
    [Nonempty (Variety.Point V)] [Nonempty (Variety.Point W)] :
    Variety.dimension (Variety.prod V W) =
      Variety.dimension V + Variety.dimension W := by
  classical
  let IV := {C : Set (Variety.Point V) //
    C ∈ irreducibleComponents (Variety.Point V)}
  let IW := {D : Set (Variety.Point W) //
    D ∈ irreducibleComponents (Variety.Point W)}
  let IP := {Z : Set (Variety.Point (Variety.prod V W)) //
    Z ∈ irreducibleComponents (Variety.Point (Variety.prod V W))}
  let : Nonempty IV := by
    let x := Classical.choice (inferInstance : Nonempty (Variety.Point V))
    exact ⟨⟨irreducibleComponent x,
      irreducibleComponent_mem_irreducibleComponents x⟩⟩
  let : Nonempty IW := by
    let y := Classical.choice (inferInstance : Nonempty (Variety.Point W))
    exact ⟨⟨irreducibleComponent y,
      irreducibleComponent_mem_irreducibleComponents y⟩⟩
  let f : IV → Cardinal := fun C ↦ Variety.componentDimension V C.1 C.2
  let g : IW → Cardinal := fun D ↦ Variety.componentDimension W D.1 D.2
  let q : IP → Cardinal := fun Z ↦
    Variety.componentDimension (Variety.prod V W) Z.1 Z.2
  have hf : BddAbove (Set.range f) := ⟨#(V.Coordinates), by
    intro x hx
    rcases hx with ⟨C, rfl⟩
    exact componentDimension_le_coordinates V C.1 C.2⟩
  have hg : BddAbove (Set.range g) := ⟨#(W.Coordinates), by
    intro x hx
    rcases hx with ⟨D, rfl⟩
    exact componentDimension_le_coordinates W D.1 D.2⟩
  have hq : BddAbove (Set.range q) :=
    ⟨#((Variety.prod V W).Coordinates), by
      intro x hx
      rcases hx with ⟨Z, rfl⟩
      exact componentDimension_le_coordinates (Variety.prod V W) Z.1 Z.2⟩
  change (⨆ Z : IP, q Z) = (⨆ C : IV, f C) + (⨆ D : IW, g D)
  apply le_antisymm
  · apply ciSup_le'
    intro Z
    rcases exists_eq_prodSet_of_mem_irreducibleComponents Z.2 with
      ⟨C, hC, D, hD, hZ⟩
    have hcomp := componentDimension_prodSet hC hD
    have hCf : f ⟨C, hC⟩ ≤ ⨆ C : IV, f C := le_ciSup hf ⟨C, hC⟩
    have hDg : g ⟨D, hD⟩ ≤ ⨆ D : IW, g D := le_ciSup hg ⟨D, hD⟩
    calc
      q Z = f ⟨C, hC⟩ + g ⟨D, hD⟩ := by
        simpa [q, f, g, hZ] using hcomp
      _ ≤ (⨆ C : IV, f C) + (⨆ D : IW, g D) := add_le_add hCf hDg
  · rw [Cardinal.ciSup_add_ciSup f hf g hg]
    apply ciSup_le'
    intro C
    apply ciSup_le'
    intro D
    let Z : IP := ⟨Variety.prodSet C.1 D.1,
      prodSet_mem_irreducibleComponents C.2 D.2⟩
    calc
      f C + g D = q Z := by
        simpa [f, g, q, Z] using (componentDimension_prodSet C.2 D.2).symm
      _ ≤ ⨆ Z : IP, q Z := le_ciSup hq Z

end Theory.AlgebraicGroup
