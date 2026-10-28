module

public import Mathlib.GroupTheory.SemidirectProduct
public import Theory.AlgebraicGroup.Instance.Finite
public import Theory.AlgebraicGroup.Morphism.Operations
public import Theory.AlgebraicGroup.Product

universe u

/-!
Algebraic actions and semidirect products.
-/

namespace Theory.AlgebraicGroup

open scoped TensorProduct

open LinearMap Submodule

variable {k : Type u} [Field k]

public structure Action (X : Type u) (G : Variety k)
    [Group X] [AlgebraicGroup G] where
  toMulAut : X →* MulAut (Variety.Point G)
  regular : ∀ x : X, ∀ i : G.Coordinates,
    ∃ p : MvPolynomial G.Coordinates k,
      ∀ g : Variety.Point G, (toMulAut x g).val i = evalPolynomial g.val p

/-- An element of an algebraic action as an algebraic-group automorphism. -/
@[expose]
public def Action.morphism {X : Type u} {G : Variety k}
    [Group X] [AlgebraicGroup G] (A : Theory.AlgebraicGroup.Action X G) (x : X) :
    Theory.AlgebraicGroup.Morphism G G where
  toVariety :=
    { toFun := A.toMulAut x
      regular := A.regular x }
  map_one := (A.toMulAut x).map_one
  map_mul := (A.toMulAut x).map_mul

/-- The affine zero locus underlying the semidirect product. -/
public noncomputable abbrev Action.semidirectVariety {X : Type u}
    {G : Variety k} [Finite X] [Group X] [AlgebraicGroup G]
    (_A : Theory.AlgebraicGroup.Action X G) : Variety k :=
  Variety.prod G (finiteGroupVariety k X)

/-- Points of the semidirect-product zero locus as the ordinary semidirect
product. -/
@[expose]
public noncomputable def Action.semidirectPointEquiv {X : Type u}
    {G : Variety k} [Finite X] [Group X] [AlgebraicGroup G]
    (A : Theory.AlgebraicGroup.Action X G) :
    Variety.Point A.semidirectVariety ≃
      SemidirectProduct (Variety.Point G) X A.toMulAut :=
  (Variety.prodPointEquiv G (finiteGroupVariety k X)).trans
    ((Equiv.prodCongr (Equiv.refl (Variety.Point G))
      (finiteGroupPointEquiv (k := k) X)).trans
        SemidirectProduct.equivProd.symm)

/-- The first-coordinate multiplication map for a fixed acting element. -/
@[expose]
public def Action.mulFirstMorphism {X : Type u}
    {G : Variety k} [Group X] [AlgebraicGroup G]
    (A : Theory.AlgebraicGroup.Action X G) (x : X) :
    Variety.Morphism (Variety.prod G G) G :=
  (Theory.AlgebraicGroup.mulMorphism G).comp
    ((Theory.AlgebraicGroup.Morphism.fst G G).toVariety.pair
      ((A.morphism x).toVariety.comp
        (Theory.AlgebraicGroup.Morphism.snd G G).toVariety))

/-- The first-coordinate inversion map on the slice indexed by an acting
element. -/
@[expose]
public def Action.invFirstMorphism {X : Type u}
    {G : Variety k} [Group X] [AlgebraicGroup G]
    (A : Theory.AlgebraicGroup.Action X G) (x : X) : Variety.Morphism G G :=
  (A.morphism x⁻¹).toVariety.comp (Theory.AlgebraicGroup.invMorphism G)

public lemma Action.mulFirstMorphism_apply {X : Type u}
    {G : Variety k} [Group X] [AlgebraicGroup G]
    (A : Theory.AlgebraicGroup.Action X G) (x : X)
    (g h : Variety.Point G) :
    (A.mulFirstMorphism x).toFun
        ((Variety.prodPointEquiv G G).symm (g, h)) =
      g * A.toMulAut x h := by
  simp [Theory.AlgebraicGroup.Action.mulFirstMorphism, Theory.AlgebraicGroup.mulMorphism,
    Theory.AlgebraicGroup.Morphism.fst, Theory.AlgebraicGroup.Morphism.snd,
    Theory.AlgebraicGroup.Action.morphism, Variety.Morphism.comp,
    Variety.Morphism.pair, Variety.prodPointEquiv]

public lemma Action.invFirstMorphism_apply {X : Type u}
    {G : Variety k} [Group X] [AlgebraicGroup G]
    (A : Theory.AlgebraicGroup.Action X G) (x : X) (g : Variety.Point G) :
    (A.invFirstMorphism x).toFun g = A.toMulAut x⁻¹ g⁻¹ := by
  rfl

/-- Multiplication coordinate polynomials for the semidirect product. -/
public noncomputable def Action.semidirectMulPolynomial {X : Type u}
    {G : Variety k} [Finite X] [Group X] [AlgebraicGroup G]
    (A : Theory.AlgebraicGroup.Action X G) :
    (G.Coordinates ⊕ X) →
      MvPolynomial ((G.Coordinates ⊕ X) ⊕ (G.Coordinates ⊕ X)) k := by
  letI := Fintype.ofFinite X
  intro i
  cases i with
  | inl i =>
      exact ∑ x : X, MvPolynomial.X (Sum.inl (Sum.inr x)) *
        MvPolynomial.rename
          (Sum.map (fun j : G.Coordinates ↦
              (Sum.inl j : G.Coordinates ⊕ X))
            (fun j : G.Coordinates ↦
              (Sum.inl j : G.Coordinates ⊕ X)))
          (Classical.choose ((A.mulFirstMorphism x).regular i))
  | inr z =>
      exact MvPolynomial.rename
        (Sum.map (fun x : X ↦ (Sum.inr x : G.Coordinates ⊕ X))
          (fun x : X ↦ (Sum.inr x : G.Coordinates ⊕ X)))
        (finiteGroupMulPolynomial (k := k) X z)

/-- Inversion coordinate polynomials for the semidirect product. -/
public noncomputable def Action.semidirectInvPolynomial {X : Type u}
    {G : Variety k} [Finite X] [Group X] [AlgebraicGroup G]
    (A : Theory.AlgebraicGroup.Action X G) :
    (G.Coordinates ⊕ X) → MvPolynomial (G.Coordinates ⊕ X) k := by
  letI := Fintype.ofFinite X
  intro i
  cases i with
  | inl i =>
      exact ∑ x : X, MvPolynomial.X (Sum.inr x) *
        MvPolynomial.rename Sum.inl
          (Classical.choose ((A.invFirstMorphism x).regular i))
  | inr z =>
      exact MvPolynomial.rename Sum.inr (finiteGroupInvPolynomial (k := k) X z)

private lemma Action.semidirect_mul_regular_on_equiv
    {X : Type u} {G : Variety k} [Finite X] [Group X] [AlgebraicGroup G]
    (A : Theory.AlgebraicGroup.Action X G) (g h : Variety.Point G) (a b : X)
    (i : G.Coordinates ⊕ X) :
    ((A.semidirectPointEquiv).symm
      ((⟨g, a⟩ : SemidirectProduct (Variety.Point G) X A.toMulAut) *
        (⟨h, b⟩ : SemidirectProduct (Variety.Point G) X A.toMulAut))).val i =
      evalPolynomial
        (Sum.elim
          ((A.semidirectPointEquiv).symm
            (⟨g, a⟩ : SemidirectProduct (Variety.Point G) X A.toMulAut)).val
          ((A.semidirectPointEquiv).symm
            (⟨h, b⟩ : SemidirectProduct (Variety.Point G) X A.toMulAut)).val)
        (A.semidirectMulPolynomial i) := by
  classical
  let := Fintype.ofFinite X
  cases i with
  | inl i =>
      rw [SemidirectProduct.mul_def]
      change (g * A.toMulAut a h).val i = _
      have hpoly := Classical.choose_spec
        ((A.mulFirstMorphism a).regular i)
        ((Variety.prodPointEquiv G G).symm (g, h))
      rw [A.mulFirstMorphism_apply] at hpoly
      rw [hpoly]
      rw [Theory.AlgebraicGroup.Action.semidirectMulPolynomial]
      simp only [evalPolynomial_sum]
      rw [Finset.sum_eq_single a]
      · rw [evalPolynomial_mul, evalPolynomial_X]
        simp only [Sum.elim_inl]
        have hselector :
            ((A.semidirectPointEquiv).symm
              (⟨g, a⟩ : SemidirectProduct (Variety.Point G) X A.toMulAut)).val
                (Sum.inr a) = 1 := by
          change (if a = a then 1 else 0) = 1
          simp
        rw [hselector, one_mul, evalPolynomial_rename]
        congr 1
        funext j
        cases j <;> rfl
      · intro c hc hca
        rw [evalPolynomial_mul, evalPolynomial_X]
        simp only [Sum.elim_inl]
        have hselector :
            ((A.semidirectPointEquiv).symm
              (⟨g, a⟩ : SemidirectProduct (Variety.Point G) X A.toMulAut)).val
                (Sum.inr c) = 0 := by
          change (if c = a then 1 else 0) = 0
          simp [hca]
        rw [hselector, zero_mul]
      · simp
  | inr z =>
      rw [SemidirectProduct.mul_def]
      change (finiteGroupPoint (k := k) X (a * b)).val z = _
      rw [← finiteGroupPoint_mul]
      rw [AlgebraicGroup.mul_regular]
      rw [Theory.AlgebraicGroup.Action.semidirectMulPolynomial, evalPolynomial_rename]
      congr 1
      funext j
      cases j <;> rfl

private lemma Action.semidirect_inv_regular_on_equiv
    {X : Type u} {G : Variety k} [Finite X] [Group X] [AlgebraicGroup G]
    (A : Theory.AlgebraicGroup.Action X G) (g : Variety.Point G) (a : X)
    (i : G.Coordinates ⊕ X) :
    ((A.semidirectPointEquiv).symm
      (⟨g, a⟩ : SemidirectProduct (Variety.Point G) X A.toMulAut)⁻¹).val i =
      evalPolynomial
        ((A.semidirectPointEquiv).symm
          (⟨g, a⟩ : SemidirectProduct (Variety.Point G) X A.toMulAut)).val
        (A.semidirectInvPolynomial i) := by
  classical
  let := Fintype.ofFinite X
  cases i with
  | inl i =>
      change
        ((⟨g, a⟩ : SemidirectProduct
          (Variety.Point G) X A.toMulAut)⁻¹).left.val i = _
      rw [SemidirectProduct.inv_left]
      change (A.toMulAut a⁻¹ g⁻¹).val i = _
      have hpoly := Classical.choose_spec ((A.invFirstMorphism a).regular i) g
      rw [A.invFirstMorphism_apply] at hpoly
      rw [hpoly]
      rw [Theory.AlgebraicGroup.Action.semidirectInvPolynomial]
      simp only [evalPolynomial_sum]
      rw [Finset.sum_eq_single a]
      · rw [evalPolynomial_mul, evalPolynomial_X]
        have hselector :
            ((A.semidirectPointEquiv).symm
              (⟨g, a⟩ : SemidirectProduct (Variety.Point G) X A.toMulAut)).val
                (Sum.inr a) = 1 := by
          change (if a = a then 1 else 0) = 1
          simp
        rw [hselector, one_mul, evalPolynomial_rename]
        congr 1
      · intro c hc hca
        rw [evalPolynomial_mul, evalPolynomial_X]
        have hselector :
            ((A.semidirectPointEquiv).symm
              (⟨g, a⟩ : SemidirectProduct (Variety.Point G) X A.toMulAut)).val
                (Sum.inr c) = 0 := by
          change (if c = a then 1 else 0) = 0
          simp [hca]
        rw [hselector, zero_mul]
      · simp
  | inr z =>
      change
        (finiteGroupPoint (k := k) X
          ((⟨g, a⟩ : SemidirectProduct
            (Variety.Point G) X A.toMulAut)⁻¹).right).val z = _
      rw [SemidirectProduct.inv_right]
      change (finiteGroupPoint (k := k) X a⁻¹).val z = _
      rw [← finiteGroupPoint_inv]
      rw [AlgebraicGroup.inv_regular]
      rw [Theory.AlgebraicGroup.Action.semidirectInvPolynomial, evalPolynomial_rename]
      congr 1

/-- The algebraic-group structure on the semidirect product by a finite group of
algebraic automorphisms.  It is explicit rather than a global instance because
the same product zero locus also carries its direct-product group structure. -/
@[expose, reducible]
public noncomputable def Action.semidirectAlgebraicGroup
    {X : Type u} {G : Variety k} [Finite X] [Group X] [AlgebraicGroup G]
    (A : Theory.AlgebraicGroup.Action X G) : AlgebraicGroup A.semidirectVariety := by
  let e := A.semidirectPointEquiv
  let hGroup : Group (Variety.Point A.semidirectVariety) := e.group
  letI : Group (Variety.Point A.semidirectVariety) := hGroup
  exact
    { toGroup := hGroup
      mulPolynomial := A.semidirectMulPolynomial
      invPolynomial := A.semidirectInvPolynomial
      mul_regular := by
        intro i x y
        let u := e x
        let v := e y
        have hx : x = e.symm u := (e.symm_apply_apply x).symm
        have hy : y = e.symm v := (e.symm_apply_apply y).symm
        rw [hx, hy]
        have hmul : e.symm u * e.symm v = e.symm (u * v) := by
          apply e.injective
          change e (e.symm (e (e.symm u) * e (e.symm v))) = e (e.symm (u * v))
          simp
        rw [hmul]
        rcases u with ⟨g, a⟩
        rcases v with ⟨h, b⟩
        exact A.semidirect_mul_regular_on_equiv g h a b i
      inv_regular := by
        intro i x
        let u := e x
        have hx : x = e.symm u := (e.symm_apply_apply x).symm
        rw [hx]
        have hinv : (e.symm u)⁻¹ = e.symm u⁻¹ := by
          apply e.injective
          change e (e.symm (e (e.symm u))⁻¹) = e (e.symm u⁻¹)
          simp
        rw [hinv]
        rcases u with ⟨g, a⟩
        exact A.semidirect_inv_regular_on_equiv g a i }

/-- Projection from the semidirect product to its finite factor. -/
@[expose]
public noncomputable def Action.rightMorphism
    {X : Type u} {G : Variety k} [Finite X] [Group X] [AlgebraicGroup G]
    (A : Theory.AlgebraicGroup.Action X G) :
    @Theory.AlgebraicGroup.Morphism k _ A.semidirectVariety
      (finiteGroupVariety k X) A.semidirectAlgebraicGroup
      (Theory.AlgebraicGroup.finiteGroup X) := by
  letI : AlgebraicGroup A.semidirectVariety := A.semidirectAlgebraicGroup
  let eMul := Equiv.mulEquiv A.semidirectPointEquiv
  let finiteHom : X →* Variety.Point (finiteGroupVariety k X) :=
    (Equiv.mulEquiv (finiteGroupPointEquiv (k := k) X)).symm.toMonoidHom
  let pointHom : Variety.Point A.semidirectVariety →*
      Variety.Point (finiteGroupVariety k X) :=
    finiteHom.comp (SemidirectProduct.rightHom.comp eMul.toMonoidHom)
  exact
    { toVariety :=
        { toFun := pointHom
          regular := by
            intro z
            refine ⟨MvPolynomial.X (Sum.inr z), ?_⟩
            intro p
            rw [evalPolynomial_X]
            have hp := A.semidirectPointEquiv.symm_apply_apply p
            exact congrArg (fun q : Variety.Point A.semidirectVariety ↦
              q.val (Sum.inr z)) hp }
      map_one := pointHom.map_one
      map_mul := pointHom.map_mul }

/-- The canonical morphism from the base group into the semidirect product. -/
@[expose]
public noncomputable def Action.baseMorphism
    {X : Type u} {G : Variety k} [Finite X] [Group X] [AlgebraicGroup G]
    (A : Theory.AlgebraicGroup.Action X G) :
    @Theory.AlgebraicGroup.Morphism k _ G A.semidirectVariety
      (inferInstance : AlgebraicGroup G) A.semidirectAlgebraicGroup := by
  letI : AlgebraicGroup A.semidirectVariety := A.semidirectAlgebraicGroup
  let eMul := Equiv.mulEquiv A.semidirectPointEquiv
  let pointHom : Variety.Point G →* Variety.Point A.semidirectVariety :=
    eMul.symm.toMonoidHom.comp SemidirectProduct.inl
  exact
    { toVariety :=
        { toFun := pointHom
          regular := by
            intro i
            cases i with
            | inl i =>
                exact ⟨MvPolynomial.X i, fun g ↦ by
                  rw [evalPolynomial_X]
                  change
                    ((A.semidirectPointEquiv).symm
                      (⟨g, 1⟩ : SemidirectProduct
                        (Variety.Point G) X A.toMulAut)).val (Sum.inl i) = g.val i
                  rfl⟩
            | inr z =>
                exact ⟨MvPolynomial.C
                    ((finiteGroupPoint (k := k) X 1).val z), fun g ↦ by
                  change
                    ((A.semidirectPointEquiv).symm
                      (⟨g, 1⟩ : SemidirectProduct
                        (Variety.Point G) X A.toMulAut)).val (Sum.inr z) =
                      evalPolynomial g.val
                        (MvPolynomial.C
                          ((finiteGroupPoint (k := k) X 1).val z))
                  rw [show evalPolynomial g.val
                    (MvPolynomial.C ((finiteGroupPoint (k := k) X 1).val z)) =
                      (finiteGroupPoint (k := k) X 1).val z by
                        simp [evalPolynomial]]
                  rfl⟩ }
      map_one := pointHom.map_one
      map_mul := pointHom.map_mul }

end Theory.AlgebraicGroup
