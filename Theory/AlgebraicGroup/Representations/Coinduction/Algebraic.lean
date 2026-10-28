module

public import Mathlib.RepresentationTheory.FiniteIndex
public import Theory.AlgebraicGroup.ClosedSubgroup.FiniteIndex
public import Theory.AlgebraicGroup.Representations.Coinduction.RightQuotient
public import Theory.AlgebraicGroup.Representations.Matrix

universe u v w

set_option linter.style.haveILetI false

/-! Regular finite-index coinduction for algebraic-group representations. -/

/-! Matrix blocks of the transported coinduced representation. -/

open Representation
namespace Theory.AlgebraicGroup

section
variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
public lemma ClosedSubgroup.coindRightQuotient_matrixCoefficient_of_ne
    {G : Variety k} [AlgebraicGroup G]
    (K : ClosedSubgroup G) [K.toSubgroup.FiniteIndex]
    [Fintype (Quotient (QuotientGroup.rightRel K.toSubgroup))]
    (n : ℕ) (ρ : AlgebraicGroup.Morphism K.carrierVariety (glVariety n : Variety k))
    (g : Variety.Point G)
    (q r : Quotient (QuotientGroup.rightRel K.toSubgroup)) (i j : Fin n)
    (h : @Quotient.mk' _ (QuotientGroup.rightRel K.toSubgroup) (q.out * g) ≠ r) :
    letI := QuotientGroup.rightRel K.toSubgroup
    let A := Rep.of (K.generalLinearMorphismRepresentation n ρ)
    let b := Pi.basis (fun _ : Quotient (QuotientGroup.rightRel K.toSubgroup) =>
      Pi.basisFun k (Fin n))
    b.repr (Representation.coindRightQuotient K.toSubgroup A g (b ⟨r,j⟩)) ⟨q,i⟩ = 0 := by
  classical
  dsimp only
  simp only [Pi.basis_repr]
  rw [Representation.coindRightQuotient_apply]
  simp only [Pi.basis_apply]
  have hne : r ≠ @Quotient.mk' _ (QuotientGroup.rightRel K.toSubgroup)
      (q.out * g) := fun hr => h hr.symm
  simp [hne]

end

/-! Matrix blocks of the transported coinduced representation. -/

open Representation
section
variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
public lemma ClosedSubgroup.coindRightQuotient_matrixCoefficient_of_eq
    {G : Variety k} [AlgebraicGroup G]
    (K : ClosedSubgroup G) [K.toSubgroup.FiniteIndex]
    [Fintype (Quotient (QuotientGroup.rightRel K.toSubgroup))]
    (n : ℕ) (ρ : AlgebraicGroup.Morphism K.carrierVariety (glVariety n : Variety k))
    (g : Variety.Point G)
    (q r : Quotient (QuotientGroup.rightRel K.toSubgroup)) (i j : Fin n)
    (h : @Quotient.mk' _ (QuotientGroup.rightRel K.toSubgroup) (q.out * g) = r) :
    letI := QuotientGroup.rightRel K.toSubgroup
    let A := Rep.of (K.generalLinearMorphismRepresentation n ρ)
    let b := Pi.basis (fun _ : Quotient (QuotientGroup.rightRel K.toSubgroup) =>
      Pi.basisFun k (Fin n))
    b.repr (Representation.coindRightQuotient K.toSubgroup A g (b ⟨r,j⟩)) ⟨q,i⟩ =
      (ρ.onPoints (K.pointEquiv.symm
        (Subgroup.rightCosetCorrection K.toSubgroup (q.out * g)))).val
        (Sum.inl (i,j)) := by
  classical
  dsimp only
  simp only [Pi.basis_repr]
  rw [Representation.coindRightQuotient_apply]
  simp only [Pi.basis_apply]
  have hval :
      (Pi.single r ((Pi.basisFun k (Fin n)) j) :
        Quotient (QuotientGroup.rightRel K.toSubgroup) → (Fin n → k))
          (@Quotient.mk' _ (QuotientGroup.rightRel K.toSubgroup) (q.out * g)) =
        (Pi.basisFun k (Fin n)) j := by
    simp [h]
  rw [hval]
  apply K.generalLinearMorphismRepresentation_matrixCoefficient

end

/-! Ambient polynomial extensions of translated subgroup matrix coordinates. -/

section
variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
public lemma ClosedSubgroup.translatedGeneralLinearCoordinate_extension_exists
    {G : Variety k} [AlgebraicGroup G]
    (K : ClosedSubgroup G) [K.toSubgroup.FiniteIndex]
    (n : ℕ) (ρ : AlgebraicGroup.Morphism K.carrierVariety (glVariety n : Variety k))
    (q r : Quotient (QuotientGroup.rightRel K.toSubgroup)) (i j : Fin n) :
    ∃ f : G.PolynomialFunction, ∀ g,
      @Quotient.mk' _ (QuotientGroup.rightRel K.toSubgroup) (q.out * g) = r →
      f g = (ρ.onPoints (K.pointEquiv.symm
        (Subgroup.rightCosetCorrection K.toSubgroup (q.out * g)))).val
          (Sum.inl (i, j)) := by
  classical
  let coordinate : (glVariety n : Variety k).PolynomialFunction :=
    Variety.PolynomialFunction.ofPolynomial (glVariety n : Variety k)
      (MvPolynomial.X (Sum.inl (i, j)))
  let onK : K.carrierVariety.PolynomialFunction :=
    Variety.PolynomialFunction.pullback ρ.toVariety coordinate
  obtain ⟨ambient, hambient⟩ := K.exists_polynomialFunction_extension onK
  let translate : Variety.Morphism G G :=
    (AlgebraicGroup.rightMulMorphism G r.out⁻¹).comp
      (AlgebraicGroup.leftMulMorphism G q.out)
  let f : G.PolynomialFunction :=
    Variety.PolynomialFunction.pullback translate ambient
  refine ⟨f, ?_⟩
  intro g hg
  have hr := Quotient.out_eq r
  change (@Quotient.mk' _ (QuotientGroup.rightRel K.toSubgroup) r.out) = r at hr
  have hmem : q.out * g * r.out⁻¹ ∈ K.toSubgroup :=
    QuotientGroup.rightRel_apply.mp (Quotient.eq'.mp (hr.trans hg.symm))
  let x : Variety.Point K.carrierVariety :=
    K.pointEquiv.symm ⟨q.out * g * r.out⁻¹, hmem⟩
  have htranslate : translate.toFun g = K.inclusion.onPoints x := by
    change q.out * g * r.out⁻¹ = (K.pointEquiv x).val
    rw [K.pointEquiv.apply_symm_apply]
  change ambient (translate.toFun g) = _
  rw [htranslate, hambient]
  change coordinate (ρ.onPoints x) = _
  have hcorr : Subgroup.rightCosetCorrection K.toSubgroup (q.out * g) = K.pointEquiv x := by
    apply Subtype.ext
    change q.out * g *
      (@Quotient.mk' _ (QuotientGroup.rightRel K.toSubgroup) (q.out * g)).out⁻¹ =
        q.out * g * r.out⁻¹
    have hout := congrArg Quotient.out hg
    rw [hout]
  rw [hcorr, K.pointEquiv.symm_apply_apply]
  change MvPolynomial.eval₂ (RingHom.id k) (ρ.onPoints x).val
    (MvPolynomial.X (Sum.inl (i, j))) = _
  simp

end

/-! Forward branch of the coinduced right-quotient matrix-coefficient package. -/

section

open Representation

variable {k : Type u} [Field k] [IsAlgClosed k]

public lemma ClosedSubgroup.coindRightQuotient_matrixCoefficient_forward_exists
    {G : Variety k} [AlgebraicGroup G]
    (K : ClosedSubgroup G) [K.toSubgroup.FiniteIndex]
    [Fintype (Quotient (QuotientGroup.rightRel K.toSubgroup))]
    (n : ℕ) (ρ : AlgebraicGroup.Morphism K.carrierVariety (glVariety n : Variety k))
    (q r : Quotient (QuotientGroup.rightRel K.toSubgroup)) (i j : Fin n) :
    letI := QuotientGroup.rightRel K.toSubgroup
    let A := Rep.of (K.generalLinearMorphismRepresentation n ρ)
    let b := Pi.basis (fun _ : Quotient (QuotientGroup.rightRel K.toSubgroup) =>
      Pi.basisFun k (Fin n))
    ∃ f : G.PolynomialFunction,
      ∀ x, f x =
        b.repr (Representation.coindRightQuotient K.toSubgroup A x (b ⟨r, j⟩)) ⟨q, i⟩ := by
  classical
  dsimp only
  letI := QuotientGroup.rightRel K.toSubgroup
  let A := Rep.of (K.generalLinearMorphismRepresentation n ρ)
  let b := Pi.basis (fun _ : Quotient (QuotientGroup.rightRel K.toSubgroup) =>
    Pi.basisFun k (Fin n))
  let c : Variety.Point G → Quotient (QuotientGroup.rightRel K.toSubgroup) :=
    fun x => @Quotient.mk' _ (QuotientGroup.rightRel K.toSubgroup) (q.out * x)
  have hc : ∀ z : Quotient (QuotientGroup.rightRel K.toSubgroup),
      IsClopen {x : Variety.Point G | c x = z} := by
    intro z
    simpa [c] using (K.quotientRightTranslateFiber_isClopen q.out z)
  obtain ⟨fr, hfr⟩ :=
    K.translatedGeneralLinearCoordinate_extension_exists n ρ q r i j
  rcases fr.representedBy with ⟨pr, hpr⟩
  let p : Quotient (QuotientGroup.rightRel K.toSubgroup) →
      MvPolynomial G.Coordinates k := fun z => if hz : z = r then pr else 0
  let F : Variety.Point G → k := fun x =>
    b.repr (Representation.coindRightQuotient K.toSubgroup A x (b ⟨r, j⟩)) ⟨q, i⟩
  have hp : ∀ z x, c x = z → F x = evalPolynomial x.val (p z) := by
    intro z x hx
    by_cases hzr : z = r
    · have hzr' : z = r := hzr
      have hmatch : @Quotient.mk' _ (QuotientGroup.rightRel K.toSubgroup) (q.out * x) = r := by
        simpa [c, hzr'] using hx
      have hsub :
          F x =
            (ρ.onPoints (K.pointEquiv.symm
              (Subgroup.rightCosetCorrection K.toSubgroup (q.out * x)))).val
              (Sum.inl (i, j)) :=
        K.coindRightQuotient_matrixCoefficient_of_eq n ρ x q r i j hmatch
      have hreg :
          fr x =
            (ρ.onPoints (K.pointEquiv.symm
              (Subgroup.rightCosetCorrection K.toSubgroup (q.out * x)))).val
              (Sum.inl (i, j)) :=
        hfr x hmatch
      calc
        F x =
            (ρ.onPoints (K.pointEquiv.symm
              (Subgroup.rightCosetCorrection K.toSubgroup (q.out * x)))).val
              (Sum.inl (i, j)) := hsub
        _ = fr x := hreg.symm
        _ = evalPolynomial x.val (p z) := by
          simpa [p, hzr'] using hpr x
    · have hneq : c x ≠ r := by
        intro hcr
        exact hzr (by
          calc
            z = c x := hx.symm
            _ = r := hcr)
      have hnot : @Quotient.mk' _ (QuotientGroup.rightRel K.toSubgroup) (q.out * x) ≠ r := by
        intro hmk
        have hcr : c x = r := by
          simpa [c] using hmk
        exact hneq hcr
      have hsub : F x = 0 :=
        K.coindRightQuotient_matrixCoefficient_of_ne n ρ x q r i j hnot
      simpa [p, hzr, evalPolynomial] using hsub
  obtain ⟨f, hf⟩ := Variety.exists_polynomialFunction_of_finite_clopen c hc F p hp
  exact ⟨f, hf⟩

end

/-! Inverse-branch formulas for the transported coinduced representation. -/

section

variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
public lemma ClosedSubgroup.coindRightQuotient_matrixCoefficient_of_eq_inv
    {G : Variety k} [AlgebraicGroup G]
    (K : ClosedSubgroup G) [K.toSubgroup.FiniteIndex]
    [Fintype (Quotient (QuotientGroup.rightRel K.toSubgroup))]
    (n : ℕ) (ρ : AlgebraicGroup.Morphism K.carrierVariety (glVariety n : Variety k))
    (g : Variety.Point G)
    (q r : Quotient (QuotientGroup.rightRel K.toSubgroup)) (i j : Fin n)
    (h : @Quotient.mk' _ (QuotientGroup.rightRel K.toSubgroup) (q.out * g⁻¹) = r) :
  letI := QuotientGroup.rightRel K.toSubgroup
  let A := Rep.of (K.generalLinearMorphismRepresentation n ρ)
  let b := Pi.basis (fun _ : Quotient (QuotientGroup.rightRel K.toSubgroup) =>
      Pi.basisFun k (Fin n))
  b.repr (Representation.coindRightQuotient K.toSubgroup A g⁻¹ (b ⟨r,j⟩)) ⟨q,i⟩ =
      (ρ.onPoints (K.pointEquiv.symm
        (Subgroup.rightCosetCorrection K.toSubgroup (q.out * g⁻¹)))).val
        (Sum.inl (i,j)) := by
  simpa using
    (ClosedSubgroup.coindRightQuotient_matrixCoefficient_of_eq
      (K := K) (n := n) ρ (g := g⁻¹) q r i j h)

omit [IsAlgClosed k] in
public lemma ClosedSubgroup.coindRightQuotient_matrixCoefficient_of_ne_inv
    {G : Variety k} [AlgebraicGroup G]
    (K : ClosedSubgroup G) [K.toSubgroup.FiniteIndex]
    [Fintype (Quotient (QuotientGroup.rightRel K.toSubgroup))]
    (n : ℕ) (ρ : AlgebraicGroup.Morphism K.carrierVariety (glVariety n : Variety k))
    (g : Variety.Point G)
    (q r : Quotient (QuotientGroup.rightRel K.toSubgroup)) (i j : Fin n)
    (h : @Quotient.mk' _ (QuotientGroup.rightRel K.toSubgroup) (q.out * g⁻¹) ≠ r) :
  letI := QuotientGroup.rightRel K.toSubgroup
  let A := Rep.of (K.generalLinearMorphismRepresentation n ρ)
  let b := Pi.basis (fun _ : Quotient (QuotientGroup.rightRel K.toSubgroup) =>
      Pi.basisFun k (Fin n))
  b.repr (Representation.coindRightQuotient K.toSubgroup A g⁻¹ (b ⟨r,j⟩)) ⟨q,i⟩ = 0 := by
  simpa using
    (ClosedSubgroup.coindRightQuotient_matrixCoefficient_of_ne
      (K := K) (n := n) ρ (g := g⁻¹) q r i j h)

end

/-! Ambient polynomial extensions of translated inverse subgroup matrix coordinates. -/

section
variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
public lemma ClosedSubgroup.translatedGeneralLinearCoordinate_extension_inv_exists
    {G : Variety k} [AlgebraicGroup G]
    (K : ClosedSubgroup G) [K.toSubgroup.FiniteIndex]
    (n : ℕ) (ρ : AlgebraicGroup.Morphism K.carrierVariety (glVariety n : Variety k))
    (q r : Quotient (QuotientGroup.rightRel K.toSubgroup)) (i j : Fin n) :
    ∃ f : G.PolynomialFunction, ∀ g,
      @Quotient.mk' _ (QuotientGroup.rightRel K.toSubgroup) (q.out * g⁻¹) = r →
      f g = (ρ.onPoints (K.pointEquiv.symm
        (Subgroup.rightCosetCorrection K.toSubgroup (q.out * g⁻¹)))).val
          (Sum.inl (i, j)) := by
  classical
  obtain ⟨f, hf⟩ :=
    K.translatedGeneralLinearCoordinate_extension_exists n ρ q r i j
  refine ⟨Variety.PolynomialFunction.pullback (AlgebraicGroup.invMorphism G) f, ?_⟩
  intro g hg
  change f g⁻¹ =
    (ρ.onPoints (K.pointEquiv.symm
      (Subgroup.rightCosetCorrection K.toSubgroup (q.out * g⁻¹)))).val
        (Sum.inl (i, j))
  exact hf (g⁻¹) hg

end

/-! Inverse branch of the coinduced right-quotient matrix-coefficient package. -/

section

open Representation

variable {k : Type u} [Field k] [IsAlgClosed k]

public lemma ClosedSubgroup.coindRightQuotient_matrixCoefficient_inv_exists
    {G : Variety k} [AlgebraicGroup G]
    (K : ClosedSubgroup G) [K.toSubgroup.FiniteIndex]
    [Fintype (Quotient (QuotientGroup.rightRel K.toSubgroup))]
    (n : ℕ) (ρ : AlgebraicGroup.Morphism K.carrierVariety (glVariety n : Variety k))
    (q r : Quotient (QuotientGroup.rightRel K.toSubgroup)) (i j : Fin n) :
    letI := QuotientGroup.rightRel K.toSubgroup
    let A := Rep.of (K.generalLinearMorphismRepresentation n ρ)
    let b := Pi.basis (fun _ : Quotient (QuotientGroup.rightRel K.toSubgroup) =>
      Pi.basisFun k (Fin n))
    ∃ f : G.PolynomialFunction,
      ∀ x, f x =
        b.repr (Representation.coindRightQuotient K.toSubgroup A x⁻¹ (b ⟨r, j⟩)) ⟨q, i⟩ := by
  classical
  dsimp only
  letI := QuotientGroup.rightRel K.toSubgroup
  let A := Rep.of (K.generalLinearMorphismRepresentation n ρ)
  let b := Pi.basis (fun _ : Quotient (QuotientGroup.rightRel K.toSubgroup) =>
    Pi.basisFun k (Fin n))
  let c0 : Variety.Point G → Quotient (QuotientGroup.rightRel K.toSubgroup) :=
    fun x => @Quotient.mk' _ (QuotientGroup.rightRel K.toSubgroup) (q.out * x)
  have hc0 : ∀ z : Quotient (QuotientGroup.rightRel K.toSubgroup),
      IsClopen {x : Variety.Point G | c0 x = z} := by
    intro z
    change IsClopen {x : Variety.Point G |
      @Quotient.mk' _ (QuotientGroup.rightRel K.toSubgroup) (q.out * x) = z}
    exact K.quotientRightTranslateFiber_isClopen q.out z
  let c : Variety.Point G → Quotient (QuotientGroup.rightRel K.toSubgroup) :=
    fun x => @Quotient.mk' _ (QuotientGroup.rightRel K.toSubgroup) (q.out * x⁻¹)
  have hc : ∀ z : Quotient (QuotientGroup.rightRel K.toSubgroup),
      IsClopen {x : Variety.Point G | c x = z} := by
    intro z
    change IsClopen ((AlgebraicGroup.invMorphism G).toFun ⁻¹'
      {x : Variety.Point G | c0 x = z})
    simpa [c, c0] using (hc0 z).preimage (AlgebraicGroup.invMorphism G).continuous
  obtain ⟨fr, hfr⟩ :=
    K.translatedGeneralLinearCoordinate_extension_inv_exists n ρ q r i j
  rcases fr.representedBy with ⟨pr, hpr⟩
  let p : Quotient (QuotientGroup.rightRel K.toSubgroup) →
      MvPolynomial G.Coordinates k := fun z => if hz : z = r then pr else 0
  let F : Variety.Point G → k := fun x =>
    b.repr (Representation.coindRightQuotient K.toSubgroup A x⁻¹ (b ⟨r, j⟩)) ⟨q, i⟩
  have hp : ∀ z x, c x = z → F x = evalPolynomial x.val (p z) := by
    intro z x hx
    by_cases hzr : z = r
    · have hx' : c x = r := by simpa [hzr] using hx
      have hmatch :
          @Quotient.mk' _ (QuotientGroup.rightRel K.toSubgroup) (q.out * x⁻¹) = r := by
        simpa [c] using hx'
      have hsub :
          F x =
            (ρ.onPoints (K.pointEquiv.symm
              (Subgroup.rightCosetCorrection K.toSubgroup (q.out * x⁻¹)))).val
              (Sum.inl (i, j)) :=
        K.coindRightQuotient_matrixCoefficient_of_eq_inv n ρ x q r i j hmatch
      have hreg :
          fr x =
            (ρ.onPoints (K.pointEquiv.symm
              (Subgroup.rightCosetCorrection K.toSubgroup (q.out * x⁻¹)))).val
              (Sum.inl (i, j)) :=
        hfr x hmatch
      calc
        F x =
            (ρ.onPoints (K.pointEquiv.symm
              (Subgroup.rightCosetCorrection K.toSubgroup (q.out * x⁻¹)))).val
              (Sum.inl (i, j)) := hsub
        _ = fr x := hreg.symm
        _ = evalPolynomial x.val (p z) := by
          simpa [p, hzr] using hpr x
    · have hneq : c x ≠ r := by
        intro hcr
        exact hzr (by
          calc
            z = c x := hx.symm
            _ = r := hcr)
      have hnot :
          @Quotient.mk' _ (QuotientGroup.rightRel K.toSubgroup) (q.out * x⁻¹) ≠ r := by
        intro hmk
        exact hneq (by simpa [c] using hmk)
      have hsub : F x = 0 :=
        K.coindRightQuotient_matrixCoefficient_of_ne_inv n ρ x q r i j hnot
      simpa [p, hzr, evalPolynomial] using hsub
  obtain ⟨f, hf⟩ := Variety.exists_polynomialFunction_of_finite_clopen c hc F p hp
  exact ⟨f, hf⟩

end

/-! Regularity of the transported finite-index coinduced representation. -/

section

open Representation

variable {k : Type u} [Field k] [IsAlgClosed k]

public lemma ClosedSubgroup.coindRightQuotient_generalLinearMorphism_exists
    {G : Variety k} [AlgebraicGroup G]
    (K : ClosedSubgroup G) [K.toSubgroup.FiniteIndex]
    [Fintype (Quotient (QuotientGroup.rightRel K.toSubgroup))]
    (n : ℕ) (ρ : AlgebraicGroup.Morphism K.carrierVariety (glVariety n : Variety k)) :
    letI := QuotientGroup.rightRel K.toSubgroup
    let A := Rep.of (K.generalLinearMorphismRepresentation n ρ)
    let Q := Quotient (QuotientGroup.rightRel K.toSubgroup)
    let V := Q → (Fin n → k)
    let τ := Representation.coindRightQuotient K.toSubgroup A
    let τGL := MonoidHom.toHomUnits τ
    let b0 := Pi.basis (fun _ : Q => Pi.basisFun k (Fin n))
    let idx := (Fintype.equivFin (Σ _ : Q, Fin n)).trans
      (finCongr (Module.finrank_eq_card_basis b0).symm)
    let b := b0.reindex idx
    ∃ F : AlgebraicGroup.Morphism G (glVariety (Module.finrank k V) : Variety k),
      ∀ x, F.onPoints x = generalLinearRepresentationPoint b (τGL x) := by
  classical
  dsimp only
  letI := QuotientGroup.rightRel K.toSubgroup
  let A := Rep.of (K.generalLinearMorphismRepresentation n ρ)
  let Q := Quotient (QuotientGroup.rightRel K.toSubgroup)
  let V := Q → (Fin n → k)
  let τ := Representation.coindRightQuotient K.toSubgroup A
  let τGL := MonoidHom.toHomUnits τ
  let b0 := Pi.basis (fun _ : Q => Pi.basisFun k (Fin n))
  let idx := (Fintype.equivFin (Σ _ : Q, Fin n)).trans
    (finCongr (Module.finrank_eq_card_basis b0).symm)
  let b := b0.reindex idx
  have hpackage (i j : Fin (Module.finrank k V)) :
      ∃ f g : G.PolynomialFunction,
        (∀ x, f x = b.repr ((τ x) (b j)) i) ∧
        (∀ x, g x = b.repr ((τ x⁻¹) (b j)) i) := by
    rcases hi : idx.symm i with ⟨q, a⟩
    rcases hj : idx.symm j with ⟨r, c⟩
    rcases K.coindRightQuotient_matrixCoefficient_forward_exists n ρ q r a c with
      ⟨f, hf⟩
    rcases K.coindRightQuotient_matrixCoefficient_inv_exists n ρ q r a c with
      ⟨g, hg⟩
    refine ⟨f, g, ?_, ?_⟩
    · intro x
      simpa [b, b0, Module.Basis.reindex_apply, Pi.basis_repr, Pi.basisFun_repr,
        τ, V, Q, A, hi, hj] using hf x
    · intro x
      simpa [b, b0, Module.Basis.reindex_apply, Pi.basis_repr, Pi.basisFun_repr,
        τ, V, Q, A, hi, hj] using hg x
  choose matrixCoefficient inverseMatrixCoefficient matrixCoefficient_apply'
    inverseMatrixCoefficient_apply' using hpackage
  have matrixCoefficient_apply : ∀ i j x,
      matrixCoefficient i j x = b.repr ((τGL x : Module.End k V) (b j)) i := by
    intro i j x
    exact matrixCoefficient_apply' i j x
  have inverseMatrixCoefficient_apply : ∀ i j x,
      inverseMatrixCoefficient i j x =
        b.repr (((((τGL x)⁻¹ : LinearMap.GeneralLinearGroup k V) : Module.End k V))
          (b j)) i := by
    intro i j x
    change inverseMatrixCoefficient i j x = b.repr ((τ x⁻¹) (b j)) i
    exact inverseMatrixCoefficient_apply' i j x
  let F := generalLinearRepresentationMorphismOfInverseMatrixCoefficient b τGL
    matrixCoefficient inverseMatrixCoefficient matrixCoefficient_apply inverseMatrixCoefficient_apply
  exact ⟨F, fun x => generalLinearRepresentationMorphismOfInverseMatrixCoefficient_apply
    b τGL matrixCoefficient inverseMatrixCoefficient matrixCoefficient_apply
      inverseMatrixCoefficient_apply x⟩

end

/-! Restriction of an induced representation detects the original subgroup action. -/

open scoped MonoidAlgebra
open Representation

section

public lemma Representation.ind_subtype_eq_one_imp
    {k : Type u} {G : Type v} [Field k] [Group G]
    (S : Subgroup G) [S.FiniteIndex]
    (A : Rep.{w} k S) (s : S)
    (hs : (Rep.ind S.subtype A).ρ s.val = 1) : A.ρ s = 1 := by
  classical
  apply LinearMap.ext
  intro a
  let m := IndV.mk S.subtype A.ρ 1 a
  have hm := congrArg (fun L : Module.End k (Rep.ind S.subtype A) => L m) hs
  change (Rep.ind S.subtype A).ρ s.val m = m at hm
  rw [Representation.ind_mk] at hm
  have hleft :
      (Rep.indToCoind A (IndV.mk S.subtype A.ρ s.val⁻¹ a)).1 1 = A.ρ s a := by
    simp [Rep.indToCoind, Rep.indToCoindAux, QuotientGroup.rightRel_apply]
  have hright : (Rep.indToCoind A m).1 1 = a := by
    simp [m, Rep.indToCoind, LinearMap.codRestrict]
  have hf := congrArg
    (fun z : Rep.ind S.subtype A => (Rep.indToCoind A z).1 1) hm
  have hf' :
      (Rep.indToCoind A (IndV.mk S.subtype A.ρ s.val⁻¹ a)).1 1 =
        (Rep.indToCoind A m).1 1 := by
    simpa only [one_mul] using hf
  rw [hleft, hright] at hf'
  simpa using hf'

end

/-! Exact kernel of the regular finite-index coinduced representation. -/

section

open Representation

variable {k : Type u} [Field k] [IsAlgClosed k]

public lemma ClosedSubgroup.coindRightQuotient_generalLinearMorphism_kernel_eq
    {G : Variety k} [AlgebraicGroup G]
    (K : ClosedSubgroup G) [K.toSubgroup.FiniteIndex]
    [Fintype (Quotient (QuotientGroup.rightRel K.toSubgroup))]
    (n : ℕ) (ρ : AlgebraicGroup.Morphism K.carrierVariety (glVariety n : Variety k)) :
    letI := QuotientGroup.rightRel K.toSubgroup
    let A := Rep.of (K.generalLinearMorphismRepresentation n ρ)
    let Q := Quotient (QuotientGroup.rightRel K.toSubgroup)
    let V := Q → (Fin n → k)
    let τ := Representation.coindRightQuotient K.toSubgroup A
    let τGL := MonoidHom.toHomUnits τ
    let b0 := Pi.basis (fun _ : Q => Pi.basisFun k (Fin n))
    let idx := (Fintype.equivFin (Σ _ : Q, Fin n)).trans
      (finCongr (Module.finrank_eq_card_basis b0).symm)
    let b := b0.reindex idx
    ∃ F : AlgebraicGroup.Morphism G (glVariety (Module.finrank k V) : Variety k),
      (∀ x, F.onPoints x = generalLinearRepresentationPoint b (τGL x)) ∧
        F.kernel = (Rep.ind K.toSubgroup.subtype A).ρ.ker := by
  classical
  dsimp only
  letI := QuotientGroup.rightRel K.toSubgroup
  let A := Rep.of (K.generalLinearMorphismRepresentation n ρ)
  let Q := Quotient (QuotientGroup.rightRel K.toSubgroup)
  let V := Q → (Fin n → k)
  let τ := Representation.coindRightQuotient K.toSubgroup A
  let τGL := MonoidHom.toHomUnits τ
  let b0 := Pi.basis (fun _ : Q => Pi.basisFun k (Fin n))
  let idx := (Fintype.equivFin (Σ _ : Q, Fin n)).trans
    (finCongr (Module.finrank_eq_card_basis b0).symm)
  let b := b0.reindex idx
  obtain ⟨F, hF⟩ := K.coindRightQuotient_generalLinearMorphism_exists n ρ
  refine ⟨F, hF, ?_⟩
  ext x
  constructor
  · intro hx
    have hxone : F.onPoints x = 1 := hx
    have hpoint : generalLinearRepresentationPoint b (τGL x) = 1 := by
      rw [← hF x]
      exact hxone
    have hτGL : τGL x = 1 := (generalLinearRepresentationPoint_eq_one_iff b (τGL x)).mp hpoint
    have hτ : τ x = 1 := by
      have h := congrArg (fun z : (Module.End k V)ˣ => (z : Module.End k V)) hτGL
      simpa [τGL] using h
    have hcoind : (Representation.coind K.toSubgroup.subtype A.ρ) x = 1 := by
      let E := Representation.coindVEquivRightQuotientPi K.toSubgroup A
      apply LinearMap.ext
      intro y
      have hy := congrArg (fun L : Module.End k V => L (E y)) hτ
      simpa [τ, Representation.coindRightQuotient, E] using hy
    have hind : (Rep.ind K.toSubgroup.subtype A).ρ x = 1 := by
      apply LinearMap.ext
      intro z
      have hz := congrArg
        (fun L : Module.End k (Rep.coind K.toSubgroup.subtype A) =>
          L ((Rep.indCoindIso A).hom.hom z)) hcoind
      rw [← Rep.hom_comm_apply (Rep.indCoindIso A).hom x z] at hz
      have hz' := congrArg (Rep.indCoindIso A).inv.hom hz
      simpa using hz'
    exact MonoidHom.mem_ker.mpr hind
  · intro hx
    have hind : (Rep.ind K.toSubgroup.subtype A).ρ x = 1 := MonoidHom.mem_ker.mp hx
    have hcoind : (Representation.coind K.toSubgroup.subtype A.ρ) x = 1 := by
      let E := Rep.indCoindIso A
      apply LinearMap.ext
      intro y
      have hy := congrArg E.hom.hom
        (congrArg (fun L : Module.End k (Rep.ind K.toSubgroup.subtype A) =>
          L (E.inv.hom y)) hind)
      rw [Rep.hom_comm_apply E.hom x (E.inv.hom y)] at hy
      simpa using hy
    have hτ : τ x = 1 := by
      let E := Representation.coindVEquivRightQuotientPi K.toSubgroup A
      apply LinearMap.ext
      intro y
      have hy := congrArg E
        (congrArg (fun L : Module.End k (Rep.coind K.toSubgroup.subtype A) =>
          L (E.symm y)) hcoind)
      simpa [τ, Representation.coindRightQuotient, E] using hy
    have hτGL : τGL x = 1 := by
      apply Units.ext
      simpa [τGL] using hτ
    have hpoint : generalLinearRepresentationPoint b (τGL x) = 1 :=
      (generalLinearRepresentationPoint_eq_one_iff b (τGL x)).mpr hτGL
    have hxone : F.onPoints x = 1 := by
      rw [hF x, hpoint]
    exact hxone

end

/-! Detecting the identity in the representation underlying a morphism to `GLₙ`. -/

section

variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
public lemma ClosedSubgroup.generalLinearMorphismRepresentation_eq_one_iff
    {G : Variety k} [AlgebraicGroup G]
    (K : ClosedSubgroup G) (n : ℕ)
    (ρ : AlgebraicGroup.Morphism K.carrierVariety (glVariety n : Variety k))
    (s : K.toSubgroup) :
    K.generalLinearMorphismRepresentation n ρ s = 1 ↔
      ρ.onPoints (K.pointEquiv.symm s) = 1 := by
  dsimp [ClosedSubgroup.generalLinearMorphismRepresentation]
  constructor
  · intro h
    have hlin : Matrix.GeneralLinearGroup.toLin
        ((translationGLPointMulEquiv n) (ρ.onPoints (K.pointEquiv.symm s))) = 1 := by
      apply Units.ext
      exact h
    have hmatrix :
        (translationGLPointMulEquiv n) (ρ.onPoints (K.pointEquiv.symm s)) = 1 :=
      (Matrix.GeneralLinearGroup.toLin).injective (by simpa using hlin)
    apply (translationGLPointMulEquiv n).injective
    simpa using hmatrix
  · intro h
    have hs :
        ({ toEquiv := K.pointEquiv, map_mul' := fun _ _ => rfl } :
          Variety.Point K.carrierVariety ≃* K.toSubgroup).symm s =
          K.pointEquiv.symm s := by
      apply Variety.Point.ext
      rfl
    rw [hs, h]
    simp [Module.End.one_eq_id]

end
end Theory.AlgebraicGroup
