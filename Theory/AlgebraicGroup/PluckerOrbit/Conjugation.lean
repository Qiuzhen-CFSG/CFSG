module

public import Theory.AlgebraicGroup.PluckerOrbit.MatrixCoefficients

universe u v

/-! Conjugation of endomorphisms by the general linear group. -/

namespace Theory.AlgebraicGroup

section

variable {k : Type u} [Field k]
variable {V : Type v} [AddCommGroup V] [Module k V]

@[expose]
public noncomputable def generalLinearConjugationRepresentation :
    LinearMap.GeneralLinearGroup k V →*
      LinearMap.GeneralLinearGroup k (Module.End k V) where
  toFun x := LinearMap.GeneralLinearGroup.ofLinearEquiv x.toLinearEquiv.conj
  map_one' := by
    apply Units.ext
    change (1 : LinearMap.GeneralLinearGroup k V).toLinearEquiv.conj.toLinearMap =
      LinearMap.id
    ext f v
    rfl
  map_mul' x y := by
    apply Units.ext
    change (x * y).toLinearEquiv.conj.toLinearMap =
      x.toLinearEquiv.conj.toLinearMap * y.toLinearEquiv.conj.toLinearMap
    ext f v
    rw [LinearMap.GeneralLinearGroup.toLinearEquiv_mul]
    rfl

public lemma generalLinearConjugationRepresentation_apply
    (x : LinearMap.GeneralLinearGroup k V) (f : Module.End k V) :
    ((generalLinearConjugationRepresentation x :
      LinearMap.GeneralLinearGroup k (Module.End k V)) :
      Module.End k (Module.End k V)) f = x.toLinearEquiv.conj f :=
  rfl

public lemma generalLinearConjugationRepresentation_eq_one_iff
    (x : LinearMap.GeneralLinearGroup k V) :
    generalLinearConjugationRepresentation x = 1 ↔
      ∃ a : k, (x : Module.End k V) = a • LinearMap.id := by
  constructor
  · intro hx
    have hfix : ∀ f : Module.End k V, x.toLinearEquiv.conj f = f := by
      intro f
      have h := congrArg
        (fun y : LinearMap.GeneralLinearGroup k (Module.End k V) =>
          ((y : Module.End k (Module.End k V)) f)) hx
      simpa [generalLinearConjugationRepresentation_apply] using h
    have hcenter : (x : Module.End k V) ∈ Set.center (Module.End k V) := by
      rw [Semigroup.mem_center_iff]
      intro f
      ext v
      change f (x.toLinearEquiv v) = x.toLinearEquiv (f v)
      have h := LinearMap.congr_fun (hfix f) (x.toLinearEquiv v)
      change x.toLinearEquiv (f (x.toLinearEquiv.symm (x.toLinearEquiv v))) =
        f (x.toLinearEquiv v) at h
      rw [LinearEquiv.symm_apply_apply] at h
      exact h.symm
    rcases Module.End.mem_center_iff.mp hcenter with ⟨a, ha, hxa⟩
    refine ⟨a, ?_⟩
    ext v
    have h := LinearMap.congr_fun hxa v
    simpa [Module.End.smulLeft] using h
  · rintro ⟨a, hxa⟩
    apply Units.ext
    change x.toLinearEquiv.conj.toLinearMap = LinearMap.id
    ext f v
    change x.toLinearEquiv (f (x.toLinearEquiv.symm v)) = f v
    have hcomm : (x : Module.End k V) * f = f * (x : Module.End k V) := by
      rw [hxa]
      ext w
      simp
    have h : (x : Module.End k V) (f (x.toLinearEquiv.symm v)) =
        f ((x : Module.End k V) (x.toLinearEquiv.symm v)) := by
      change ((x : Module.End k V) * f) (x.toLinearEquiv.symm v) =
        (f * (x : Module.End k V)) (x.toLinearEquiv.symm v)
      exact LinearMap.congr_fun hcomm (x.toLinearEquiv.symm v)
    change x.toLinearEquiv (f (x.toLinearEquiv.symm v)) =
      f (x.toLinearEquiv (x.toLinearEquiv.symm v)) at h
    rw [LinearEquiv.apply_symm_apply] at h
    exact h

variable [Module.Finite k V]

@[expose]
public noncomputable def generalLinearConjugationEndIndexEquiv :
    (Fin (Module.finrank k V) × Fin (Module.finrank k V)) ≃
      Fin (Module.finrank k (Module.End k V)) :=
  Fintype.equivOfCardEq (by
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin,
      Module.finrank_linearMap])

@[expose]
public noncomputable def generalLinearConjugationEndBasis
    (b : Module.Basis (Fin (Module.finrank k V)) k V) :
    Module.Basis (Fin (Module.finrank k (Module.End k V))) k (Module.End k V) :=
  b.end.reindex (generalLinearConjugationEndIndexEquiv (k := k) (V := V))

public lemma generalLinearConjugationEndBasis_apply
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (i : Fin (Module.finrank k (Module.End k V))) :
    generalLinearConjugationEndBasis b i =
      b.end ((generalLinearConjugationEndIndexEquiv (k := k) (V := V)).symm i) := by
  simp [generalLinearConjugationEndBasis]

public lemma generalLinearConjugationEndBasis_repr
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (f : Module.End k V) (i : Fin (Module.finrank k (Module.End k V))) :
    (generalLinearConjugationEndBasis b).repr f i =
      b.end.repr f
        ((generalLinearConjugationEndIndexEquiv (k := k) (V := V)).symm i) := by
  simp [generalLinearConjugationEndBasis]

omit [Module.Finite k V] in
public lemma Module.Basis.end_apply_eq_smul
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (a c : Fin (Module.finrank k V)) (v : V) :
    b.end (a, c) v = (b.repr v c) • b a := by
  rw [← b.sum_repr v]
  simp only [map_sum]
  rw [Finset.sum_eq_single c]
  · simp [b.end_apply_apply]
  · intro x _ hxc
    simp [b.end_apply_apply, Ne.symm hxc]
  · simp

omit [Module.Finite k V] in
public lemma generalLinearConjugationRepresentation_matrixCoefficient
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (x : LinearMap.GeneralLinearGroup k V)
    (p q a c : Fin (Module.finrank k V)) :
    b.end.repr
        (((generalLinearConjugationRepresentation x :
          LinearMap.GeneralLinearGroup k (Module.End k V)) :
          Module.End k (Module.End k V)) (b.end (a, c))) (p, q) =
      b.repr ((x : Module.End k V) (b a)) p *
        b.repr (((x⁻¹ : LinearMap.GeneralLinearGroup k V) : Module.End k V) (b q)) c := by
  rw [generalLinearConjugationRepresentation_apply]
  change (LinearMap.toMatrix b b (x.toLinearEquiv.conj (b.end (a, c)))) p q = _
  rw [LinearMap.toMatrix_apply, LinearEquiv.conj_apply_apply]
  rw [Theory.AlgebraicGroup.Module.Basis.end_apply_eq_smul, map_smul, map_smul]
  change _ = b.repr (x.toLinearEquiv (b a)) p *
    b.repr (x.toLinearEquiv.symm (b q)) c
  simp [mul_comm]

public lemma generalLinearConjugationRepresentation_finMatrixCoefficient
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (x : LinearMap.GeneralLinearGroup k V)
    (i j : Fin (Module.finrank k (Module.End k V))) :
    (generalLinearConjugationEndBasis b).repr
        (((generalLinearConjugationRepresentation x :
          LinearMap.GeneralLinearGroup k (Module.End k V)) :
          Module.End k (Module.End k V)) (generalLinearConjugationEndBasis b j)) i =
      b.repr ((x : Module.End k V)
          (b ((generalLinearConjugationEndIndexEquiv (k := k) (V := V)).symm j).1))
        ((generalLinearConjugationEndIndexEquiv (k := k) (V := V)).symm i).1 *
      b.repr (((x⁻¹ : LinearMap.GeneralLinearGroup k V) : Module.End k V)
          (b ((generalLinearConjugationEndIndexEquiv (k := k) (V := V)).symm i).2))
        ((generalLinearConjugationEndIndexEquiv (k := k) (V := V)).symm j).2 := by
  rw [generalLinearConjugationEndBasis_repr,
    generalLinearConjugationEndBasis_apply]
  exact generalLinearConjugationRepresentation_matrixCoefficient b x
    ((generalLinearConjugationEndIndexEquiv (k := k) (V := V)).symm i).1
    ((generalLinearConjugationEndIndexEquiv (k := k) (V := V)).symm i).2
    ((generalLinearConjugationEndIndexEquiv (k := k) (V := V)).symm j).1
    ((generalLinearConjugationEndIndexEquiv (k := k) (V := V)).symm j).2

end

/-! The regular conjugation representation of the standard general linear group. -/

section

variable {k : Type u} [Field k] [IsAlgClosed k]

@[expose]
public noncomputable def generalLinearStandardIndexEquiv (n : ℕ) :
    Fin n ≃ Fin (Module.finrank k (Fin n → k)) :=
  let h : Module.finrank k (Fin n → k) = n := by
    simpa only [Fintype.card_fin] using (Module.finrank_pi k :
      Module.finrank k (Fin n → k) = Fintype.card (Fin n))
  Equiv.cast (congrArg Fin h.symm)

@[expose]
public noncomputable def generalLinearStandardBasis (n : ℕ) :
    Module.Basis (Fin (Module.finrank k (Fin n → k))) k (Fin n → k) :=
  (Pi.basisFun k (Fin n)).reindex (generalLinearStandardIndexEquiv (k := k) n)

@[expose]
public noncomputable def generalLinearPointRepresentation (n : ℕ) :
    Variety.Point (glVariety n : Variety k) →*
      LinearMap.GeneralLinearGroup k (Fin n → k) :=
  Matrix.GeneralLinearGroup.toLin.toMonoidHom.comp
    (translationGLPointMulEquiv n).toMonoidHom

omit [IsAlgClosed k] in
public lemma generalLinearPointRepresentation_matrixCoefficient
    (n : ℕ) (x : Variety.Point (glVariety n : Variety k))
    (i j : Fin (Module.finrank k (Fin n → k))) :
    (generalLinearStandardBasis (k := k) n).repr
      (((generalLinearPointRepresentation (k := k) n x :
        LinearMap.GeneralLinearGroup k (Fin n → k)) : Module.End k (Fin n → k))
        (generalLinearStandardBasis (k := k) n j)) i =
      x.val (Sum.inl
        ((generalLinearStandardIndexEquiv (k := k) n).symm i,
          (generalLinearStandardIndexEquiv (k := k) n).symm j)) := by
  simp [generalLinearStandardBasis, generalLinearPointRepresentation,
    translationGLPointMulEquiv]
  rfl

@[expose]
public noncomputable def generalLinearConjugationPointRepresentation (n : ℕ) :
    Variety.Point (glVariety n : Variety k) →*
      LinearMap.GeneralLinearGroup k (Module.End k (Fin n → k)) :=
  (generalLinearConjugationRepresentation (k := k) (V := Fin n → k)).comp
    (generalLinearPointRepresentation (k := k) n)

omit [IsAlgClosed k] in
public lemma generalLinearConjugationPointRepresentation_apply (n : ℕ)
    (x : Variety.Point (glVariety n : Variety k)) :
    generalLinearConjugationPointRepresentation (k := k) n x =
      generalLinearConjugationRepresentation
        (generalLinearPointRepresentation (k := k) n x) :=
  rfl

@[expose]
public noncomputable def generalLinearConjugationMatrixCoefficient (n : ℕ)
    (i j : Fin (Module.finrank k (Module.End k (Fin n → k)))) :
    (glVariety n : Variety k).PolynomialFunction :=
  let e := generalLinearConjugationEndIndexEquiv (k := k) (V := Fin n → k)
  let s := generalLinearStandardIndexEquiv (k := k) n
  generalLinearMatrixCoordinate n (s.symm (e.symm i).1) (s.symm (e.symm j).1) *
    generalLinearInverseMatrixCoordinate n (s.symm (e.symm j).2) (s.symm (e.symm i).2)

omit [IsAlgClosed k] in
public lemma generalLinearConjugationMatrixCoefficient_apply (n : ℕ)
    (i j : Fin (Module.finrank k (Module.End k (Fin n → k))))
    (x : Variety.Point (glVariety n : Variety k)) :
    generalLinearConjugationMatrixCoefficient (k := k) n i j x =
      (generalLinearConjugationEndBasis (generalLinearStandardBasis (k := k) n)).repr
        (((generalLinearConjugationPointRepresentation (k := k) n x :
          LinearMap.GeneralLinearGroup k (Module.End k (Fin n → k))) :
          Module.End k (Module.End k (Fin n → k)))
          (generalLinearConjugationEndBasis
            (generalLinearStandardBasis (k := k) n) j)) i := by
  let b := generalLinearStandardBasis (k := k) n
  let ρ := generalLinearPointRepresentation (k := k) n
  let e := generalLinearConjugationEndIndexEquiv (k := k) (V := Fin n → k)
  let s := generalLinearStandardIndexEquiv (k := k) n
  rw [generalLinearConjugationMatrixCoefficient]
  change
    generalLinearMatrixCoordinate n (s.symm (e.symm i).1) (s.symm (e.symm j).1) x *
      generalLinearInverseMatrixCoordinate n (s.symm (e.symm j).2)
        (s.symm (e.symm i).2) x = _
  rw [generalLinearMatrixCoordinate_apply, generalLinearInverseMatrixCoordinate_apply]
  rw [← generalLinearPointRepresentation_matrixCoefficient,
    ← generalLinearPointRepresentation_matrixCoefficient]
  exact (generalLinearConjugationRepresentation_finMatrixCoefficient b (ρ x) i j).symm

@[expose]
public noncomputable def generalLinearConjugationInverseMatrixCoefficient (n : ℕ)
    (i j : Fin (Module.finrank k (Module.End k (Fin n → k)))) :
    (glVariety n : Variety k).PolynomialFunction :=
  let e := generalLinearConjugationEndIndexEquiv (k := k) (V := Fin n → k)
  let s := generalLinearStandardIndexEquiv (k := k) n
  generalLinearInverseMatrixCoordinate n (s.symm (e.symm i).1) (s.symm (e.symm j).1) *
    generalLinearMatrixCoordinate n (s.symm (e.symm j).2) (s.symm (e.symm i).2)

omit [IsAlgClosed k] in
public lemma generalLinearConjugationInverseMatrixCoefficient_apply (n : ℕ)
    (i j : Fin (Module.finrank k (Module.End k (Fin n → k))))
    (x : Variety.Point (glVariety n : Variety k)) :
    generalLinearConjugationInverseMatrixCoefficient (k := k) n i j x =
      (generalLinearConjugationEndBasis (generalLinearStandardBasis (k := k) n)).repr
        ((((generalLinearConjugationPointRepresentation (k := k) n x)⁻¹ :
          LinearMap.GeneralLinearGroup k (Module.End k (Fin n → k))) :
          Module.End k (Module.End k (Fin n → k)))
          (generalLinearConjugationEndBasis
            (generalLinearStandardBasis (k := k) n) j)) i := by
  let b := generalLinearStandardBasis (k := k) n
  let ρ := generalLinearPointRepresentation (k := k) n
  let e := generalLinearConjugationEndIndexEquiv (k := k) (V := Fin n → k)
  let s := generalLinearStandardIndexEquiv (k := k) n
  rw [generalLinearConjugationInverseMatrixCoefficient]
  change
    generalLinearInverseMatrixCoordinate n (s.symm (e.symm i).1) (s.symm (e.symm j).1) x *
      generalLinearMatrixCoordinate n (s.symm (e.symm j).2) (s.symm (e.symm i).2) x = _
  rw [generalLinearInverseMatrixCoordinate_apply, generalLinearMatrixCoordinate_apply]
  rw [← generalLinearPointRepresentation_matrixCoefficient,
    ← generalLinearPointRepresentation_matrixCoefficient]
  have hconj := generalLinearConjugationRepresentation_finMatrixCoefficient
    b ((ρ x)⁻¹) i j
  have hinv : generalLinearConjugationRepresentation ((ρ x)⁻¹) =
      (generalLinearConjugationPointRepresentation (k := k) n x)⁻¹ := by
    exact map_inv (generalLinearConjugationRepresentation (k := k) (V := Fin n → k)) (ρ x)
  rw [hinv] at hconj
  exact hconj.symm

@[expose]
public noncomputable def generalLinearConjugationMorphism (n : ℕ) :
    AlgebraicGroup.Morphism (glVariety n : Variety k)
      (glVariety (Module.finrank k (Module.End k (Fin n → k))) : Variety k) :=
  generalLinearRepresentationMorphismOfInverseMatrixCoefficient
    (generalLinearConjugationEndBasis (generalLinearStandardBasis (k := k) n))
    (generalLinearConjugationPointRepresentation (k := k) n)
    (generalLinearConjugationMatrixCoefficient (k := k) n)
    (generalLinearConjugationInverseMatrixCoefficient (k := k) n)
    (generalLinearConjugationMatrixCoefficient_apply (k := k) n)
    (generalLinearConjugationInverseMatrixCoefficient_apply (k := k) n)

omit [IsAlgClosed k] in
public lemma generalLinearConjugationMorphism_apply (n : ℕ)
    (x : Variety.Point (glVariety n : Variety k)) :
    (generalLinearConjugationMorphism (k := k) n).onPoints x =
      generalLinearRepresentationPoint
        (generalLinearConjugationEndBasis (generalLinearStandardBasis (k := k) n))
        (generalLinearConjugationPointRepresentation (k := k) n x) :=
  rfl

end

/-! The projective Plücker representation obtained by postcomposing with conjugation. -/

section
variable {k : Type u} [Field k] [IsAlgClosed k]

@[expose]
public noncomputable def ClosedSubgroup.rightTranslateVanishingPluckerConjugationMorphism
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G) :
    AlgebraicGroup.Morphism G
      (glVariety (Module.finrank k
        (Module.End k (Fin (Module.finrank k H.rightTranslateVanishingPluckerOrbitSpan) → k))) :
        Variety k) :=
  (generalLinearConjugationMorphism
    (k := k) (Module.finrank k H.rightTranslateVanishingPluckerOrbitSpan)).comp
      H.rightTranslateVanishingPluckerOrbitSpanRepresentationMorphism

omit [IsAlgClosed k] in
public lemma ClosedSubgroup.rightTranslateVanishingPluckerConjugationMorphism_apply
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (g : Variety.Point G) :
    H.rightTranslateVanishingPluckerConjugationMorphism.onPoints g =
      (generalLinearConjugationMorphism
        (k := k) (Module.finrank k H.rightTranslateVanishingPluckerOrbitSpan)).onPoints
        (H.rightTranslateVanishingPluckerOrbitSpanRepresentationMorphism.onPoints g) :=
  rfl

end

/-! Exactness of the Plücker-conjugation kernel in the forward direction. -/

section
open scoped ExteriorAlgebra
variable {k : Type u} [Field k] [IsAlgClosed k]

set_option maxHeartbeats 800000 in
omit [IsAlgClosed k] in
public lemma ClosedSubgroup.rightTranslateVanishingPluckerConjugationMorphism_eq_one_imp_mem
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (g : Variety.Point G)
    (hcand : H.rightTranslateVanishingPluckerConjugationMorphism.onPoints g = 1) :
    g ∈ H.toSubgroup := by
  let W : Type u := H.rightTranslateVanishingPluckerOrbitSpan
  let n := Module.finrank k W
  let b : Module.Basis (Fin (Module.finrank k W)) k W :=
    H.rightTranslateVanishingPluckerOrbitSpanBasis
  let ρ : Variety.Point G →* LinearMap.GeneralLinearGroup k W :=
    H.rightTranslateVanishingPluckerOrbitSpanGeneralLinear
  let p := H.rightTranslateVanishingPluckerOrbitSpanRepresentationMorphism.onPoints g
  have hp : p = generalLinearRepresentationPoint (k := k) (V := W) b (ρ g) := by
    simpa [p, b, ρ] using
      H.rightTranslateVanishingPluckerOrbitSpanRepresentationMorphism_apply g
  have hscalarForward (a : k)
      (h : ((generalLinearPointRepresentation (k := k) (Module.finrank k W)
        (generalLinearRepresentationPoint (k := k) (V := W) b (ρ g)) :
          LinearMap.GeneralLinearGroup k (Fin (Module.finrank k W) → k)) :
        Module.End k (Fin (Module.finrank k W) → k)) = a • LinearMap.id) :
      ((ρ g : LinearMap.GeneralLinearGroup k W) : Module.End k W) =
        a • LinearMap.id := by
    let nW := Module.finrank k W
    let s := generalLinearStandardIndexEquiv (k := k) nW
    let bs := generalLinearStandardBasis (k := k) nW
    let q := generalLinearRepresentationPoint (k := k) (V := W) b (ρ g)
    let ρs := generalLinearPointRepresentation (k := k) nW q
    apply b.ext
    intro j
    apply b.repr.injective
    ext i
    have hs := congrArg
      (fun f : Module.End k (Fin nW → k) => bs.repr (f (bs (s j))) (s i)) h
    have hq := generalLinearPointRepresentation_matrixCoefficient
      (k := k) nW q (s i) (s j)
    have hx := generalLinearRepresentationPoint_matrix
      (k := k) (V := W) b (ρ g) i j
    calc
      b.repr (((ρ g : LinearMap.GeneralLinearGroup k W) : Module.End k W) (b j)) i =
          q.val (Sum.inl (i, j)) := hx.symm
      _ = bs.repr ((ρs : Module.End k (Fin nW → k)) (bs (s j))) (s i) := by
        simpa [s] using hq.symm
      _ = bs.repr ((a • LinearMap.id) (bs (s j))) (s i) := hs
      _ = b.repr ((a • LinearMap.id) (b j)) i := by
        simp [bs, s, Finsupp.single_apply]
  have hcomp : (generalLinearConjugationMorphism (k := k) n).onPoints p = 1 :=
    (H.rightTranslateVanishingPluckerConjugationMorphism_apply g).symm.trans hcand
  have hbase : (generalLinearConjugationMorphism (k := k) n).onPoints
      (generalLinearRepresentationPoint (k := k) (V := W) b (ρ g)) = 1 := by
    rw [← hp]
    exact hcomp
  rw [generalLinearConjugationMorphism_apply,
    generalLinearRepresentationPoint_eq_one_iff,
    generalLinearConjugationPointRepresentation_apply,
    generalLinearConjugationRepresentation_eq_one_iff] at hbase
  rcases hbase with ⟨a, ha⟩
  have hscalarρ := hscalarForward a ha
  apply (H.chevalleyPluckerLine_stabilizer_iff g).mp
  rw [Submodule.mem_span_singleton]
  refine ⟨a, ?_⟩
  let v : H.rightTranslateVanishingPluckerOrbitSpan :=
    ⟨H.rightTranslateVanishingPluckerOrbitVector 1,
      H.rightTranslateVanishingPluckerOrbitVector_mem_span 1⟩
  have hv := LinearMap.congr_fun hscalarρ v
  have hvcoe := congrArg Subtype.val hv
  rw [H.rightTranslateVanishingPluckerOrbitSpanGeneralLinear_apply_coe] at hvcoe
  change
    ((H.rightTranslateVanishingExteriorGeneralLinear g :
      LinearMap.GeneralLinearGroup k _) : Module.End k _)
        (H.rightTranslateVanishingPluckerOrbitVector 1) =
      a • H.rightTranslateVanishingPluckerOrbitVector 1 at hvcoe
  rw [← H.rightTranslateVanishingExteriorGeneralLinear_apply]
  simpa [ClosedSubgroup.rightTranslateVanishingPluckerOrbitVector,
    linearRepresentationOrbitVector] using hvcoe.symm

end
end Theory.AlgebraicGroup

