module

public import Theory.AlgebraicGroup.Automorphisms.Lang.theorem_2_1_1
public import Mathlib.FieldTheory.Finite.Basic

/-!
This module records the faithful matrix-realization input used in the St1
converse to the Steinberg--Frobenius theorem.  A representation package
specifies a closed subgroup of `GL_n`, an algebraic-group isomorphism onto it,
root-element generation, and the Lemma 34 assertion that every root-element
matrix coordinate is a polynomial over the prime field.  Evaluating such a
polynomial after an `r^a`-power gives the entrywise matrix Frobenius formula;
the final closure-induction theorem extends that formula from root elements to
all points whenever an endomorphism has the corresponding root formula.
The polynomial coordinate assertion is deliberately an explicit field of the
package: constructing the Chevalley representation and its prime-field basis
is a separate geometric input, while all consequences used by the Lang proof
are proved here.  The coordinate calculation follows GLS3, Chapter 2, St1,
Lemma 34 (the root-element exponential in a weight-vector basis).
-/

universe u

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

set_option linter.style.haveILetI false

/-- The canonical map from the prime field `ZMod r` into a field of
characteristic `r`. -/
@[expose]
public def st1PrimeFieldMap (r : ℕ) [CharP k r] : ZMod r →+* k :=
  ZMod.castHom (dvd_refl r) k

/-- A scalar function is given by a polynomial with prime-field coefficients. -/
@[expose]
public def IsSt1PrimeFieldPolynomial (r : ℕ) [CharP k r] (f : k → k) : Prop :=
  ∃ p : Polynomial (ZMod r), ∀ t, f t = p.eval₂ (st1PrimeFieldMap (k := k) r) t

omit [IsAlgClosed k] in
public theorem st1PrimeFieldPolynomial_eval_frobenius
    {r : ℕ} [Fact r.Prime] [CharP k r]
    (p : Polynomial (ZMod r)) (t : k) (a : ℕ) :
    p.eval₂ (st1PrimeFieldMap (k := k) r) (t ^ (r ^ a)) =
      (p.eval₂ (st1PrimeFieldMap (k := k) r) t) ^ (r ^ a) := by
  let f : ZMod r →+* k := st1PrimeFieldMap (k := k) r
  have hf : (iterateFrobenius k r a).comp f = f := by
    apply RingHom.ext
    intro z
    calc
      ((iterateFrobenius k r a).comp f) z =
          (f.comp (iterateFrobenius (ZMod r) r a)) z := by
            rw [← RingHom.iterateFrobenius_comm f r a]
      _ = f z := by
        rw [RingHom.comp_apply, iterateFrobenius_def]
        simp
  calc
    p.eval₂ f (t ^ (r ^ a)) =
        p.eval₂ f ((iterateFrobenius k r a) t) := by
          rw [iterateFrobenius_def]
    _ = (iterateFrobenius k r a) (p.eval₂ f t) := by
      rw [Polynomial.hom_eval₂]
      rw [hf]
    _ = (p.eval₂ f t) ^ (r ^ a) := by
      rw [iterateFrobenius_def]

/-- A St1 Lemma 34 matrix package for Chevalley root elements.

The `embedding` field is an algebraic-group isomorphism onto a closed
subgroup of `GL_n`; hence it is both a faithful representation and a closed
embedding.  The `coordinates` field is the prime-field polynomial assertion
for every root element and every matrix entry. -/
public structure St1PrimeFieldMatrixRepresentation
    {K : Variety k} [AlgebraicGroup K]
    {T : ClosedSubgroup K} (D : RootGroupData K T)
    (C : ChevalleyData K D) (r : ℕ)
    [Fact r.Prime] [CharP k r] where
  n : ℕ
  H : ClosedSubgroup (glVariety n : Variety k)
  embedding : @AlgebraicGroup.Iso k _ K H.carrierVariety _ H.carrierAlgebraicGroup
  generation : HasChevalleyRootGeneration D C
  coordinates : let _ := H.carrierAlgebraicGroup; ∀ (α : D.Root) (i j : Fin n),
    IsSt1PrimeFieldPolynomial (k := k) r
      (fun t => glMatrixOfPoint n
        (H.inclusion.onPoints (embedding.hom.onPoints (C.x α t))) i j)

/-- The closed embedding into the ambient general-linear group. -/
public noncomputable def St1PrimeFieldMatrixRepresentation.embeddingMorphism
    {K : Variety k} [AlgebraicGroup K]
    {T : ClosedSubgroup K} {D : RootGroupData K T}
    {C : ChevalleyData K D} {r : ℕ}
    [Fact r.Prime] [CharP k r]
    (R : St1PrimeFieldMatrixRepresentation D C r) :
    Morphism K (glVariety R.n) := by
  letI := R.H.carrierAlgebraicGroup
  exact R.H.inclusion.comp R.embedding.hom

/-- The point map of the closed matrix realization. -/
public noncomputable def St1PrimeFieldMatrixRepresentation.point
    {K : Variety k} [AlgebraicGroup K]
    {T : ClosedSubgroup K} {D : RootGroupData K T}
    {C : ChevalleyData K D} {r : ℕ}
    [Fact r.Prime] [CharP k r]
    (R : St1PrimeFieldMatrixRepresentation D C r) :
    Variety.Point K →* GL (Fin R.n) k := by
  letI := R.H.carrierAlgebraicGroup
  exact
    { toFun := fun x =>
        translationGLPointMulEquiv R.n
          (R.H.inclusion.onPoints (R.embedding.hom.onPoints x))
      map_one' := by simp
      map_mul' := by simp }

omit [IsAlgClosed k] in
/-- The matrix point map is faithful. -/
public theorem St1PrimeFieldMatrixRepresentation.point_injective
    {K : Variety k} [AlgebraicGroup K]
    {T : ClosedSubgroup K} {D : RootGroupData K T}
    {C : ChevalleyData K D} {r : ℕ}
    [Fact r.Prime] [CharP k r]
    (R : St1PrimeFieldMatrixRepresentation D C r) :
    Function.Injective R.point := by
  letI := R.H.carrierAlgebraicGroup
  intro x y hxy
  have hpoint :
      R.H.inclusion.onPoints (R.embedding.hom.onPoints x) =
        R.H.inclusion.onPoints (R.embedding.hom.onPoints y) := by
    apply (glPointEquiv R.n).injective
    exact hxy
  have hhom : R.embedding.hom.onPoints x = R.embedding.hom.onPoints y :=
    R.H.inclusion_injective hpoint
  have hinv := congrArg R.embedding.inv.onPoints hhom
  simpa only [R.embedding.hom_inv_id] using hinv

/-- The matrix of a root element in the chosen realization. -/
public noncomputable def St1PrimeFieldMatrixRepresentation.matrixPoint
    {K : Variety k} [AlgebraicGroup K]
    {T : ClosedSubgroup K} {D : RootGroupData K T}
    {C : ChevalleyData K D} {r : ℕ}
    [Fact r.Prime] [CharP k r]
    (R : St1PrimeFieldMatrixRepresentation D C r)
    (α : D.Root) (t : k) : GL (Fin R.n) k :=
  R.point (C.x α t)

omit [IsAlgClosed k] in
/-- Every root-element matrix entry commutes with an `r^a`-power. -/
public theorem St1PrimeFieldMatrixRepresentation.matrixPoint_entry_frobenius
    {K : Variety k} [AlgebraicGroup K]
    {T : ClosedSubgroup K} {D : RootGroupData K T}
    {C : ChevalleyData K D} {r : ℕ}
    [Fact r.Prime] [CharP k r]
    (R : St1PrimeFieldMatrixRepresentation D C r)
    (α : D.Root) (t : k) (a : ℕ) (i j : Fin R.n) :
    ((R.matrixPoint α (t ^ (r ^ a)) : GL (Fin R.n) k) :
        Matrix (Fin R.n) (Fin R.n) k) i j =
      (((R.matrixPoint α t : GL (Fin R.n) k) :
        Matrix (Fin R.n) (Fin R.n) k) i j) ^ (r ^ a) := by
  letI := R.H.carrierAlgebraicGroup
  rcases R.coordinates α i j with ⟨p, hp⟩
  change glMatrixOfPoint R.n
      (R.H.inclusion.onPoints (R.embedding.hom.onPoints (C.x α (t ^ (r ^ a))))) i j =
    glMatrixOfPoint R.n
      (R.H.inclusion.onPoints (R.embedding.hom.onPoints (C.x α t))) i j ^ (r ^ a)
  have hp' (s : k) :
      glMatrixOfPoint R.n
          (R.H.inclusion.onPoints (R.embedding.hom.onPoints (C.x α s))) i j =
        p.eval₂ (st1PrimeFieldMap (k := k) r) s := by
    simpa only using hp s
  rw [hp' (t ^ (r ^ a)), hp' t]
  exact st1PrimeFieldPolynomial_eval_frobenius p t a

omit [IsAlgClosed k] in
/-- The root-element point itself is carried to entrywise matrix Frobenius. -/
public theorem St1PrimeFieldMatrixRepresentation.matrixPoint_frobenius
    {K : Variety k} [AlgebraicGroup K]
    {T : ClosedSubgroup K} {D : RootGroupData K T}
    {C : ChevalleyData K D} {r : ℕ}
    [Fact r.Prime] [CharP k r]
    (R : St1PrimeFieldMatrixRepresentation D C r)
    (α : D.Root) (t : k) (a : ℕ) :
    R.matrixPoint α (t ^ (r ^ a)) =
      generalLinearFrobenius (k := k) R.n r a (R.matrixPoint α t) := by
  letI := R.H.carrierAlgebraicGroup
  apply Units.ext
  funext i j
  exact R.matrixPoint_entry_frobenius α t a i j

omit [IsAlgClosed k] in
/-- Root-generator Frobenius compatibility extends to every group point. -/
public theorem St1PrimeFieldMatrixRepresentation.point_frobenius_of_root_formula
    {K : Variety k} [AlgebraicGroup K]
    {T : ClosedSubgroup K} {D : RootGroupData K T}
    {C : ChevalleyData K D} {r : ℕ}
    [Fact r.Prime] [CharP k r]
    (R : St1PrimeFieldMatrixRepresentation D C r)
    (σ : AlgebraicGroup.Morphism K K) (a : ℕ)
    (hσ : ∀ α t, σ.onPoints (C.x α t) = C.x α (t ^ (r ^ a))) :
    ∀ x : Variety.Point K,
      R.point (σ.onPoints x) =
        generalLinearFrobenius (k := k) R.n r a (R.point x) := by
  letI := R.H.carrierAlgebraicGroup
  intro x
  have hx : x ∈ Subgroup.closure (ChevalleyRootElementSet D C) := by
    rw [R.generation]
    exact Subgroup.mem_top x
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
      change x ∈ Set.range (fun z : D.Root × k => C.x z.1 z.2) at hx
      obtain ⟨⟨α, t⟩, rfl⟩ := hx
      rw [hσ]
      exact R.matrixPoint_frobenius α t a
  | one => simp
  | mul x y _ _ hx hy => simp [hx, hy]
  | inv x _ hx => simp [hx]

end Theory.AlgebraicGroup
