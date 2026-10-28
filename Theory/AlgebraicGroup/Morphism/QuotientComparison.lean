module

public import Theory.AlgebraicGroup.Isomorphism
public import Theory.AlgebraicGroup.Quotient
public import Theory.AlgebraicGroup.Morphism.Isogeny

universe u

/-!
Coordinate-factorisation comparison for geometric quotient presentations.

The point-surjective presentation `G → Q₁` determines a unique point-group
comparison to a second presentation with the same kernel.  Reciprocal
factorisation of polynomial coordinates is the precise regularity input: it
expresses that each target coordinate descends to the other quotient, without
requiring pullback onto the full coordinate ring of `G`.  This module is kept
below the Bor1 development so root-data and other quotient consumers can use
the comparison interface without an upward import.

There is deliberately no isogeny comparison from point-kernel equality alone.
`IsIsogeny` records only point-surjectivity and finiteness of the point kernel,
while the characteristic-two B/C alternative in GLS3, Theorem 1.10.4(a), and
the discussion after Theorem 1.10.7 exhibit inseparable morphisms that need not
be algebraic-group isomorphisms even when they are bijective on points.  The
isogeny-facing endpoint therefore keeps reciprocal coordinate factorisation as
the missing regular quotient data.
-/

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k]

/-! The comparison endpoint with the coordinate hypothesis stated directly. -/

/-- A point-surjective morphism admits a unique regular comparison map whenever
the target coordinates of the second morphism factor through its pullback. -/
public theorem quotient_comparison_existsUnique_of_surjective_kernel_eq_of_coordinate_factorization
    {G Q₁ Q₂ : Variety k} [AlgebraicGroup G] [AlgebraicGroup Q₁]
    [AlgebraicGroup Q₂]
    (π₁ : AlgebraicGroup.Morphism G Q₁)
    (π₂ : AlgebraicGroup.Morphism G Q₂)
    (hπ₁surj : Function.Surjective π₁.onPoints)
    (hker : π₁.kernel = π₂.kernel)
    (hfactor : ∀ a : Variety.PolynomialFunction Q₂,
      ∃ q : Variety.PolynomialFunction Q₁,
        π₁.toVariety.pullbackAlgHom q = π₂.toVariety.pullbackAlgHom a) :
    ∃! ψ : AlgebraicGroup.Morphism Q₁ Q₂, ψ.comp π₁ = π₂ := by
  let H : ClosedSubgroup G := π₁.kernelClosedSubgroup
  have hHnormal : H.toSubgroup.Normal := π₁.kernelClosedSubgroup_isNormal
  have hπ₁ker : π₁.kernel = H.toSubgroup := rfl
  have hπ₂kill : H.toSubgroup ≤ π₂.kernel := by
    rw [show H.toSubgroup = π₁.kernel from rfl, hker]
  obtain ⟨ψp, hψp, _⟩ :=
    π₁.pointLift_existsUnique_of_surjective_kernel H hHnormal
      hπ₁surj hπ₁ker π₂ hπ₂kill
  let ψ : AlgebraicGroup.Morphism Q₁ Q₂ :=
    { toVariety :=
        { toFun := ψp
          regular := by
            intro j
            let coordinate : Variety.PolynomialFunction Q₂ :=
              Variety.PolynomialFunction.ofPolynomial Q₂ (MvPolynomial.X j)
            obtain ⟨q, hq⟩ := hfactor coordinate
            rcases q.representedBy with ⟨p, hp⟩
            refine ⟨p, ?_⟩
            intro y
            obtain ⟨x, rfl⟩ := hπ₁surj y
            have hpoint := congrArg
              (fun m : Variety.Point G →* Variety.Point Q₂ => m x) hψp
            have hcoord := congrArg (fun y : Variety.Point Q₂ => y.val j) hpoint
            change (ψp (π₁.onPoints x)).val j = (π₂.onPoints x).val j at hcoord
            have hfunx := congrArg
              (fun r : Variety.PolynomialFunction G => r x) hq
            change (ψp (π₁.onPoints x)).val j = evalPolynomial (π₁.onPoints x).val p
            rw [hcoord, ← hp (π₁.onPoints x)]
            change (π₂.toVariety.toFun x).val j = q (π₁.toVariety.toFun x)
            have hfunx' :
                (π₂.toVariety.pullbackAlgHom coordinate) x =
                  (π₁.toVariety.pullbackAlgHom q) x := hfunx.symm
            change coordinate (π₂.toVariety.toFun x) =
              q (π₁.toVariety.toFun x) at hfunx'
            simpa [Variety.PolynomialFunction.pullback, coordinate,
              Variety.PolynomialFunction.ofPolynomial,
              Variety.PolynomialFunction.toFun, evalPolynomial] using hfunx' }
      map_one := ψp.map_one
      map_mul := ψp.map_mul }
  have hcomp : ψ.comp π₁ = π₂ := by
    apply AlgebraicGroup.Morphism.ext
    funext g
    change ψ.onPoints (π₁.onPoints g) = π₂.onPoints g
    change ψp (π₁.onPoints g) = π₂.onPoints g
    exact congrArg (fun m : Variety.Point G →* Variety.Point Q₂ => m g) hψp
  refine ⟨ψ, hcomp, ?_⟩
  intro ψ' hψ'
  apply AlgebraicGroup.Morphism.ext
  funext x
  obtain ⟨g, rfl⟩ := hπ₁surj x
  have hψ'point := congrArg
    (fun m : AlgebraicGroup.Morphism G Q₂ => m.onPoints g) hψ'
  have hψpoint := congrArg
    (fun m : AlgebraicGroup.Morphism G Q₂ => m.onPoints g) hcomp
  change ψ'.onPoints (π₁.onPoints g) = π₂.onPoints g at hψ'point
  change ψ.onPoints (π₁.onPoints g) = π₂.onPoints g at hψpoint
  exact hψ'point.trans hψpoint.symm

/-- Two point-surjective presentations with equal kernels and reciprocal
coordinate factorisations have isomorphic algebraic-group targets. -/
public theorem quotient_comparison_iso_of_surjective_kernel_eq_of_coordinate_factorization
    {G Q₁ Q₂ : Variety k} [AlgebraicGroup G] [AlgebraicGroup Q₁]
    [AlgebraicGroup Q₂]
    (π₁ : AlgebraicGroup.Morphism G Q₁)
    (π₂ : AlgebraicGroup.Morphism G Q₂)
    (hπ₁surj : Function.Surjective π₁.onPoints)
    (hπ₂surj : Function.Surjective π₂.onPoints)
    (hker : π₁.kernel = π₂.kernel)
    (hfactor₁₂ : ∀ a : Variety.PolynomialFunction Q₂,
      ∃ q : Variety.PolynomialFunction Q₁,
        π₁.toVariety.pullbackAlgHom q = π₂.toVariety.pullbackAlgHom a)
    (hfactor₂₁ : ∀ a : Variety.PolynomialFunction Q₁,
      ∃ q : Variety.PolynomialFunction Q₂,
        π₂.toVariety.pullbackAlgHom q = π₁.toVariety.pullbackAlgHom a) :
    ∃ e : AlgebraicGroup.Iso Q₁ Q₂,
      e.hom.comp π₁ = π₂ ∧ e.inv.comp π₂ = π₁ := by
  obtain ⟨f₁₂, hf₁₂, _⟩ :=
    quotient_comparison_existsUnique_of_surjective_kernel_eq_of_coordinate_factorization
      π₁ π₂ hπ₁surj hker hfactor₁₂
  obtain ⟨f₂₁, hf₂₁, _⟩ :=
    quotient_comparison_existsUnique_of_surjective_kernel_eq_of_coordinate_factorization
      π₂ π₁ hπ₂surj hker.symm hfactor₂₁
  have hleft : ∀ x : Variety.Point Q₁, f₂₁.onPoints (f₁₂.onPoints x) = x := by
    intro x
    obtain ⟨g, rfl⟩ := hπ₁surj x
    have hcomp12point := congrArg
      (fun f : AlgebraicGroup.Morphism G Q₂ => f.onPoints g) hf₁₂
    change f₁₂.onPoints (π₁.onPoints g) = π₂.onPoints g at hcomp12point
    calc
      f₂₁.onPoints (f₁₂.onPoints (π₁.onPoints g)) =
          f₂₁.onPoints (π₂.onPoints g) := by
            exact congrArg f₂₁.onPoints hcomp12point
      _ = π₁.onPoints g := by
        have hcomp21point := congrArg
          (fun f : AlgebraicGroup.Morphism G Q₁ => f.onPoints g) hf₂₁
        change f₂₁.onPoints (π₂.onPoints g) = π₁.onPoints g at hcomp21point
        exact hcomp21point
  have hright : ∀ y : Variety.Point Q₂, f₁₂.onPoints (f₂₁.onPoints y) = y := by
    intro y
    obtain ⟨g, rfl⟩ := hπ₂surj y
    have hcomp21point := congrArg
      (fun f : AlgebraicGroup.Morphism G Q₁ => f.onPoints g) hf₂₁
    change f₂₁.onPoints (π₂.onPoints g) = π₁.onPoints g at hcomp21point
    calc
      f₁₂.onPoints (f₂₁.onPoints (π₂.onPoints g)) =
          f₁₂.onPoints (π₁.onPoints g) := by
            exact congrArg f₁₂.onPoints hcomp21point
      _ = π₂.onPoints g := by
        have hcomp12point := congrArg
          (fun f : AlgebraicGroup.Morphism G Q₂ => f.onPoints g) hf₁₂
        change f₁₂.onPoints (π₁.onPoints g) = π₂.onPoints g at hcomp12point
        exact hcomp12point
  refine ⟨({ hom := f₁₂, inv := f₂₁, hom_inv_id := hleft, inv_hom_id := hright } :
    AlgebraicGroup.Iso Q₁ Q₂), ?_, ?_⟩
  · exact hf₁₂
  · exact hf₂₁

/-! Convenience wrappers for the stronger full-pullback hypothesis. -/

/-- A point-surjective morphism with surjective polynomial pullback has a
unique regular comparison map to any morphism with the same point-kernel. -/
public theorem quotient_comparison_existsUnique_of_surjective_kernel_eq_of_pullback_surjective
    {G Q₁ Q₂ : Variety k} [AlgebraicGroup G] [AlgebraicGroup Q₁]
    [AlgebraicGroup Q₂]
    (π₁ : AlgebraicGroup.Morphism G Q₁)
    (π₂ : AlgebraicGroup.Morphism G Q₂)
    (hπ₁surj : Function.Surjective π₁.onPoints)
    (hker : π₁.kernel = π₂.kernel)
    (hpull₁ : Function.Surjective π₁.toVariety.pullbackRingHom) :
    ∃! ψ : AlgebraicGroup.Morphism Q₁ Q₂, ψ.comp π₁ = π₂ := by
  apply quotient_comparison_existsUnique_of_surjective_kernel_eq_of_coordinate_factorization
    π₁ π₂ hπ₁surj hker
  intro a
  obtain ⟨q, hq⟩ := hpull₁ (Variety.PolynomialFunction.pullback π₂.toVariety a)
  exact ⟨q, hq⟩

/-- Two point-surjective quotient presentations with equal kernels and
surjective polynomial pullbacks have isomorphic algebraic-group targets. -/
public theorem quotient_comparison_iso_of_surjective_kernel_eq_of_pullback_surjective
    {G Q₁ Q₂ : Variety k} [AlgebraicGroup G] [AlgebraicGroup Q₁]
    [AlgebraicGroup Q₂]
    (π₁ : AlgebraicGroup.Morphism G Q₁)
    (π₂ : AlgebraicGroup.Morphism G Q₂)
    (hπ₁surj : Function.Surjective π₁.onPoints)
    (hπ₂surj : Function.Surjective π₂.onPoints)
    (hker : π₁.kernel = π₂.kernel)
    (hpull₁ : Function.Surjective π₁.toVariety.pullbackRingHom)
    (hpull₂ : Function.Surjective π₂.toVariety.pullbackRingHom) :
    ∃ e : AlgebraicGroup.Iso Q₁ Q₂,
      e.hom.comp π₁ = π₂ ∧ e.inv.comp π₂ = π₁ := by
  apply quotient_comparison_iso_of_surjective_kernel_eq_of_coordinate_factorization
    π₁ π₂ hπ₁surj hπ₂surj hker
  · intro a
    obtain ⟨q, hq⟩ := hpull₁ (Variety.PolynomialFunction.pullback π₂.toVariety a)
    exact ⟨q, hq⟩
  · intro a
    obtain ⟨q, hq⟩ := hpull₂ (Variety.PolynomialFunction.pullback π₁.toVariety a)
    exact ⟨q, hq⟩

/-! Isogeny-facing contract repair.  Point-kernel equality alone is not a
regular quotient uniqueness principle in positive characteristic; the
factorisation hypotheses below retain the missing coordinate descent data. -/

/-- Isogenies with equal point kernels have isomorphic targets when the two
quotient presentations satisfy reciprocal coordinate factorisation. -/
public theorem isogeny_target_iso_of_kernel_eq_of_coordinate_factorization
    {G Q₁ Q₂ : Variety k} [AlgebraicGroup G] [AlgebraicGroup Q₁]
    [AlgebraicGroup Q₂]
    (π₁ : AlgebraicGroup.Morphism G Q₁)
    (π₂ : AlgebraicGroup.Morphism G Q₂)
    (hπ₁ : IsIsogeny π₁) (hπ₂ : IsIsogeny π₂)
    (hker : π₁.kernel = π₂.kernel)
    (hfactor₁₂ : ∀ a : Variety.PolynomialFunction Q₂,
      ∃ q : Variety.PolynomialFunction Q₁,
        π₁.toVariety.pullbackAlgHom q = π₂.toVariety.pullbackAlgHom a)
    (hfactor₂₁ : ∀ a : Variety.PolynomialFunction Q₁,
      ∃ q : Variety.PolynomialFunction Q₂,
        π₂.toVariety.pullbackAlgHom q = π₁.toVariety.pullbackAlgHom a) :
    ∃ e : AlgebraicGroup.Iso Q₁ Q₂,
      e.hom.comp π₁ = π₂ ∧ e.inv.comp π₂ = π₁ := by
  exact quotient_comparison_iso_of_surjective_kernel_eq_of_coordinate_factorization
    π₁ π₂ hπ₁.1 hπ₂.1 hker hfactor₁₂ hfactor₂₁

end Theory.AlgebraicGroup
