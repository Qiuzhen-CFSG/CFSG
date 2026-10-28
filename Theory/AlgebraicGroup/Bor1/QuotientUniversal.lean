module

public import Theory.AlgebraicGroup.ClosedSubgroup.InvariantCoordinates
public import Theory.AlgebraicGroup.Isomorphism
public import Theory.AlgebraicGroup.Morphism.Reconstruction
public import Theory.AlgebraicGroup.Morphism.QuotientComparison
public import Theory.AlgebraicGroup.Quotient

universe u v

namespace Theory.AlgebraicGroup.Bor1

open Theory.AlgebraicGroup

variable {k : Type u} [Field k]

/-!
The regular part of the Bor1 quotient argument is separated into two layers.
The first layer is the geometric endpoint: if every coordinate function of a
map out of `G` is the pullback of a regular function on `Q`, then the unique
point-group lift through `π` is regular.  The generic comparison endpoint is
implemented in the lower `Morphism.QuotientComparison` module and is retained
here through compatibility wrappers for existing Bor1 clients.
-/

public theorem quotient_universal_of_surjective_coordinate_pullback
    {G Q : Variety k} [AlgebraicGroup G] [AlgebraicGroup Q]
    (H : ClosedSubgroup G) (hH : H.toSubgroup.Normal)
    (π : AlgebraicGroup.Morphism G Q)
    (hπsurj : Function.Surjective π.onPoints)
    (hπker : π.kernel = H.toSubgroup)
    (hdesc : ∀ {I : Variety k} (_ : AlgebraicGroup I)
      (φ : AlgebraicGroup.Morphism G I), H.toSubgroup ≤ φ.kernel →
      ∀ a : Variety.PolynomialFunction I,
        ∃ q : Variety.PolynomialFunction Q,
          π.toVariety.pullbackAlgHom q = φ.toVariety.pullbackAlgHom a) :
    ∀ {I : Variety k} (_ : AlgebraicGroup I)
      (φ : AlgebraicGroup.Morphism G I), H.toSubgroup ≤ φ.kernel →
      ∃! ψ : AlgebraicGroup.Morphism Q I, ψ.comp π = φ := by
  intro I _ φ hφ
  let hle : H.toSubgroup ≤ π.kernel := by rw [hπker]
  obtain ⟨ψp, hψp, -⟩ :=
    π.pointLift_existsUnique_of_surjective_kernel H hH hπsurj hπker φ hφ
  let ψ : AlgebraicGroup.Morphism Q I :=
    { toVariety :=
        { toFun := ψp
          regular := by
            intro j
            let coordinate : Variety.PolynomialFunction I :=
              Variety.PolynomialFunction.ofPolynomial I (MvPolynomial.X j)
            obtain ⟨q, hq⟩ := hdesc (inferInstance : AlgebraicGroup I) φ hφ
              coordinate
            rcases q.representedBy with ⟨p, hp⟩
            refine ⟨p, ?_⟩
            intro y
            obtain ⟨x, rfl⟩ := hπsurj y
            have hpoint := congrArg
              (fun m : Variety.Point G →* Variety.Point I => m x) hψp
            have hcoord := congrArg (fun y : Variety.Point I => y.val j) hpoint
            change (ψp (π.onPoints x)).val j = (φ.onPoints x).val j at hcoord
            have hfunx := congrArg
              (fun r : Variety.PolynomialFunction G => r x) hq
            change (ψp (π.onPoints x)).val j = evalPolynomial (π.onPoints x).val p
            rw [hcoord, ← hp (π.onPoints x)]
            change (φ.toVariety.toFun x).val j = q (π.toVariety.toFun x)
            have hfunx' :
                (φ.toVariety.pullbackAlgHom coordinate) x =
                  (π.toVariety.pullbackAlgHom q) x := hfunx.symm
            change coordinate (φ.toVariety.toFun x) =
              q (π.toVariety.toFun x) at hfunx'
            simpa [Morphism.pullbackToRightInvariantCoordinateRing_apply,
              Variety.PolynomialFunction.pullback, coordinate,
              Variety.PolynomialFunction.ofPolynomial,
              Variety.PolynomialFunction.toFun, evalPolynomial] using hfunx' }
      map_one := ψp.map_one
      map_mul := ψp.map_mul }
  have hψ : ψ.comp π = φ := by
    apply Morphism.ext
    funext x
    change ψ.onPoints (π.onPoints x) = φ.onPoints x
    change ψp (π.onPoints x) = φ.onPoints x
    exact congrArg (fun m : Variety.Point G →* Variety.Point I => m x) hψp
  refine ⟨ψ, hψ, ?_⟩
  intro ψ' hψ'
  apply Morphism.ext
  funext y
  obtain ⟨x, rfl⟩ := hπsurj y
  have hψ'point := congrArg
    (fun m : AlgebraicGroup.Morphism G I => m.onPoints x) hψ'
  have hψpoint := congrArg
    (fun m : AlgebraicGroup.Morphism G I => m.onPoints x) hψ
  change ψ'.onPoints (π.onPoints x) = φ.onPoints x at hψ'point
  change ψ.onPoints (π.onPoints x) = φ.onPoints x at hψpoint
  exact hψ'point.trans hψpoint.symm

/-! Compatibility wrappers for the lower comparison API. -/

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
    ∃! ψ : AlgebraicGroup.Morphism Q₁ Q₂, ψ.comp π₁ = π₂ :=
  Theory.AlgebraicGroup.quotient_comparison_existsUnique_of_surjective_kernel_eq_of_coordinate_factorization
    π₁ π₂ hπ₁surj hker hfactor

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
      e.hom.comp π₁ = π₂ ∧ e.inv.comp π₂ = π₁ :=
  Theory.AlgebraicGroup.quotient_comparison_iso_of_surjective_kernel_eq_of_coordinate_factorization
    π₁ π₂ hπ₁surj hπ₂surj hker hfactor₁₂ hfactor₂₁

public theorem quotient_comparison_existsUnique_of_surjective_kernel_eq_of_pullback_surjective
    {G Q₁ Q₂ : Variety k} [AlgebraicGroup G] [AlgebraicGroup Q₁]
    [AlgebraicGroup Q₂]
    (π₁ : AlgebraicGroup.Morphism G Q₁)
    (π₂ : AlgebraicGroup.Morphism G Q₂)
    (hπ₁surj : Function.Surjective π₁.onPoints)
    (hker : π₁.kernel = π₂.kernel)
    (hpull₁ : Function.Surjective π₁.toVariety.pullbackRingHom) :
    ∃! ψ : AlgebraicGroup.Morphism Q₁ Q₂, ψ.comp π₁ = π₂ :=
  Theory.AlgebraicGroup.quotient_comparison_existsUnique_of_surjective_kernel_eq_of_pullback_surjective
    π₁ π₂ hπ₁surj hker hpull₁

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
      e.hom.comp π₁ = π₂ ∧ e.inv.comp π₂ = π₁ :=
  Theory.AlgebraicGroup.quotient_comparison_iso_of_surjective_kernel_eq_of_pullback_surjective
    π₁ π₂ hπ₁surj hπ₂surj hker hpull₁ hpull₂

/-!
The second Bor1 layer supplies coordinate factorisation from the stronger
invariant-ring statement.  Regularity then follows from the lower comparison
and coordinate-descent infrastructure.
-/

public theorem quotient_universal_of_surjective_invariant_pullback
    {G Q : Variety k} [AlgebraicGroup G] [AlgebraicGroup Q]
    (H : ClosedSubgroup G) (hH : H.toSubgroup.Normal)
    (π : AlgebraicGroup.Morphism G Q)
    (hπsurj : Function.Surjective π.onPoints)
    (hπker : π.kernel = H.toSubgroup)
    (hpull : Function.Surjective
      (π.pullbackToRightInvariantCoordinateRing H (by rw [hπker]))) :
    ∀ {I : Variety k} (_ : AlgebraicGroup I)
      (φ : AlgebraicGroup.Morphism G I), H.toSubgroup ≤ φ.kernel →
      ∃! ψ : AlgebraicGroup.Morphism Q I, ψ.comp π = φ := by
  have hdesc : ∀ {I : Variety k} (_ : AlgebraicGroup I)
      (φ : AlgebraicGroup.Morphism G I), H.toSubgroup ≤ φ.kernel →
      ∀ a : Variety.PolynomialFunction I,
        ∃ q : Variety.PolynomialFunction Q,
          π.toVariety.pullbackAlgHom q = φ.toVariety.pullbackAlgHom a := by
    intro I _ φ hφ a
    obtain ⟨q, hq⟩ := hpull
      (φ.pullbackToRightInvariantCoordinateRing H hφ a)
    refine ⟨q, ?_⟩
    exact congrArg Subtype.val hq
  intro I hI φ hφ
  exact (quotient_universal_of_surjective_coordinate_pullback
    H hH π hπsurj hπker hdesc) hI φ hφ

end Theory.AlgebraicGroup.Bor1
