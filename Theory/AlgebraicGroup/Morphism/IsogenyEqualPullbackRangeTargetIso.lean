module

public import Theory.AlgebraicGroup.RootSystems.AlgebraicGroups.theorem_1_10_4_b

public import Theory.AlgebraicGroup.RootSystems.AlgebraicGroups.ClassicalPointGroups

/-!
Fiber staging module for the regular comparison of two isogeny targets.  Equality
of the pullback ranges supplies reciprocal coordinate factorizations.  In each
direction, equality of point kernels gives a point-group lift, while the
factorization represents every coordinate of that lift by a polynomial and
hence proves regularity.  Source-point surjectivity then makes the two comparison
morphisms inverse and yields the target isomorphism.
-/

set_option warningAsError false

universe u

namespace Theory.AlgebraicGroup

public theorem isogeny_target_iso_of_equal_pullback_ranges
    {k : Type u} [Field k] [IsAlgClosed k]
    {U G H : Variety k} [AlgebraicGroup U] [AlgebraicGroup G] [AlgebraicGroup H]
    (φ : AlgebraicGroup.Morphism U G) (ψ : AlgebraicGroup.Morphism U H)
    (hφ : IsIsogeny φ) (hψ : IsIsogeny ψ)
    (hker : φ.kernel = ψ.kernel)
    (hrange : Set.range φ.toVariety.pullbackRingHom =
      Set.range ψ.toVariety.pullbackRingHom) :
    ∃ e : AlgebraicGroup.Iso G H,
      e.hom.comp φ = ψ ∧ e.inv.comp ψ = φ := by
  have comparison : ∀ {Q₁ Q₂ : Variety k} [AlgebraicGroup Q₁]
      [AlgebraicGroup Q₂]
      (π₁ : AlgebraicGroup.Morphism U Q₁)
      (π₂ : AlgebraicGroup.Morphism U Q₂),
      Function.Surjective π₁.onPoints →
      π₁.kernel = π₂.kernel →
      (∀ a : Variety.PolynomialFunction Q₂,
        ∃ q : Variety.PolynomialFunction Q₁,
          π₁.toVariety.pullbackAlgHom q = π₂.toVariety.pullbackAlgHom a) →
      ∃! f : AlgebraicGroup.Morphism Q₁ Q₂, f.comp π₁ = π₂ := by
    intro Q₁ Q₂ _ _ π₁ π₂ hπ₁surj hπker hfactor
    let K : ClosedSubgroup U := π₁.kernelClosedSubgroup
    have hKnormal : K.toSubgroup.Normal := π₁.kernelClosedSubgroup_isNormal
    have hπ₁ker : π₁.kernel = K.toSubgroup := rfl
    have hπ₂kill : K.toSubgroup ≤ π₂.kernel := by
      rw [show K.toSubgroup = π₁.kernel from rfl, hπker]
    obtain ⟨fp, hfp, _⟩ :=
      π₁.pointLift_existsUnique_of_surjective_kernel K hKnormal
        hπ₁surj hπ₁ker π₂ hπ₂kill
    let f : AlgebraicGroup.Morphism Q₁ Q₂ :=
      { toVariety :=
          { toFun := fp
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
                (fun m : Variety.Point U →* Variety.Point Q₂ => m x) hfp
              have hcoord := congrArg (fun z : Variety.Point Q₂ => z.val j) hpoint
              change (fp (π₁.onPoints x)).val j = (π₂.onPoints x).val j at hcoord
              have hfunx := congrArg
                (fun r : Variety.PolynomialFunction U => r x) hq
              change (fp (π₁.onPoints x)).val j =
                evalPolynomial (π₁.onPoints x).val p
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
        map_one := fp.map_one
        map_mul := fp.map_mul }
    have hf : f.comp π₁ = π₂ := by
      apply AlgebraicGroup.Morphism.ext
      funext x
      change f.onPoints (π₁.onPoints x) = π₂.onPoints x
      change fp (π₁.onPoints x) = π₂.onPoints x
      exact congrArg (fun m : Variety.Point U →* Variety.Point Q₂ => m x) hfp
    refine ⟨f, hf, ?_⟩
    intro f' hf'
    apply AlgebraicGroup.Morphism.ext
    funext y
    obtain ⟨x, rfl⟩ := hπ₁surj y
    have hf'point := congrArg
      (fun m : AlgebraicGroup.Morphism U Q₂ => m.onPoints x) hf'
    have hfpoint := congrArg
      (fun m : AlgebraicGroup.Morphism U Q₂ => m.onPoints x) hf
    change f'.onPoints (π₁.onPoints x) = π₂.onPoints x at hf'point
    change f.onPoints (π₁.onPoints x) = π₂.onPoints x at hfpoint
    exact hf'point.trans hfpoint.symm
  have hfactor₁₂ : ∀ a : Variety.PolynomialFunction H,
      ∃ q : Variety.PolynomialFunction G,
        φ.toVariety.pullbackAlgHom q = ψ.toVariety.pullbackAlgHom a := by
    intro a
    have ha : ψ.toVariety.pullbackRingHom a ∈
        Set.range φ.toVariety.pullbackRingHom := by
      rw [hrange]
      exact ⟨a, rfl⟩
    obtain ⟨q, hq⟩ := ha
    exact ⟨q, hq⟩
  have hfactor₂₁ : ∀ a : Variety.PolynomialFunction G,
      ∃ q : Variety.PolynomialFunction H,
        ψ.toVariety.pullbackAlgHom q = φ.toVariety.pullbackAlgHom a := by
    intro a
    have ha : φ.toVariety.pullbackRingHom a ∈
        Set.range ψ.toVariety.pullbackRingHom := by
      rw [← hrange]
      exact ⟨a, rfl⟩
    obtain ⟨q, hq⟩ := ha
    exact ⟨q, hq⟩
  obtain ⟨f₁₂, hf₁₂, _⟩ := comparison φ ψ hφ.1 hker hfactor₁₂
  obtain ⟨f₂₁, hf₂₁, _⟩ := comparison ψ φ hψ.1 hker.symm hfactor₂₁
  have hleft : ∀ x : Variety.Point G, f₂₁.onPoints (f₁₂.onPoints x) = x := by
    intro x
    obtain ⟨u, rfl⟩ := hφ.1 x
    have hf₁₂point := congrArg
      (fun f : AlgebraicGroup.Morphism U H => f.onPoints u) hf₁₂
    change f₁₂.onPoints (φ.onPoints u) = ψ.onPoints u at hf₁₂point
    calc
      f₂₁.onPoints (f₁₂.onPoints (φ.onPoints u)) =
          f₂₁.onPoints (ψ.onPoints u) := congrArg f₂₁.onPoints hf₁₂point
      _ = φ.onPoints u := by
        have hf₂₁point := congrArg
          (fun f : AlgebraicGroup.Morphism U G => f.onPoints u) hf₂₁
        exact hf₂₁point
  have hright : ∀ y : Variety.Point H, f₁₂.onPoints (f₂₁.onPoints y) = y := by
    intro y
    obtain ⟨u, rfl⟩ := hψ.1 y
    have hf₂₁point := congrArg
      (fun f : AlgebraicGroup.Morphism U G => f.onPoints u) hf₂₁
    change f₂₁.onPoints (ψ.onPoints u) = φ.onPoints u at hf₂₁point
    calc
      f₁₂.onPoints (f₂₁.onPoints (ψ.onPoints u)) =
          f₁₂.onPoints (φ.onPoints u) := congrArg f₁₂.onPoints hf₂₁point
      _ = ψ.onPoints u := by
        have hf₁₂point := congrArg
          (fun f : AlgebraicGroup.Morphism U H => f.onPoints u) hf₁₂
        exact hf₁₂point
  refine ⟨({ hom := f₁₂, inv := f₂₁, hom_inv_id := hleft, inv_hom_id := hright } :
    AlgebraicGroup.Iso G H), ?_, ?_⟩
  · exact hf₁₂
  · exact hf₂₁

end Theory.AlgebraicGroup
