module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Passage
public import Theory.AlgebraicGroup.Automorphisms.Lang.Basic
public import Theory.AlgebraicGroup.Variety.Iterate
public import Theory.AlgebraicGroup.Morphism.CodRestrict
public import Theory.AlgebraicGroup.Automorphisms.Steinberg

/-!
# Regular graph-field maps on point centralizers

The graph-field point endomorphism is realized by a regular morphism. Its
restriction to the closed centralizer of a fixed point is bijective on points
and has finitely many fixed points for every positive exponent. Consequently,
Lang surjectivity on this centralizer gives the precise centralizing solution
needed for descent of conjugacy.

This does not prove centralizer connectedness or Lang surjectivity. Those are
the geometric inputs in Steinberg, `refs/KGroup/GLS3/Chapter2St2.tex`, 8.5,
10.1 and 12.5. No regular inverse of Frobenius is used.
-/

@[expose] public noncomputable section

namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound

open Theory.AlgebraicGroup

universe u
variable {k : Type u} [Field k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K]

/-- A regular realization of graph followed by the `n`th ordinary Frobenius. -/
def graphFieldMorphism (S : Geometry K) (n : ℕ) : Morphism K K :=
  let F : Morphism K K := {
    toVariety := S.frobenius.toVariety.iterate n
    map_one := by
      rw [Variety.Morphism.iterate_toFun]
      exact iterate_map_one S.frobenius.onPoints n
    map_mul := by
      intro x y
      rw [Variety.Morphism.iterate_toFun]
      exact iterate_map_mul S.frobenius.onPoints n x y }
  F.comp S.diagram.hom

/-- The regular realization has exactly the published fixed-group point map. -/
theorem graphFieldMorphism_onPoints (S : Geometry K) (n : ℕ) :
    (graphFieldMorphism S n).onPoints = graphFieldEnd S n := by
  ext g
  change (S.frobenius.toVariety.iterate n).toFun (S.diagram.toMulEquiv g) = _
  rw [Variety.Morphism.iterate_toFun]
  rfl

/-- Bijectivity concerns points only. -/
theorem graphFieldEnd_bijective (S : Geometry K) (n : ℕ) :
    Function.Bijective (graphFieldEnd S n) :=
  (S.frobenius_bijective.iterate n).comp S.diagram.toMulEquiv.bijective

/-- Positive graph-field powers are Steinberg endomorphisms. -/
theorem graphFieldMorphism_steinberg (S : Geometry K) (n : ℕ) (hn : 0 < n) :
    IsAlgebraicSteinbergEndomorphism (graphFieldMorphism S n) := by
  refine ⟨?_, ?_⟩
  · rw [graphFieldMorphism_onPoints]
    exact (graphFieldEnd_bijective S n).surjective
  · rw [graphFieldMorphism_onPoints]
    exact S.fixed_finite n hn

/-- The literal closed centralizer of a fixed point. Its closedness is the
regular equalizer of left and right multiplication by that point. -/
def fixedCentralizer (S : Geometry K) (n : ℕ)
    (x : graphFieldFixedSubgroup S.diagram.toMulEquiv S.frobenius.onPoints n) :
    ClosedSubgroup K :=
  ClosedSubgroup.ofSubgroup
    (Subgroup.centralizer ({(x : Variety.Point K)} : Set (Variety.Point K))) (by
      have hclosed := Variety.Morphism.isZariskiClosed_equalizer
        (Theory.AlgebraicGroup.leftMulMorphism K (x : Variety.Point K))
        (Theory.AlgebraicGroup.rightMulMorphism K (x : Variety.Point K))
      convert hclosed using 1
      ext g
      change g ∈ Subgroup.centralizer {(x : Variety.Point K)} ↔
        (x : Variety.Point K) * g = g * (x : Variety.Point K)
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact eq_comm)

/-- Membership in the chosen closed subgroup means actual commutation. -/
theorem mem_fixedCentralizer_iff (S : Geometry K) (n : ℕ)
    (x : graphFieldFixedSubgroup S.diagram.toMulEquiv S.frobenius.onPoints n)
    (a : Variety.Point K) :
    a ∈ (fixedCentralizer S n x).toSubgroup ↔ Commute a (x : Variety.Point K) :=
  Subgroup.mem_centralizer_singleton_iff

/-- The graph-field map preserves the centralizer of each fixed point. -/
theorem fixedCentralizer_map (S : Geometry K) (n : ℕ)
    (x : graphFieldFixedSubgroup S.diagram.toMulEquiv S.frobenius.onPoints n)
    (a : Variety.Point (fixedCentralizer S n x).carrierVariety) :
    ((graphFieldMorphism S n).comp (fixedCentralizer S n x).inclusion).onPoints a ∈
      (fixedCentralizer S n x).toSubgroup := by
  change (graphFieldMorphism S n).onPoints
    ((fixedCentralizer S n x).inclusion.onPoints a) ∈
      (fixedCentralizer S n x).toSubgroup
  rw [mem_fixedCentralizer_iff, graphFieldMorphism_onPoints]
  have ha := (mem_fixedCentralizer_iff S n x _).mp
    ((fixedCentralizer S n x).pointEquiv a).property
  change Commute ((fixedCentralizer S n x).inclusion.onPoints a)
    (x : Variety.Point K) at ha
  have hx : graphFieldEnd S n (x : Variety.Point K) = x := x.property
  change graphFieldEnd S n ((fixedCentralizer S n x).inclusion.onPoints a) *
    (x : Variety.Point K) = (x : Variety.Point K) *
      graphFieldEnd S n ((fixedCentralizer S n x).inclusion.onPoints a)
  rw [← hx, ← map_mul, ← map_mul, ha.eq]

/-- Regular restriction of the graph-field map to the centralizer. -/
def centralizerRestriction (S : Geometry K) (n : ℕ)
    (x : graphFieldFixedSubgroup S.diagram.toMulEquiv S.frobenius.onPoints n) :
    Morphism (fixedCentralizer S n x).carrierVariety
      (fixedCentralizer S n x).carrierVariety :=
  Morphism.codRestrictClosedSubgroup
    ((graphFieldMorphism S n).comp (fixedCentralizer S n x).inclusion)
    (fixedCentralizer S n x) (fixedCentralizer_map S n x)

/-- The restriction agrees with the ambient graph-field map after inclusion. -/
theorem centralizerRestriction_inclusion_apply (S : Geometry K) (n : ℕ)
    (x : graphFieldFixedSubgroup S.diagram.toMulEquiv S.frobenius.onPoints n)
    (a : Variety.Point (fixedCentralizer S n x).carrierVariety) :
    (fixedCentralizer S n x).inclusion.onPoints ((centralizerRestriction S n x).onPoints a) =
      graphFieldEnd S n ((fixedCentralizer S n x).inclusion.onPoints a) := by
  calc
    _ = (graphFieldMorphism S n).onPoints
        ((fixedCentralizer S n x).inclusion.onPoints a) :=
      Morphism.codRestrictClosedSubgroup_inclusion_apply
        ((graphFieldMorphism S n).comp (fixedCentralizer S n x).inclusion)
        (fixedCentralizer S n x) (fixedCentralizer_map S n x) a
    _ = _ := congrArg (fun f : Monoid.End (Variety.Point K) =>
      f ((fixedCentralizer S n x).inclusion.onPoints a)) (graphFieldMorphism_onPoints S n)

/-- The inverse on ambient points preserves the centralizer, because the
centralized point is fixed and the ambient map is injective. -/
theorem centralizerRestriction_bijective (S : Geometry K) (n : ℕ)
    (x : graphFieldFixedSubgroup S.diagram.toMulEquiv S.frobenius.onPoints n) :
    Function.Bijective (centralizerRestriction S n x).onPoints := by
  let C := fixedCentralizer S n x
  have hσ := graphFieldEnd_bijective S n
  constructor
  · intro a b hab
    apply C.inclusion_injective
    apply hσ.injective
    rw [← centralizerRestriction_inclusion_apply, ← centralizerRestriction_inclusion_apply]
    exact congrArg C.inclusion.onPoints hab
  · intro a
    obtain ⟨b, hb⟩ := hσ.surjective (C.inclusion.onPoints a)
    have hbC : b ∈ C.toSubgroup := by
      apply (mem_fixedCentralizer_iff S n x b).mpr
      change b * (x : Variety.Point K) = (x : Variety.Point K) * b
      apply hσ.injective
      have hx : graphFieldEnd S n (x : Variety.Point K) = x := x.property
      have ha := (mem_fixedCentralizer_iff S n x _).mp (C.pointEquiv a).property
      change Commute (C.inclusion.onPoints a) (x : Variety.Point K) at ha
      simpa only [map_mul, hb, hx] using ha.eq
    refine ⟨C.pointEquiv.symm ⟨b, hbC⟩, C.inclusion_injective ?_⟩
    rw [centralizerRestriction_inclusion_apply]
    change graphFieldEnd S n b = C.inclusion.onPoints a
    exact hb

/-- The centralizer's fixed points inject into the literal finite fixed group. -/
theorem centralizerRestriction_steinberg (S : Geometry K) (n : ℕ) (hn : 0 < n)
    (x : graphFieldFixedSubgroup S.diagram.toMulEquiv S.frobenius.onPoints n) :
    IsAlgebraicSteinbergEndomorphism (centralizerRestriction S n x) := by
  refine ⟨(centralizerRestriction_bijective S n x).surjective, ?_⟩
  let C := fixedCentralizer S n x
  let := S.fixed_finite n hn
  let f : {a : Variety.Point C.carrierVariety |
      (centralizerRestriction S n x).onPoints a = a} →
      graphFieldFixedSubgroup S.diagram.toMulEquiv S.frobenius.onPoints n :=
    fun a => ⟨C.inclusion.onPoints a, by
      change graphFieldEnd S n (C.inclusion.onPoints a) = C.inclusion.onPoints a
      rw [← centralizerRestriction_inclusion_apply, a.property]⟩
  exact Finite.of_injective f (by
    intro a b h
    apply Subtype.ext
    apply C.inclusion_injective
    exact congrArg (fun z : graphFieldFixedSubgroup S.diagram.toMulEquiv
      S.frobenius.onPoints n => (z : Variety.Point K)) h)

/-- A geometric Lang solution maps to the ambient solution required for
conjugator correction. -/
theorem centralizer_lang_solution (S : Geometry K) (n : ℕ)
    (x : graphFieldFixedSubgroup S.diagram.toMulEquiv S.frobenius.onPoints n)
    (hLang : Function.Surjective (langMorphism (centralizerRestriction S n x)).toFun)
    (a : Variety.Point K) (ha : Commute a (x : Variety.Point K)) :
    ∃ c : Variety.Point K, Commute c (x : Variety.Point K) ∧
      c * (graphFieldEnd S n c)⁻¹ = a := by
  let C := fixedCentralizer S n x
  let aC : Variety.Point C.carrierVariety :=
    C.pointEquiv.symm ⟨a, (mem_fixedCentralizer_iff S n x a).mpr ha⟩
  obtain ⟨c, hc⟩ := hLang aC
  refine ⟨C.inclusion.onPoints c,
    (mem_fixedCentralizer_iff S n x _).mp (C.pointEquiv c).property, ?_⟩
  have h := congrArg C.inclusion.onPoints hc
  simp only [langMorphism_apply, map_mul, map_inv] at h
  change (fixedCentralizer S n x).inclusion.onPoints c *
    ((fixedCentralizer S n x).inclusion.onPoints
      ((centralizerRestriction S n x).onPoints c))⁻¹ = a at h
  rw [centralizerRestriction_inclusion_apply] at h
  exact h

end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound
