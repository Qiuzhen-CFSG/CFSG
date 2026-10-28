module

public import Theory.AlgebraicGroup.RootSubgroups.Tangent
public import Theory.AlgebraicGroup.Unipotent.Radical

/-!
# Borel action on a regular simple-root tangent sum

This module records the source-faithful tangent-action contract used in the
proof of Bor1, Lemma 14.23.  For a realized positive root system and chosen
root parametrizations, the unipotent-radical assertion says that conjugating
the sum of the simple-root tangents changes it only by a linear combination of
non-simple positive-root tangents.  If a Borel point factors as `t * u`, torus
conjugation then replaces each simple-root coefficient by the inverse root
character at `t`; these coefficients are all nonzero.  Thus a general Borel
point is controlled modulo the same higher-root span, but not in general
modulo the original unweighted sum.

The proof separates these two effects.  The root tangent weight-vector theorem
computes the torus action and proves invariance of the higher-root span.  The
factorization theorem then transports the unipotent error through the torus.
Finally, linear independence of the positive-root tangent family shows that
every simple root remains in the support modulo all the other positive roots.
The exposed definitions below are the intended stable boundary for consumers
carrying out the Weyl-support argument in Lemma 14.23.

Source: Bor1, Chapter 4, lines 1439--1447, using the commutator tangent
calculation in Chapter 1, lines 1122--1140.  That calculation applies to two
points of the unipotent radical; the torus contribution is handled separately
here.
-/

open scoped BigOperators

universe u

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

@[expose]
public noncomputable def rootTangentVector
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T)
    (x : (alpha : D.Root) ->
      OneParameterParametrization (D.rootSubgroup alpha).carrierVariety)
    (alpha : D.Root) : IdentityPointDerivation K :=
  oneParameterTangent (D.rootSubgroup alpha) (x alpha)

@[expose]
public noncomputable def simpleRootTangentSum
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) [Finite D.Root]
    (x : (alpha : D.Root) ->
      OneParameterParametrization (D.rootSubgroup alpha).carrierVariety) :
    IdentityPointDerivation K :=
  ∑ alpha ∈ D.simple.toFinite.toFinset, rootTangentVector D x alpha

@[expose]
public noncomputable def weightedSimpleRootTangentSum
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) [Finite D.Root]
    (x : (alpha : D.Root) ->
      OneParameterParametrization (D.rootSubgroup alpha).carrierVariety)
    (c : D.Root -> k) : IdentityPointDerivation K :=
  ∑ alpha ∈ D.simple.toFinite.toFinset,
    c alpha • rootTangentVector D x alpha

@[expose]
public noncomputable def nonSimplePositiveRootTangentSpan
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T)
    (x : (alpha : D.Root) ->
      OneParameterParametrization (D.rootSubgroup alpha).carrierVariety) :
    Submodule k (IdentityPointDerivation K) :=
  Submodule.span k
    (rootTangentVector D x '' (D.positive \ D.simple))

omit [IsAlgClosed k] in
private theorem RootGroupData.IsRealization.simple_subset_positive
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    {D : RootGroupData K T} (hD : D.IsRealization) :
    D.simple ⊆ D.positive := by
  rcases hD with ⟨_, _, _, _, _, _, _, _, _, _, _, hsimple, _⟩
  intro alpha halpha
  exact (hsimple alpha).mp halpha |>.1

public theorem rootTangentVector_torus_conjugation
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (hD : D.IsRealization)
    (x : (alpha : D.Root) ->
      OneParameterParametrization (D.rootSubgroup alpha).carrierVariety)
    (t : Variety.Point T.carrierVariety) (alpha : D.Root) :
    ((identityTangentRepresentation K).action (T.includePoint t)).1
        (rootTangentVector D x alpha) =
      ((D.rootWeight alpha)⁻¹).pointCharacter t •
        rootTangentVector D x alpha := by
  exact (oneParameterTangent_isWeightVector T (D.rootSubgroup alpha) (x alpha)
    (hD.2.2.1 alpha).2).2 t

omit [IsAlgClosed k] in
public theorem rootTangentCoefficient_ne_zero
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (t : Variety.Point T.carrierVariety)
    (alpha : D.Root) :
    ((D.rootWeight alpha)⁻¹).pointCharacter t ≠ 0 := by
  exact Units.ne_zero (dPointEquiv 1 (((D.rootWeight alpha)⁻¹).onPoints t) 0)

public theorem simpleRootTangentSum_torus_conjugation
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) [Finite D.Root] (hD : D.IsRealization)
    (x : (alpha : D.Root) ->
      OneParameterParametrization (D.rootSubgroup alpha).carrierVariety)
    (t : Variety.Point T.carrierVariety) :
    ((identityTangentRepresentation K).action (T.includePoint t)).1
        (simpleRootTangentSum D x) =
      weightedSimpleRootTangentSum D x
        (fun alpha => ((D.rootWeight alpha)⁻¹).pointCharacter t) := by
  classical
  simp only [simpleRootTangentSum, weightedSimpleRootTangentSum, map_sum]
  apply Finset.sum_congr rfl
  intro alpha halpha
  rw [rootTangentVector_torus_conjugation D hD x t alpha]

public theorem nonSimplePositiveRootTangentSpan_torus_invariant
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (hD : D.IsRealization)
    (x : (alpha : D.Root) ->
      OneParameterParametrization (D.rootSubgroup alpha).carrierVariety)
    (t : Variety.Point T.carrierVariety) :
    ∀ z, z ∈ nonSimplePositiveRootTangentSpan D x ->
      ((identityTangentRepresentation K).action (T.includePoint t)).1 z ∈
        nonSimplePositiveRootTangentSpan D x := by
  intro z hz
  refine Submodule.span_induction (p := fun y _ =>
    ((identityTangentRepresentation K).action (T.includePoint t)).1 y ∈
      nonSimplePositiveRootTangentSpan D x) ?_ ?_ ?_ ?_ hz
  · rintro _ ⟨alpha, halpha, rfl⟩
    rw [rootTangentVector_torus_conjugation D hD x t alpha]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨alpha, halpha, rfl⟩)
  · simpa only [map_zero] using
      (nonSimplePositiveRootTangentSpan D x).zero_mem
  · intro y z _ _ hy hz
    rw [map_add]
    exact Submodule.add_mem _ hy hz
  · intro c y _ hy
    rw [map_smul]
    exact Submodule.smul_mem _ c hy

@[expose]
public def HasDerivedUnipotentSimpleRootTangentControl
    {K : Variety k} [AlgebraicGroup K]
    (U T : ClosedSubgroup K) (D : RootGroupData K T) [Finite D.Root]
    (x : (alpha : D.Root) ->
      OneParameterParametrization (D.rootSubgroup alpha).carrierVariety) : Prop :=
  ∀ u : Variety.Point K, u ∈ U ->
    ((identityTangentRepresentation K).action u).1 (simpleRootTangentSum D x) -
        simpleRootTangentSum D x ∈
      nonSimplePositiveRootTangentSpan D x

public structure BorelTangentDerivedUnipotentControl
    {K : Variety k} [AlgebraicGroup K]
    (B U T : ClosedSubgroup K) (D : RootGroupData K T) [Finite D.Root]
    (x : (alpha : D.Root) ->
      OneParameterParametrization (D.rootSubgroup alpha).carrierVariety) : Prop where
  unipotentRadical : IsUnipotentRadicalOf B U
  unipotent : HasDerivedUnipotentSimpleRootTangentControl U T D x
  borel : ∀ b : Variety.Point K, b ∈ B ->
    ∃ c : D.Root -> k,
      (∀ alpha, alpha ∈ D.simple -> c alpha ≠ 0) ∧
      ((identityTangentRepresentation K).action b).1 (simpleRootTangentSum D x) -
          weightedSimpleRootTangentSum D x c ∈
        nonSimplePositiveRootTangentSpan D x

public theorem BorelTangentDerivedUnipotentControl.of_factorization
    {K : Variety k} [AlgebraicGroup K]
    (B U T : ClosedSubgroup K) (D : RootGroupData K T) [Finite D.Root]
    (x : (alpha : D.Root) ->
      OneParameterParametrization (D.rootSubgroup alpha).carrierVariety)
    (hD : D.IsRealization) (hU : IsUnipotentRadicalOf B U)
    (hfactor : ∀ b : Variety.Point K, b ∈ B ->
      ∃ t u : Variety.Point K, t ∈ T ∧ u ∈ U ∧ b = t * u)
    (hcontrol : HasDerivedUnipotentSimpleRootTangentControl U T D x) :
    BorelTangentDerivedUnipotentControl B U T D x := by
  refine ⟨hU, hcontrol, ?_⟩
  intro b hb
  obtain ⟨t, u, ht, hu, rfl⟩ := hfactor b hb
  let tT : Variety.Point T.carrierVariety := T.pointEquiv.symm ⟨t, ht⟩
  have htT : T.includePoint tT = t := by
    change (T.pointEquiv tT).val = t
    simp [tT]
  let c : D.Root -> k :=
    fun alpha => ((D.rootWeight alpha)⁻¹).pointCharacter tT
  refine ⟨c, fun alpha _ => rootTangentCoefficient_ne_zero D tT alpha, ?_⟩
  have hmap := nonSimplePositiveRootTangentSpan_torus_invariant D hD x tT
    (((identityTangentRepresentation K).action u).1 (simpleRootTangentSum D x) -
      simpleRootTangentSum D x) (hcontrol u hu)
  change ((identityTangentRepresentation K).action (t * u)).1
      (simpleRootTangentSum D x) - weightedSimpleRootTangentSum D x c ∈ _
  rw [map_mul]
  change ((identityTangentRepresentation K).action t).1
      (((identityTangentRepresentation K).action u).1
        (simpleRootTangentSum D x)) - weightedSimpleRootTangentSum D x c ∈ _
  rw [← htT,
    ← simpleRootTangentSum_torus_conjugation D hD x tT]
  simpa only [map_sub] using hmap

public theorem simpleRootTangent_mem_support_of_control
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) [Finite D.Root] (hD : D.IsRealization)
    (x : (alpha : D.Root) ->
      OneParameterParametrization (D.rootSubgroup alpha).carrierVariety)
    (hlinear : LinearIndepOn k (rootTangentVector D x) D.positive)
    (c : D.Root -> k) (hc : ∀ alpha, alpha ∈ D.simple -> c alpha ≠ 0)
    (v : IdentityPointDerivation K)
    (hv : v - weightedSimpleRootTangentSum D x c ∈
      nonSimplePositiveRootTangentSpan D x)
    (alpha : D.Root) (halpha : alpha ∈ D.simple) :
    v ∉ Submodule.span k
      (rootTangentVector D x '' (D.positive \ {alpha})) := by
  classical
  let P : Submodule k (IdentityPointDerivation K) := Submodule.span k
    (rootTangentVector D x '' (D.positive \ {alpha}))
  have halphaPositive : alpha ∈ D.positive :=
    hD.simple_subset_positive halpha
  have herrorP : v - weightedSimpleRootTangentSum D x c ∈ P := by
    apply (Submodule.span_mono ?_) hv
    rintro _ ⟨beta, ⟨hbetaPositive, hbetaNotSimple⟩, rfl⟩
    refine ⟨beta, ⟨hbetaPositive, ?_⟩, rfl⟩
    simp only [Set.mem_singleton_iff]
    intro hbeta
    subst beta
    exact hbetaNotSimple halpha
  intro hvP
  have hsumP : weightedSimpleRootTangentSum D x c ∈ P := by
    have := P.sub_mem hvP herrorP
    simpa [sub_sub_cancel] using this
  let simple : Finset D.Root := D.simple.toFinite.toFinset
  have halphaSimple : alpha ∈ simple := by simp [simple, halpha]
  have hrestP : ∑ beta ∈ simple.erase alpha,
      c beta • rootTangentVector D x beta ∈ P := by
    apply Submodule.sum_mem
    intro beta hbeta
    apply Submodule.smul_mem
    apply Submodule.subset_span
    refine ⟨beta, ⟨hD.simple_subset_positive ?_, ?_⟩, rfl⟩
    · simpa [simple] using Finset.mem_of_mem_erase hbeta
    · simpa only [Set.mem_singleton_iff] using Finset.ne_of_mem_erase hbeta
  have hcoefficientP : c alpha • rootTangentVector D x alpha ∈ P := by
    have hcoefficientEq :
        weightedSimpleRootTangentSum D x c -
            (∑ beta ∈ simple.erase alpha,
              c beta • rootTangentVector D x beta) =
          c alpha • rootTangentVector D x alpha := by
      rw [weightedSimpleRootTangentSum]
      have hsum := Finset.sum_erase_add simple
        (fun beta => c beta • rootTangentVector D x beta) halphaSimple
      rw [← hsum]
      simp [simple]
    rw [← hcoefficientEq]
    exact P.sub_mem hsumP hrestP
  exact hc alpha halpha
    (hlinear.eq_zero_of_smul_mem_span halphaPositive (c alpha) hcoefficientP)

public theorem BorelTangentDerivedUnipotentControl.simpleRoot_mem_support
    {K : Variety k} [AlgebraicGroup K]
    {B U T : ClosedSubgroup K} {D : RootGroupData K T} [Finite D.Root]
    {x : (alpha : D.Root) ->
      OneParameterParametrization (D.rootSubgroup alpha).carrierVariety}
    (control : BorelTangentDerivedUnipotentControl B U T D x)
    (hD : D.IsRealization)
    (hlinear : LinearIndepOn k (rootTangentVector D x) D.positive)
    (b : Variety.Point K) (hb : b ∈ B)
    (alpha : D.Root) (halpha : alpha ∈ D.simple) :
    ((identityTangentRepresentation K).action b).1
        (simpleRootTangentSum D x) ∉
      Submodule.span k
        (rootTangentVector D x '' (D.positive \ {alpha})) := by
  obtain ⟨c, hc, hv⟩ := control.borel b hb
  exact simpleRootTangent_mem_support_of_control D hD x hlinear c hc _ hv
    alpha halpha

end Theory.AlgebraicGroup
