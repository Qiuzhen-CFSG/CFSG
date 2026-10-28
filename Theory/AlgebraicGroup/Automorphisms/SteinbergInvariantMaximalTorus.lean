module

public import Theory.AlgebraicGroup.Automorphisms.Steinberg
public import Theory.AlgebraicGroup.Bor1.Differential
public import Theory.AlgebraicGroup.Borel.Defs
public import Theory.AlgebraicGroup.Borel.IsogenyImage
public import Theory.AlgebraicGroup.ClosedSubgroup.Conjugation
public import Theory.AlgebraicGroup.Tori.Maximal

/-!
The invariant-maximal-torus reduction in Steinberg [St2, 10.5], as presented
in `refs/KGroup/GLS3/Chapter2St2.tex`.  Given a fixed Borel subgroup, the
solvable Lang map and conjugacy of maximal tori in that Borel produce an inner
twist of a surjective endomorphism that preserves a chosen maximal torus.
The accompanying differential lemmas identify the twist with conjugation by
an algebraic inner automorphism, so nilpotence of the identity tangent map is
unchanged.  The Lang and Borel-torus conjugacy inputs are explicit interfaces;
their geometric proofs belong to the corresponding solvable and Borel layers.
-/

universe u

namespace Theory.AlgebraicGroup

open Bor1

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- The algebraic-group morphism given by conjugation by a point. -/
@[expose]
public def innerConjugationMorphism
    {K : Variety k} [AlgebraicGroup K]
    (g : Variety.Point K) : AlgebraicGroup.Morphism K K :=
  { toVariety := AlgebraicGroup.conjugationByMorphism K g
    map_one := by simp [AlgebraicGroup.conjugationByMorphism_apply]
    map_mul := by
      intro x y
      simp only [AlgebraicGroup.conjugationByMorphism_apply]
      group }

/-- The inner twist `i_g σ` of an algebraic-group endomorphism. -/
@[expose]
public def innerTwist
    {K : Variety k} [AlgebraicGroup K]
    (g : Variety.Point K) (σ : AlgebraicGroup.Morphism K K) :
    AlgebraicGroup.Morphism K K :=
  (innerConjugationMorphism g).comp σ

omit [IsAlgClosed k] in
/-- Pointwise formula for `innerConjugationMorphism`. -/
public lemma innerConjugationMorphism_onPoints
    {K : Variety k} [AlgebraicGroup K]
    (g x : Variety.Point K) :
    (innerConjugationMorphism g).onPoints x = g * x * g⁻¹ := by
  exact AlgebraicGroup.conjugationByMorphism_apply K g x

omit [IsAlgClosed k] in
/-- Conjugation by `g⁻¹` is the inverse algebraic morphism to conjugation by `g`. -/
public lemma innerConjugationMorphism_comp_inv
    {K : Variety k} [AlgebraicGroup K]
    (g : Variety.Point K) :
    (innerConjugationMorphism g⁻¹).comp
        (innerConjugationMorphism g) = AlgebraicGroup.Morphism.id K := by
  apply AlgebraicGroup.Morphism.ext
  funext x
  change (g⁻¹) * (g * x * g⁻¹) * (g⁻¹)⁻¹ = x
  group

omit [IsAlgClosed k] in
/-- Conjugation by `g` is the inverse algebraic morphism to conjugation by `g⁻¹`. -/
public lemma innerConjugationMorphism_inv_comp
    {K : Variety k} [AlgebraicGroup K]
    (g : Variety.Point K) :
    (innerConjugationMorphism g).comp
        (innerConjugationMorphism g⁻¹) = AlgebraicGroup.Morphism.id K := by
  apply AlgebraicGroup.Morphism.ext
  funext x
  change g * (g⁻¹ * x * (g⁻¹)⁻¹) * g⁻¹ = x
  group

omit [IsAlgClosed k] in
/-- The Lang-form twist is algebraically conjugate to the original endomorphism. -/
public lemma innerTwist_eq_conjugate
    {K : Variety k} [AlgebraicGroup K]
    (σ : AlgebraicGroup.Morphism K K)
    (c : Variety.Point K) :
    innerTwist (c * σ.onPoints c⁻¹) σ =
      (innerConjugationMorphism c).comp
        (σ.comp (innerConjugationMorphism c⁻¹)) := by
  apply AlgebraicGroup.Morphism.ext
  funext x
  change (c * σ.onPoints c⁻¹) * σ.onPoints x *
      (c * σ.onPoints c⁻¹)⁻¹ =
    c * σ.onPoints (c⁻¹ * x * (c⁻¹)⁻¹) * c⁻¹
  simp only [map_mul, map_inv]
  group

omit [IsAlgClosed k] in
private lemma nilpotent_conjugate_iff
    {M : Type u} [AddCommGroup M] [Module k M]
    (A Ainv D : Module.End k M)
    (hAA : A.comp Ainv = LinearMap.id)
    (hAinvA : Ainv.comp A = LinearMap.id) :
    IsNilpotent (A * D * Ainv) ↔ IsNilpotent D := by
  have hpow (X Y : Module.End k M)
      (hYX : Y.comp X = LinearMap.id)
      (hXY : X.comp Y = LinearMap.id) (n : ℕ) :
      (X * D * Y) ^ n = X * (D ^ n) * Y := by
    induction n with
    | zero =>
        simp only [pow_zero, mul_one]
        exact hXY.symm
    | succ n ih =>
        rw [pow_succ, ih]
        apply LinearMap.ext
        intro v
        change X ((D ^ n) (Y (X (D (Y v))))) =
          X ((D ^ (n + 1)) (Y v))
        have hv : Y (X (D (Y v))) = D (Y v) := by
          change (Y.comp X) (D (Y v)) = D (Y v)
          rw [hYX]
          rfl
        rw [hv]
        rw [pow_succ]
        rfl
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have h := hpow A Ainv hAinvA hAA n
    calc
      D ^ n = Ainv * (A * (D ^ n) * Ainv) * A := by
        apply LinearMap.ext
        intro v
        change (D ^ n) v = Ainv (A ((D ^ n) (Ainv (A v))))
        have hv : Ainv (A v) = v := by
          exact LinearMap.congr_fun hAinvA v
        rw [hv]
        have hv' : Ainv (A ((D ^ n) v)) = (D ^ n) v := by
          exact LinearMap.congr_fun hAinvA ((D ^ n) v)
        rw [hv']
      _ = Ainv * ((A * D * Ainv) ^ n) * A := by rw [h]
      _ = 0 := by rw [hn]; simp
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    rw [hpow A Ainv hAinvA hAA n, hn]
    simp

/-- Nilpotence of the identity differential is invariant under a Lang-form
inner twist. -/
public theorem identityTangentMorphismLinearMap_innerTwist_nilpotent_iff
    {K : Variety k} [AlgebraicGroup K]
    (σ : AlgebraicGroup.Morphism K K) (c : Variety.Point K) :
    IsNilpotent
        (identityTangentMorphismLinearMap
          (innerTwist (c * σ.onPoints c⁻¹) σ)) ↔
      IsNilpotent (identityTangentMorphismLinearMap σ) := by
  rw [innerTwist_eq_conjugate]
  rw [AlgebraicGroup.Morphism.comp_assoc,
    identityTangentMorphismLinearMap_comp,
    identityTangentMorphismLinearMap_comp]
  apply nilpotent_conjugate_iff
  · rw [← identityTangentMorphismLinearMap_comp,
      innerConjugationMorphism_inv_comp, identityTangentMorphismLinearMap_id]
  · rw [← identityTangentMorphismLinearMap_comp,
      innerConjugationMorphism_comp_inv, identityTangentMorphismLinearMap_id]

/-- The pointwise Lang-surjectivity interface on a fixed Borel subgroup. -/
@[expose]
public def BorelLangSurjective
    {K : Variety k} [AlgebraicGroup K]
    (σ : AlgebraicGroup.Morphism K K) (B : ClosedSubgroup K) : Prop :=
  ∀ z : B.toSubgroup, ∃ c : B.toSubgroup,
    (c : Variety.Point K) * σ.onPoints (c : Variety.Point K)⁻¹ =
      (z : Variety.Point K)

/-- The pointwise conjugacy interface for maximal tori contained in `B`. -/
@[expose]
public def MaximalToriConjugateIn
    {K : Variety k} [AlgebraicGroup K]
    (B : ClosedSubgroup K) : Prop :=
  ∀ T₁ T₂ : ClosedSubgroup K,
    IsMaximalTorus T₁ → IsMaximalTorus T₂ →
    T₁ ≤ B → T₂ ≤ B →
    ∃ b : B.toSubgroup,
      (fun x : Variety.Point K =>
        (b : Variety.Point K) * x * (b : Variety.Point K)⁻¹) ''
          (T₁ : Set (Variety.Point K)) = (T₂ : Set (Variety.Point K))

/-- Construct an inner twist preserving a maximal torus in a fixed Borel.

The image of `T` under the surjective endomorphism is a maximal torus by the
isogeny image theorem.  Conjugating that image back to `T` inside `B` gives
`b`; solvable Lang writes `b = c σ(c)⁻¹`, and the differential lemma above
transfers nilpotence back to `σ`. -/
public theorem exists_innerTwist_preserving_maximalTorus
    {K : Variety k} [AlgebraicGroup K]
    (σ : AlgebraicGroup.Morphism K K)
    (hσ : IsAlgebraicSteinbergEndomorphism σ)
    (B : ClosedSubgroup K) (_hB : IsBorelSubgroup B)
    (hBσ : σ.onPoints '' (B : Set (Variety.Point K)) =
      (B : Set (Variety.Point K)))
    (T : ClosedSubgroup K) (hT : IsMaximalTorus T) (hTB : T ≤ B)
    (hLang : BorelLangSurjective σ B)
    (hConj : MaximalToriConjugateIn B) :
    ∃ b c : B.toSubgroup,
      (innerTwist (b : Variety.Point K) σ).onPoints ''
          (T : Set (Variety.Point K)) = (T : Set (Variety.Point K)) ∧
      (b : Variety.Point K) =
        (c : Variety.Point K) * σ.onPoints (c : Variety.Point K)⁻¹ ∧
      (IsNilpotent
          (identityTangentMorphismLinearMap
            (innerTwist (b : Variety.Point K) σ)) ↔
        IsNilpotent (identityTangentMorphismLinearMap σ)) := by
  let hσisog : IsIsogeny σ :=
    ⟨hσ.1, surjectiveEndomorphism_kernel_finite σ hσ.1⟩
  let Tσ : ClosedSubgroup K :=
    (σ.comp T.inclusion).imageClosedSubgroup
  have hTσ : IsMaximalTorus Tσ := by
    exact isogeny_image_isMaximalTorus σ hσisog T hT
  have hTσset : (Tσ : Set (Variety.Point K)) =
      Set.range (σ.comp T.inclusion).onPoints := by
    exact (σ.comp T.inclusion).imageClosedSubgroup_carrier.trans
      (σ.comp T.inclusion).image_carrier
  have hTσB : Tσ ≤ B := by
    intro x hx
    change x ∈ (Tσ : Set (Variety.Point K)) at hx
    rw [hTσset] at hx
    rcases hx with ⟨tx, rfl⟩
    have htx : T.inclusion.onPoints tx ∈ B.toSubgroup :=
      hTB (T.pointEquiv tx).property
    change σ.onPoints (T.inclusion.onPoints tx) ∈
      (B : Set (Variety.Point K))
    rw [← hBσ]
    exact ⟨T.inclusion.onPoints tx, htx, rfl⟩
  obtain ⟨b, hb⟩ := hConj Tσ T hTσ hT hTσB hTB
  obtain ⟨c, hc⟩ := hLang b
  refine ⟨b, c, ?_, hc.symm, ?_⟩
  · apply Set.Subset.antisymm
    · rintro y ⟨x, hx, rfl⟩
      change (b : Variety.Point K) * σ.onPoints x *
        (b : Variety.Point K)⁻¹ ∈ (T : Set (Variety.Point K))
      rw [← hb]
      refine ⟨σ.onPoints x, ?_, rfl⟩
      rw [hTσset]
      exact ⟨T.pointEquiv.symm ⟨x, hx⟩, rfl⟩
    · intro y hy
      rw [← hb] at hy
      rcases hy with ⟨x, hx, rfl⟩
      rw [hTσset] at hx
      rcases hx with ⟨tx, rfl⟩
      refine ⟨T.inclusion.onPoints tx, (T.pointEquiv tx).property, ?_⟩
      rfl
  · rw [← hc]
    exact identityTangentMorphismLinearMap_innerTwist_nilpotent_iff σ
      (c : Variety.Point K)

end Theory.AlgebraicGroup
