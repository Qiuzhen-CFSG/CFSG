module

public import Theory.AlgebraicGroup.Parabolic.InvariantRationalConjugacy.Descent
public import Theory.AlgebraicGroup.Automorphisms.Lang.SolvableSurjectivity
public import Theory.AlgebraicGroup.Automorphisms.Lang.invariant_borel_factorization_closed_image
public import Theory.AlgebraicGroup.Automorphisms.SteinbergInvariantMaximalTorus
public import Theory.AlgebraicGroup.Borel.GeometricConjugacy
public import Theory.AlgebraicGroup.Borel.Existence

/-!
# Reduction of connected Lang surjectivity to Borel geometry

Steinberg's shorter proof (10.8) uses two geometric parts of 7.3: closedness
and dominance of the image of `(x,b) ↦ x b σ(x)⁻¹` for an invariant Borel.
This module keeps those two inputs explicit. Their combination first produces
an invariant Borel, by twisting a conjugator between `B` and `σ(B)` as in 7.2.
The already proved solvable Lang theorem then absorbs the Borel factor.

The ordinary Lang range need not be a subgroup. Density alone is therefore
used only after the Borel factorization image has been proved closed.

Source: Steinberg, *Endomorphisms of Linear Algebraic Groups*, 7.2–7.3 and
10.8 (`refs/KGroup/GLS3/Chapter2St2.tex`); GLS3, Theorem 2.1.1.
-/

universe u

namespace Theory.AlgebraicGroup.InvariantRationalConjugacy.ConnectedLang

open Topology

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {K : Variety k} [AlgebraicGroup K]

/-- The closed-image part of Steinberg 7.3, on the actual Borel factorization
image. No quotient-space topology or Lang solution is included in this input. -/
@[expose] public def BorelLangClosedImages (K : Variety k) [AlgebraicGroup K] : Prop :=
  ∀ (τ : AlgebraicEndomorphism K) (B : ClosedSubgroup K),
    IsBorelSubgroup B → B.toSubgroup.map τ.onPoints = B.toSubgroup →
      IsClosed (borelLangFactorizationImage τ B)

/-- The dominance part of Steinberg 7.3. The endomorphism is surjective, but
its fixed-point group is not assumed finite: the invariant-Borel construction
applies this assertion to an inner twist before its fixed points are known. -/
@[expose] public def BorelLangDominantImages (K : Variety k) [AlgebraicGroup K] : Prop :=
  ∀ (τ : AlgebraicEndomorphism K), Function.Surjective τ.onPoints →
    ∀ (B : ClosedSubgroup K), IsBorelSubgroup B →
      B.toSubgroup.map τ.onPoints = B.toSubgroup →
        Dense (borelLangFactorizationImage τ B)

omit [IsAlgClosed k] in
private theorem map_conjugate_of_image
    (σ : AlgebraicEndomorphism K) (B C : ClosedSubgroup K)
    (hmap : B.toSubgroup.map σ.onPoints = C.toSubgroup) (g : Variety.Point K) :
    (B.conjugate g).toSubgroup.map σ.onPoints =
      (C.conjugate (σ.onPoints g)).toSubgroup := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    apply (C.mem_conjugate_iff _ _).mpr
    have hm : σ.onPoints (g⁻¹ * y * g) ∈ B.toSubgroup.map σ.onPoints :=
      ⟨_, (B.mem_conjugate_iff _ _).mp hy, rfl⟩
    rw [hmap] at hm
    simpa only [map_mul, map_inv] using hm
  · intro hx
    have hm := (C.mem_conjugate_iff _ _).mp hx
    rw [← hmap] at hm
    obtain ⟨y, hy, heq⟩ := hm
    refine ⟨g * y * g⁻¹, ?_, ?_⟩
    · apply (B.mem_conjugate_iff _ _).mpr
      simp only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one]
      exact hy
    · rw [map_mul, map_mul, map_inv, heq]
      group

/-- Steinberg 7.2 from the two independent geometric parts of 7.3.
The inner twist used here need not have finite fixed points. -/
public theorem exists_invariant_borel_of_borel_geometry
    (σ : AlgebraicEndomorphism K) (hσ : Function.Surjective σ.onPoints)
    (hK : Variety.IsConnected K)
    (hclosed : BorelLangClosedImages K) (hdense : BorelLangDominantImages K) :
    ∃ B : ClosedSubgroup K, IsBorelSubgroup B ∧
      B.toSubgroup.map σ.onPoints = B.toSubgroup := by
  obtain ⟨B, hB⟩ := exists_borelSubgroup K
  let C := (σ.comp B.inclusion).imageClosedSubgroup
  have hC : IsBorelSubgroup C :=
    isogeny_image_isBorel σ ⟨hσ, surjectiveEndomorphism_kernel_finite σ hσ⟩ hK B hB
  have hmap : B.toSubgroup.map σ.onPoints = C.toSubgroup := by
    ext a
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact ⟨B.pointEquiv.symm ⟨b, hb⟩, rfl⟩
    · rintro ⟨b, rfl⟩
      exact ⟨B.inclusion.onPoints b, (B.pointEquiv b).property, rfl⟩
  obtain ⟨z, hz⟩ := BorelGeometricConjugacy.conjugacy hB hC
  rw [hz] at hmap
  let τ := innerTwist z⁻¹ σ
  have hτ (a : Variety.Point K) : τ.onPoints a = z⁻¹ * σ.onPoints a * z := by
    change z⁻¹ * σ.onPoints a * (z⁻¹)⁻¹ = _
    rw [inv_inv]
  have hτsurj : Function.Surjective τ.onPoints := by
    intro a
    obtain ⟨b, hb⟩ := hσ (z * a * z⁻¹)
    refine ⟨b, ?_⟩
    rw [hτ, hb]
    group
  have hτB : B.toSubgroup.map τ.onPoints = B.toSubgroup := by
    ext a
    constructor
    · rintro ⟨b, hb, rfl⟩
      rw [hτ]
      apply (B.mem_conjugate_iff z _).mp
      change σ.onPoints b ∈ (B.conjugate z).toSubgroup
      rw [← hmap]
      exact ⟨b, hb, rfl⟩
    · intro ha
      have hm : z * a * z⁻¹ ∈ (B.conjugate z).toSubgroup := by
        apply (B.mem_conjugate_iff z _).mpr
        simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using ha
      rw [← hmap] at hm
      obtain ⟨b, hb, heq⟩ := hm
      refine ⟨b, hb, ?_⟩
      rw [hτ, heq]
      group
  have hfull : borelLangFactorizationImage τ B = Set.univ := by
    rw [← (hclosed τ B hB hτB).closure_eq]
    exact (hdense τ hτsurj B hB hτB).closure_eq
  have hzmem : z ∈ borelLangFactorizationImage τ B := by
    rw [hfull]
    trivial
  obtain ⟨x, b, hb, heq⟩ := hzmem
  have hσxz : σ.onPoints x * z = x * b := by
    rw [hτ, map_inv] at heq
    have heq' := congrArg (fun a => a * z⁻¹ * σ.onPoints x * z) heq
    simpa only [mul_assoc, inv_mul_cancel_left, mul_inv_cancel_left,
      mul_inv_cancel, inv_mul_cancel, mul_one, one_mul] using heq'
  refine ⟨B.conjugate x, hB.conjugate x, ?_⟩
  rw [map_conjugate_of_image σ B (B.conjugate z) hmap x,
    B.conjugate_conjugate, hσxz, ← B.conjugate_conjugate]
  rw [B.conjugate_eq_self_of_mem_normalizer b (Subgroup.le_normalizer hb)]

omit [IsAlgClosed k] in
private theorem borel_carrier_connected (B : ClosedSubgroup K) (hB : IsBorelSubgroup B) :
    Variety.IsConnected B.carrierVariety := by
  let : ConnectedSpace {x : Variety.Point K // x ∈ (B : Set (Variety.Point K))} :=
    Subtype.connectedSpace hB.connected
  let : ConnectedSpace (Variety.Point B.carrierVariety) :=
    (Variety.closedSubvarietyPointHomeomorph B.isZariskiClosed).connectedSpace_iff.mpr
      inferInstance
  exact connectedSpace_iff_univ.mp inferInstance

/-- For an invariant Borel, solvable Lang absorbs the Borel factor. Finite
ambient fixed points suffice; no Lang equation on the ambient group is assumed. -/
public theorem borel_factorization_image_eq_lang_range
    (σ : AlgebraicEndomorphism K) (hσ : IsAlgebraicSteinbergEndomorphism σ)
    (B : ClosedSubgroup K) (hB : IsBorelSubgroup B)
    (hBσ : B.toSubgroup.map σ.onPoints = B.toSubgroup) :
    borelLangFactorizationImage σ B = Set.range (langMorphism σ).toFun := by
  have hLangB := langMorphism_surjective_of_solvable (invariantRestriction σ B hBσ)
    (invariantRestriction_steinberg σ hσ B hBσ) (borel_carrier_connected B hB) hB.solvable
  have hLangAmbient := ambient_lang_of_restriction σ B hBσ hLangB
  ext a
  constructor
  · rintro ⟨x, b, hb, rfl⟩
    obtain ⟨c, hc, hsol⟩ := hLangAmbient b hb
    refine ⟨x * c, ?_⟩
    rw [langMorphism_apply, mul_inv_rev, map_mul, ← hsol]
    group
  · rintro ⟨x, rfl⟩
    exact ⟨x, 1, B.toSubgroup.one_mem, by simp [langMorphism_apply]⟩

/-- Closedness of the invariant-Borel factorization image upgrades the proved
finite-fiber density theorem to Lang surjectivity. -/
public theorem lang_surjective_of_invariant_borel_closedImage
    (σ : AlgebraicEndomorphism K) (hσ : IsAlgebraicSteinbergEndomorphism σ)
    (hK : Variety.IsConnected K) (B : ClosedSubgroup K) (hB : IsBorelSubgroup B)
    (hBσ : B.toSubgroup.map σ.onPoints = B.toSubgroup)
    (hclosed : IsClosed (borelLangFactorizationImage σ B)) :
    Function.Surjective (langMorphism σ).toFun := by
  rw [borel_factorization_image_eq_lang_range σ hσ B hB hBσ] at hclosed
  have hfull : Set.range (langMorphism σ).toFun = Set.univ := by
    rw [← hclosed.closure_eq]
    exact (langMorphism_denseRange σ hσ hK).closure_eq
  exact Set.range_eq_univ.mp hfull

/-- The shorter connected Lang proof, with only the two geometric assertions
of Steinberg 7.3 left explicit. The Borel, its invariance and the Lang solutions
inside it are all constructed in this proof. -/
public theorem lang_surjective_of_borel_geometry
    (σ : AlgebraicEndomorphism K) (hσ : IsAlgebraicSteinbergEndomorphism σ)
    (hK : Variety.IsConnected K)
    (hclosed : BorelLangClosedImages K) (hdense : BorelLangDominantImages K) :
    Function.Surjective (langMorphism σ).toFun := by
  obtain ⟨B, hB, hBσ⟩ := exists_invariant_borel_of_borel_geometry σ hσ.1 hK hclosed hdense
  exact lang_surjective_of_invariant_borel_closedImage σ hσ hK B hB hBσ
    (hclosed σ B hB hBσ)

end Theory.AlgebraicGroup.InvariantRationalConjugacy.ConnectedLang
