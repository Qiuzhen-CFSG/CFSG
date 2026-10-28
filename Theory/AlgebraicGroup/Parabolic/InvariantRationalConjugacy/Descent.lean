module

public import Theory.SpecificGroups.LieType.FiniteParabolicRealization
public import Theory.AlgebraicGroup.Parabolic.Conjugation
public import Theory.AlgebraicGroup.Automorphisms.Lang.Basic

/-!
# Rational conjugacy of invariant parabolics

The source argument first places a parabolic above the specified Borel.
Uniqueness of that conjugate makes it invariant. Lang's equation on its
connected stabilizer corrects the conjugator to a fixed point. Generation of
the full fixed group by the fixed torus and fixed unipotent root groups then
absorbs the torus factor, leaving a conjugator in the literal prime-to-p
residual. Restriction intertwines the resulting conjugation with the actual
point embedding.

The results below isolate this descent argument. Algebraic standard-position
geometry, Lang surjectivity and fixed root-group generation are explicit
hypotheses; this module does not assert their existence. The geometric inputs
belong to `InvariantLeviGeometry`, and the root-generation input to the finite
Bruhat construction. The general connected Lang theorem remains a separate
upstream obligation.

Source: GLS3, Theorem 2.1.5(a), Proposition 2.6.8 and its continuation;
Theorem 1.13.2(b,d). Our `Q.conjugate g` means `g Q g⁻¹`.
-/

namespace Theory.AlgebraicGroup.InvariantRationalConjugacy

open FiniteParabolicRealization

variable {k : Type*} [Field k] {K : Variety k} [AlgebraicGroup K]

/-- Equivariance of conjugation under an endomorphism preserving a subgroup. -/
public theorem map_conjugate_of_invariant
    (σ : AlgebraicEndomorphism K) (Q : ClosedSubgroup K)
    (hQ : Q.toSubgroup.map σ.onPoints = Q.toSubgroup) (g : Variety.Point K) :
    (Q.conjugate g).toSubgroup.map σ.onPoints =
      (Q.conjugate (σ.onPoints g)).toSubgroup := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    apply (Q.mem_conjugate_iff _ _).mpr
    have hm : σ.onPoints (g⁻¹ * y * g) ∈ Q.toSubgroup.map σ.onPoints :=
      ⟨_, (Q.mem_conjugate_iff _ _).mp hy, rfl⟩
    rw [hQ] at hm
    simpa only [map_mul, map_inv] using hm
  · intro hx
    have hm := (Q.mem_conjugate_iff _ _).mp hx
    rw [← hQ] at hm
    obtain ⟨y, hy, heq⟩ := hm
    refine ⟨g * y * g⁻¹, ?_, ?_⟩
    · apply (Q.mem_conjugate_iff _ _).mpr
      simp only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one]
      exact hy
    · rw [map_mul, map_mul, map_inv, heq]
      group

/-- The unique conjugate above an invariant Borel is itself invariant.
Uniqueness is the geometric assertion of GLS3 1.13.2(d). -/
public theorem standard_conjugate_invariant
    (σ : AlgebraicEndomorphism K) (B Q : ClosedSubgroup K)
    (hB : B.toSubgroup.map σ.onPoints = B.toSubgroup)
    (hQ : Q.toSubgroup.map σ.onPoints = Q.toSubgroup)
    (hunique : ∀ g h : Variety.Point K,
      B ≤ Q.conjugate g → B ≤ Q.conjugate h → Q.conjugate g = Q.conjugate h)
    (g : Variety.Point K) (hg : B ≤ Q.conjugate g) :
    (Q.conjugate g).toSubgroup.map σ.onPoints = (Q.conjugate g).toSubgroup := by
  have hs : B ≤ Q.conjugate (σ.onPoints g) := by
    have hm := Subgroup.map_mono (f := σ.onPoints)
      (show B.toSubgroup ≤ (Q.conjugate g).toSubgroup from hg)
    rw [hB, map_conjugate_of_invariant σ Q hQ g] at hm
    exact hm
  rw [map_conjugate_of_invariant σ Q hQ, hunique _ _ hs hg]

private theorem mem_normalizer_of_conjugate_eq
    (Q : ClosedSubgroup K) (g : Variety.Point K) (hg : Q.conjugate g = Q) :
    g ∈ Q.normalizer.toSubgroup := by
  apply Subgroup.mem_normalizer_iff.mpr
  intro x
  have h := Q.mem_conjugate_iff g (g * x * g⁻¹)
  rw [hg] at h
  change (g * x * g⁻¹ ∈ Q.toSubgroup ↔ g⁻¹ * (g * x * g⁻¹) * g ∈ Q.toSubgroup) at h
  simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using h.symm

/-- Lang on the connected normalizer adjusts an ambient conjugator to a fixed
point. In the parabolic application self-normalization identifies that
normalizer with `Q`, so the Lang equation is solved inside `Q` itself. -/
public theorem exists_fixed_conjugator_of_lang
    (σ : AlgebraicEndomorphism K) (Q : ClosedSubgroup K)
    (hQ : Q.toSubgroup.map σ.onPoints = Q.toSubgroup)
    (hself : Q.normalizer = Q)
    (hLang : ∀ a ∈ Q.toSubgroup,
      ∃ c ∈ Q.toSubgroup, c * σ.onPoints c⁻¹ = a)
    (g : Variety.Point K)
    (hg : (Q.conjugate g).toSubgroup.map σ.onPoints =
      (Q.conjugate g).toSubgroup) :
    ∃ x : fixedPoints σ, Q.conjugate x.val = Q.conjugate g := by
  have hconj : Q.conjugate (σ.onPoints g) = Q.conjugate g := by
    apply SetLike.coe_injective
    exact congrArg (fun S : Subgroup (Variety.Point K) => (S : Set (Variety.Point K)))
      ((map_conjugate_of_invariant σ Q hQ g).symm.trans hg)
  have hdefect : Q.conjugate (g⁻¹ * σ.onPoints g) = Q := by
    rw [← Q.conjugate_conjugate, hconj, Q.conjugate_conjugate]
    simp only [inv_mul_cancel, Q.conjugate_one]
  have ha : g⁻¹ * σ.onPoints g ∈ Q.toSubgroup := by
    rw [← hself]
    exact mem_normalizer_of_conjugate_eq Q _ hdefect
  obtain ⟨c, hc, heq⟩ := hLang _ ha
  have hfix : σ.onPoints (g * c) = g * c := by
    have heq' := congrArg (fun z => g * z * σ.onPoints c) heq
    simp only [map_inv] at heq'
    simpa only [map_mul, mul_assoc, inv_mul_cancel, mul_one, mul_inv_cancel_left]
      using heq'.symm
  refine ⟨⟨g * c, hfix⟩, ?_⟩
  rw [← Q.conjugate_conjugate]
  rw [Q.conjugate_eq_self_of_mem_normalizer c (Subgroup.le_normalizer hc)]

/-- The genuine regular restriction to an invariant closed subgroup. -/
@[expose] public def invariantRestriction
    (σ : AlgebraicEndomorphism K) (Q : ClosedSubgroup K)
    (hQ : Q.toSubgroup.map σ.onPoints = Q.toSubgroup) :
    AlgebraicEndomorphism Q.carrierVariety :=
  (σ.comp Q.inclusion).codRestrictClosedSubgroup Q (fun x => by
    change σ.onPoints (Q.inclusion.onPoints x) ∈ Q.toSubgroup
    rw [← hQ]
    exact ⟨_, (Q.pointEquiv x).property, rfl⟩)

public theorem invariantRestriction_inclusion
    (σ : AlgebraicEndomorphism K) (Q : ClosedSubgroup K)
    (hQ : Q.toSubgroup.map σ.onPoints = Q.toSubgroup)
    (x : Variety.Point Q.carrierVariety) :
    Q.inclusion.onPoints ((invariantRestriction σ Q hQ).onPoints x) =
      σ.onPoints (Q.inclusion.onPoints x) :=
  Morphism.codRestrictClosedSubgroup_inclusion_apply _ _ _ _

/-- Exact invariance gives surjectivity of the restriction, and its fixed
points inject into the ambient fixed group. -/
public theorem invariantRestriction_steinberg
    (σ : AlgebraicEndomorphism K) (hσ : IsAlgebraicSteinbergEndomorphism σ)
    (Q : ClosedSubgroup K) (hQ : Q.toSubgroup.map σ.onPoints = Q.toSubgroup) :
    IsAlgebraicSteinbergEndomorphism (invariantRestriction σ Q hQ) := by
  constructor
  · intro y
    have hy : Q.inclusion.onPoints y ∈ Q.toSubgroup.map σ.onPoints := by
      rw [hQ]
      exact (Q.pointEquiv y).property
    obtain ⟨x, hx, heq⟩ := hy
    refine ⟨Q.pointEquiv.symm ⟨x, hx⟩, Q.inclusion_injective ?_⟩
    rw [invariantRestriction_inclusion]
    exact heq
  · let f : {x : Variety.Point Q.carrierVariety |
        (invariantRestriction σ Q hQ).onPoints x = x} →
        {x : Variety.Point K | σ.onPoints x = x} := fun x =>
      ⟨Q.inclusion.onPoints x.val, by
        change σ.onPoints (Q.inclusion.onPoints x.val) = Q.inclusion.onPoints x.val
        rw [← invariantRestriction_inclusion σ Q hQ, x.property]⟩
    let := hσ.2
    apply Finite.of_injective f
    intro x y h
    apply Subtype.ext
    apply Q.inclusion_injective
    exact congrArg (fun z : {a : Variety.Point K | σ.onPoints a = a} => z.val) h

/-- A Lang solution on the carrier variety gives the literal ambient equation
used in the conjugator correction. -/
public theorem ambient_lang_of_restriction
    (σ : AlgebraicEndomorphism K) (Q : ClosedSubgroup K)
    (hQ : Q.toSubgroup.map σ.onPoints = Q.toSubgroup)
    (hLang : Function.Surjective (langMorphism (invariantRestriction σ Q hQ)).toFun) :
    ∀ a ∈ Q.toSubgroup, ∃ c ∈ Q.toSubgroup, c * σ.onPoints c⁻¹ = a := by
  intro a ha
  obtain ⟨c, hc⟩ := hLang (Q.pointEquiv.symm ⟨a, ha⟩)
  refine ⟨Q.inclusion.onPoints c, (Q.pointEquiv c).property, ?_⟩
  have heq := congrArg Q.inclusion.onPoints hc
  have hval : Q.inclusion.onPoints (Q.pointEquiv.symm ⟨a, ha⟩) = a := by
    change (Q.pointEquiv (Q.pointEquiv.symm ⟨a, ha⟩)).val = a
    rw [Q.pointEquiv.apply_symm_apply]
  rw [hval] at heq
  simpa only [langMorphism_apply, map_mul, invariantRestriction_inclusion, map_inv]
    using heq

/-- Fixed unipotent root groups lie in the residual. Thus root generation of
the full fixed group implies the residual-times-fixed-torus factorization.
This does not assume that factorization as an input. -/
public theorem fixed_torus_mul_residual_of_unipotent_generation
    [IsAlgClosed k] (σ : AlgebraicEndomorphism K) (p : ℕ)
    [Fact p.Prime] [CharP k p] (T : ClosedSubgroup K)
    {ι : Type*} (Y : ι → ClosedSubgroup K)
    (hY : ∀ i, IsUnipotentAlgebraicGroup (Y i).carrierVariety)
    (hgen : T.toSubgroup.comap (fixedPoints σ).subtype ⊔
      (⨆ i, (Y i).toSubgroup.comap (fixedPoints σ).subtype) = ⊤)
    (x : fixedPoints σ) :
    ∃ t : fixedPoints σ, t.val ∈ T.toSubgroup ∧
      ∃ g : definingGroup σ p, x.val = t.val * pointEmbedding σ p g := by
  have htop : T.toSubgroup.comap (fixedPoints σ).subtype ⊔ definingGroup σ p = ⊤ := by
    apply top_unique
    rw [← hgen]
    exact sup_le_sup_left (iSup_le fun i => fixed_unipotent_le_definingGroup σ p (Y i) (hY i)) _
  have hx : x ∈ T.toSubgroup.comap (fixedPoints σ).subtype ⊔ definingGroup σ p := by
    rw [htop]
    trivial
  obtain ⟨t, ht, g, hg, heq⟩ := Subgroup.mem_sup_of_normal_right.mp hx
  exact ⟨t, ht, ⟨g, hg⟩, (congrArg Subtype.val heq).symm⟩

/-- Conjugation commutes with restriction along the actual point embedding. -/
public theorem restrict_conjugate
    (σ : AlgebraicEndomorphism K) (p : ℕ) (Q : ClosedSubgroup K)
    (g : definingGroup σ p) :
    restrict σ p (Q.conjugate (pointEmbedding σ p g)).toSubgroup =
      (restrict σ p Q.toSubgroup).map (MulAut.conj g).toMonoidHom := by
  ext x
  change pointEmbedding σ p x ∈ Q.conjugate (pointEmbedding σ p g) ↔ _
  rw [Q.mem_conjugate_iff]
  constructor
  · intro hx
    refine ⟨g⁻¹ * x * g, ?_, ?_⟩
    · change pointEmbedding σ p (g⁻¹ * x * g) ∈ Q.toSubgroup
      simpa only [map_mul, map_inv] using hx
    · simp [MulAut.conj_apply, mul_assoc]
  · rintro ⟨y, hy, rfl⟩
    change pointEmbedding σ p y ∈ Q.toSubgroup at hy
    change (pointEmbedding σ p g)⁻¹ *
      pointEmbedding σ p (g * y * g⁻¹) * pointEmbedding σ p g ∈ Q.toSubgroup
    simpa only [map_mul, map_inv, mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one]
      using hy

/-- Remove the fixed-torus factor from a rational conjugator. The torus is
contained in the target standard parabolic and therefore normalizes it. -/
public theorem exists_residual_conjugator_of_fixed
    (σ : AlgebraicEndomorphism K) (p : ℕ) (T Q : ClosedSubgroup K)
    (x : fixedPoints σ) (hT : T ≤ Q.conjugate x.val)
    (hfactor : ∃ t : fixedPoints σ, t.val ∈ T.toSubgroup ∧
      ∃ g : definingGroup σ p, x.val = t.val * pointEmbedding σ p g) :
    ∃ g : definingGroup σ p,
      Q.conjugate (pointEmbedding σ p g) = Q.conjugate x.val := by
  obtain ⟨t, ht, g, heq⟩ := hfactor
  refine ⟨g, ?_⟩
  have htP : t.val⁻¹ ∈ (Q.conjugate x.val).normalizer.toSubgroup :=
    Subgroup.le_normalizer ((Q.conjugate x.val).toSubgroup.inv_mem (hT ht))
  have h := (Q.conjugate x.val).conjugate_eq_self_of_mem_normalizer t.val⁻¹ htP
  rw [Q.conjugate_conjugate] at h
  have hprod : t.val⁻¹ * x.val = pointEmbedding σ p g := by
    rw [heq, inv_mul_cancel_left]
  rwa [hprod] at h

/-- Conditional rational standard-position descent. The Lang and fixed-root
inputs remain visible until their independent source producers are assembled.
The algebraic classification and uniqueness hypotheses are exactly the earlier
source geometry allowed in this descent theorem. -/
public theorem exists_residual_standard_conjugator
    [IsAlgClosed k] (σ : AlgebraicEndomorphism K) (p : ℕ)
    [Fact p.Prime] [CharP k p] (B T Q : ClosedSubgroup K)
    (hTB : T ≤ B)
    (hB : B.toSubgroup.map σ.onPoints = B.toSubgroup)
    (hQ : Q.toSubgroup.map σ.onPoints = Q.toSubgroup)
    (hself : Q.normalizer = Q)
    (hstandard : ∃ g : Variety.Point K, B ≤ Q.conjugate g)
    (hunique : ∀ g h : Variety.Point K,
      B ≤ Q.conjugate g → B ≤ Q.conjugate h → Q.conjugate g = Q.conjugate h)
    (hLang : Function.Surjective (langMorphism (invariantRestriction σ Q hQ)).toFun)
    {ι : Type*} (Y : ι → ClosedSubgroup K)
    (hY : ∀ i, IsUnipotentAlgebraicGroup (Y i).carrierVariety)
    (hgen : T.toSubgroup.comap (fixedPoints σ).subtype ⊔
      (⨆ i, (Y i).toSubgroup.comap (fixedPoints σ).subtype) = ⊤) :
    ∃ g : definingGroup σ p, B ≤ Q.conjugate (pointEmbedding σ p g) := by
  obtain ⟨a, ha⟩ := hstandard
  have hstable := standard_conjugate_invariant σ B Q hB hQ hunique a ha
  obtain ⟨x, hx⟩ := exists_fixed_conjugator_of_lang σ Q hQ hself
    (ambient_lang_of_restriction σ Q hQ hLang) a hstable
  have hBx : B ≤ Q.conjugate x.val := hx.symm ▸ ha
  obtain ⟨g, hg⟩ := exists_residual_conjugator_of_fixed σ p T Q x (fun _ ht => hBx (hTB ht))
    (fixed_torus_mul_residual_of_unipotent_generation σ p T Y hY hgen x)
  exact ⟨g, hg.symm ▸ hBx⟩

/-- The actual finite-parabolic consumer of standard-position descent.
The conjugating element is inverted because `IsFiniteParabolic` puts the
conjugate of the Borel inside the original parabolic. -/
public theorem isFiniteParabolic_of_standard_conjugator
    (σ : AlgebraicEndomorphism K) (p : ℕ) (B Q : ClosedSubgroup K)
    (h : ∃ g : definingGroup σ p, B ≤ Q.conjugate (pointEmbedding σ p g)) :
    IsFiniteParabolic σ p B (restrict σ p Q.toSubgroup) := by
  obtain ⟨g, hg⟩ := h
  refine ⟨g⁻¹, ?_⟩
  rintro x ⟨b, hb, rfl⟩
  change pointEmbedding σ p (g⁻¹ * b * (g⁻¹)⁻¹) ∈ Q.toSubgroup
  simp only [map_mul, map_inv, inv_inv]
  exact (Q.mem_conjugate_iff _ _).mp (hg hb)

end Theory.AlgebraicGroup.InvariantRationalConjugacy
