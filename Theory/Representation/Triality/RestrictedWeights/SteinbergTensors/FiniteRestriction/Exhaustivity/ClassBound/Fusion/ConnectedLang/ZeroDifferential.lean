module

public import Theory.AlgebraicGroup.Automorphisms.Lang.FiniteFiberDominance
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Theory.AlgebraicGroup.Bor1.PointDerivationCotangent
public import Mathlib.RingTheory.Ideal.IdempotentFG

/-!
# Lang surjectivity when the endomorphism differential vanishes

A vanishing identity tangent space makes the identity-point cotangent ideal
idempotent. Finite generation isolates the identity by a principal open set;
translations and Noetherianity then make the algebraic group finite. Applying
this to the closed fixed subgroup proves finiteness of fixed points for any
endomorphism whose identity differential is zero.

Every inner twist of such an endomorphism again has zero differential. For a
surjective endomorphism of a connected group, the two Lang images therefore
contain nonempty open sets. Irreducibility makes a translate of these sets
intersect, and the twisted-conjugacy identity gives every required Lang
solution. This is the special argument of Steinberg, *Endomorphisms of Linear
Algebraic Groups*, 10.7--10.8 (`refs/KGroup/GLS3/Chapter2St2.tex`).

The proof uses no smoothness or tangent-dimension theorem and does not assume
that the endomorphism has a regular inverse. The triality consumer separately
has to establish the zero differential for its actual Frobenius map.
-/

universe u
namespace Theory.AlgebraicGroup
open Bor1 Topology
variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
/-- An algebraic group with zero identity tangent space has finitely many
points. The proof works over any field. -/
public theorem finite_points_of_identity_derivations_eq_zero
    (G : Variety k) [AlgebraicGroup G]
    (h : ∀ D : IdentityPointDerivation G, D = 0) :
    Finite (Variety.Point G) := by
  let m := (G.pointPrime 1).asIdeal
  let : Subsingleton (IdentityPointDerivation G) :=
    ⟨fun D E => (h D).trans (h E).symm⟩
  let e := identityPointDerivationEquivCotangentDual G
  have hdual : Subsingleton (m.Cotangent →ₗ[k] k) :=
    e.toEquiv.subsingleton_congr.mp inferInstance
  have hcot : Subsingleton m.Cotangent :=
    (Module.subsingleton_dual_iff k).mp hdual
  let : Algebra.FiniteType k (Variety.PolynomialFunction G) :=
    polynomialFunction_finiteType G
  let : IsNoetherianRing (Variety.PolynomialFunction G) :=
    Algebra.FiniteType.isNoetherianRing k (Variety.PolynomialFunction G)
  obtain ⟨f, hf, hmf⟩ := (Ideal.isIdempotentElem_iff_of_fg m
    m.fg_of_isNoetherianRing).mp (m.cotangent_subsingleton_iff.mp hcot)
  have hf1 : f 1 = 0 := by
    have hfmem : f ∈ m := by
      rw [hmf]
      exact Submodule.mem_span_singleton_self f
    exact hfmem
  have hsingleton : G.pointPrime ⁻¹' PrimeSpectrum.basicOpen (1 - f) =
      ({1} : Set (Variety.Point G)) := by
    ext x
    constructor
    · intro hx
      have hxne : (1 - f) x ≠ 0 := hx
      have hfx : f x = 0 := by
        have hfi : IsIdempotentElem (f x) := by
          have hi := congrArg (fun q : Variety.PolynomialFunction G => q x) hf.eq
          exact hi
        rcases IsIdempotentElem.iff_eq_zero_or_one.mp hfi with hzero | hone
        · exact hzero
        · exfalso
          apply hxne
          change 1 - f x = 0
          simp [hone]
      have hmle : m ≤ (G.pointPrime x).asIdeal := by
        rw [hmf]
        exact (Submodule.span_singleton_le_iff_mem _ _).mpr hfx
      have heq : m = (G.pointPrime x).asIdeal :=
        (G.pointPrime_isMaximal 1).eq_of_le (G.pointPrime x).isPrime.ne_top hmle
      have hxone : x = 1 := G.pointPrime_injective (PrimeSpectrum.ext heq.symm)
      exact Set.mem_singleton_iff.mpr hxone
    · rintro rfl
      change (1 - f) 1 ≠ 0
      change 1 - f 1 ≠ 0
      simp [hf1]
  have hopen : IsOpen ({1} : Set (Variety.Point G)) := by
    rw [← hsingleton]
    exact PrimeSpectrum.isOpen_basicOpen.preimage G.continuous_pointPrime
  have hdiscrete : IsDiscrete (Set.univ : Set (Variety.Point G)) := by
    rw [isDiscrete_iff_forall_mem_exists_isOpen]
    intro x _
    refine ⟨{x}, ?_, by simp⟩
    have heq : (leftMulMorphism G x⁻¹).toFun ⁻¹' {1} = {x} := by
      ext y
      simp [leftMulMorphism_apply, inv_mul_eq_one, eq_comm]
    rw [← heq]
    exact hopen.preimage (leftMulMorphism G x⁻¹).continuous
  have hfinite : (Set.univ : Set (Variety.Point G)).Finite :=
    (TopologicalSpace.NoetherianSpace.isCompact Set.univ).finite hdiscrete
  exact Set.finite_univ_iff.mp hfinite

/-- The closed fixed subgroup has zero tangent space when the endomorphism
has zero identity differential, so its point set is finite. -/
public theorem finite_fixed_of_differential_eq_zero
    {G : Variety k} [AlgebraicGroup G] (σ : Morphism G G)
    (hd : identityTangentMorphismLinearMap σ = 0) :
    Finite {x : Variety.Point G | σ.onPoints x = x} := by
  let H : ClosedSubgroup G := ClosedSubgroup.ofSubgroup
    (σ.onPoints.eqLocus (MonoidHom.id _))
    (Variety.Morphism.isZariskiClosed_equalizer σ.toVariety (Variety.Morphism.id G))
  have hcomp : σ.comp H.inclusion = H.inclusion := by
    apply Morphism.ext
    funext x
    exact (H.pointEquiv x).property
  have hincl : identityTangentMorphismLinearMap H.inclusion = 0 := by
    rw [← hcomp, identityTangentMorphismLinearMap_comp, hd, LinearMap.zero_comp]
  have hfinite : Finite (Variety.Point H.carrierVariety) :=
    finite_points_of_identity_derivations_eq_zero H.carrierVariety (by
      intro D
      apply identityTangentMorphismLinearMap_inclusion_injective H
      rw [hincl]
      rfl)
  exact (Equiv.finite_iff H.pointEquiv).mp hfinite

private def langConjugation {G : Variety k} [AlgebraicGroup G]
    (a : Variety.Point G) : Morphism G G :=
  { toVariety := conjugationByMorphism G a
    map_one := by simp [conjugationByMorphism_apply]
    map_mul := by
      intro x y
      simp only [conjugationByMorphism_apply]
      group }

/-- Lang surjectivity for a surjective endomorphism of a connected algebraic
group with vanishing identity differential. -/
public theorem langMorphism_surjective_of_differential_eq_zero
    {G : Variety k} [AlgebraicGroup G] (σ : Morphism G G)
    (hsurj : Function.Surjective σ.onPoints)
    (hG : Variety.IsConnected G)
    (hd : identityTangentMorphismLinearMap σ = 0) :
    Function.Surjective (langMorphism σ).toFun := by
  let : PreirreducibleSpace (Variety.Point G) :=
    ⟨(connectedAlgebraicGroup_irreducible G hG).2⟩
  have hσ : IsAlgebraicSteinbergEndomorphism σ :=
    ⟨hsurj, finite_fixed_of_differential_eq_zero σ hd⟩
  obtain ⟨U, hUopen, hUne, hUrange⟩ :=
    langMorphism_exists_nonempty_open_subset_range σ hσ hG
  intro a
  let τ := (langConjugation a).comp σ
  have hτsurj : Function.Surjective τ.onPoints := by
    intro y
    obtain ⟨x, hx⟩ := hsurj (a⁻¹ * y * a)
    refine ⟨x, ?_⟩
    change a * σ.onPoints x * a⁻¹ = y
    rw [hx]
    group
  have hτd : identityTangentMorphismLinearMap τ = 0 := by
    dsimp only [τ]
    rw [identityTangentMorphismLinearMap_comp, hd, LinearMap.comp_zero]
  have hτ : IsAlgebraicSteinbergEndomorphism τ :=
    ⟨hτsurj, finite_fixed_of_differential_eq_zero τ hτd⟩
  obtain ⟨V, hVopen, hVne, hVrange⟩ :=
    langMorphism_exists_nonempty_open_subset_range τ hτ hG
  let W := (rightMulMorphism G a⁻¹).toFun ⁻¹' V
  have hWopen : IsOpen W := hVopen.preimage (rightMulMorphism G a⁻¹).continuous
  have hWne : W.Nonempty := by
    obtain ⟨v, hv⟩ := hVne
    refine ⟨v * a, ?_⟩
    change (v * a) * a⁻¹ ∈ V
    simpa using hv
  obtain ⟨y, hyU, hyW⟩ := nonempty_preirreducible_inter hUopen hWopen hUne hWne
  obtain ⟨b, hb⟩ := hUrange hyU
  obtain ⟨c, hc⟩ := hVrange hyW
  have hc' : c * (a * σ.onPoints c⁻¹ * a⁻¹) = y * a⁻¹ := hc
  have ha : c⁻¹ * y * σ.onPoints c = a := by
    have heq := congrArg (fun z => c⁻¹ * z * a * σ.onPoints c) hc'
    simpa [map_inv, mul_assoc] using heq.symm
  refine ⟨c⁻¹ * b, ?_⟩
  calc
    (langMorphism σ).toFun (c⁻¹ * b) =
        c⁻¹ * (langMorphism σ).toFun b * σ.onPoints c := by
          simp [langMorphism_apply, map_mul, mul_assoc]
    _ = c⁻¹ * y * σ.onPoints c := by rw [hb]
    _ = a := ha

end Theory.AlgebraicGroup
