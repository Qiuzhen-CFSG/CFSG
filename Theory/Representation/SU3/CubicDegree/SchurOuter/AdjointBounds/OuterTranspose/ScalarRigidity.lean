module

public import Theory.Representation.SU3.CubicDegree.SchurOuter.AdjointBounds.OuterTranspose.GeometryInterface
public import Theory.Representation.TensorInvolutionIntertwiners

/-!
# Removing the scalar ambiguity of the actual adjoint actor

The literal binary normalizer equation survives passage to the Schur field
and scalar extension. Given an intertwiner to an adjoint model, an operator
implementing the same pairs of group representatives differs from the actual
actor by a scalar, by Schur's lemma. If both operators square to one, that
scalar has square one and hence equals one in characteristic two.

The comparison uses the supplied representation equivalence and the actual
normalizer homomorphism. It does not require an automorphism to lift from the
action image to the covering group. The geometric construction of a model
operator remains separate in `GeometryInterface`.

Source: Guralnick--Malle, Classification of 2F-modules II, Proposition 4.11,
internal pp.31--32.
-/

public section

open Representation Representation.BinaryOffender Representation.FrobeniusTensor
open Representation.SL3.BinaryDefiningFactors
namespace Representation.SU3.CubicDegree.SchurOuter.AdjointBounds.OuterTranspose

variable {K W : Type*} [Field K] [AddCommGroup W] [Module K W]

private theorem adjointMatrix_injective :
    Function.Injective (adjointMatrix (K := K)) := by
  intro X Y h
  apply Subtype.ext
  exact LinearMap.toMatrix'.injective (by
    simpa only [adjointMatrix_apply] using h)

/-- Transpose coordinates force the literal operator to square to one. -/
theorem IsTransposeOperator.square_one {T : Module.End K W}
    (hT : IsTransposeOperator T) : T * T = 1 := by
  obtain ⟨e, he⟩ := hT
  ext v
  apply e.injective
  apply adjointMatrix_injective
  change adjointMatrix (e (T (T v))) = adjointMatrix (e v)
  rw [he, he, Matrix.transpose_transpose]

private theorem involutions_eq_of_common_targets
    [CharP K 2] [IsAlgClosed K] [FiniteDimensional K W]
    {G : Type*} [Group G] (ρ : Representation K G W) [ρ.IsIrreducible]
    (T : Module.End K W) (S : W ≃ₗ[K] W)
    (h : ∀ g, ∃ k, T * ρ g = ρ k * T ∧
      S.toLinearMap * ρ g = ρ k * S.toLinearMap)
    (hT2 : T * T = 1) (hS2 : S.toLinearMap * S.toLinearMap = 1) :
    T = S.toLinearMap := by
  let : Nontrivial W := Subrepresentation.irreducible_module_nontrivial ρ
  have hcomm (g : G) :
      (S.symm.toLinearMap * T) * ρ g = ρ g * (S.symm.toLinearMap * T) := by
    obtain ⟨k, hT, hS⟩ := h g
    have hinv : S.symm.toLinearMap * ρ k = ρ g * S.symm.toLinearMap := by
      ext v
      apply S.injective
      have he := congrArg (fun A : Module.End K W => A (S.symm v)) hS
      simpa only [Module.End.mul_apply, LinearEquiv.coe_coe,
        LinearEquiv.apply_symm_apply] using he.symm
    rw [mul_assoc, hT, ← mul_assoc, hinv, mul_assoc]
  obtain ⟨c, hc⟩ := TensorInvolutionIntertwiners.scalar_of_commutes ρ
    (S.symm.toLinearMap * T) hcomm
  have hTS : T = c • S.toLinearMap := by
    ext v
    have he := congrArg (fun A : Module.End K W => S (A v)) hc
    simpa only [Module.End.mul_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply, LinearMap.smul_apply,
      Module.End.one_apply, map_smul] using he
  have hc2 : c * c = 1 := by
    have he : (c * c) • (1 : Module.End K W) = (1 : K) • (1 : Module.End K W) := by
      simpa only [hTS, smul_mul_assoc, mul_smul_comm, smul_smul, hS2, one_smul] using hT2
    exact (smul_left_injective K (one_ne_zero : (1 : Module.End K W) ≠ 0)) he
  have hc1 : c = 1 := CharTwo.sq_injective (by simpa only [pow_two, one_mul] using hc2)
  simpa only [hc1, one_smul] using hTS

private theorem map_eq_of_common_targets
    [CharP K 2] [IsAlgClosed K] [FiniteDimensional K W]
    {G U : Type*} [Group G] [AddCommGroup U] [Module K U]
    (ρ : Representation K G W) (τ : Representation K G U) [ρ.IsIrreducible]
    (e : ρ.Equiv τ) (T : Module.End K W) (S : U ≃ₗ[K] U)
    (h : ∀ g, ∃ k, T * ρ g = ρ k * T ∧
      S.toLinearMap * τ g = τ k * S.toLinearMap)
    (hT2 : T * T = 1) (hS2 : S.toLinearMap * S.toLinearMap = 1) :
    ∀ v, e (T v) = S (e v) := by
  let E := e.toLinearEquiv
  have hE (g : G) (v : W) :
      E (ρ g v) = τ g (E v) :=
    congrArg (fun f : W →ₗ[K] U =>
      f v) (e.isIntertwining' g)
  let S' := E.trans (S.trans E.symm)
  have hS' (g h : G)
      (hh : S.toLinearMap * τ g = τ h * S.toLinearMap) :
      S'.toLinearMap * ρ g = ρ h * S'.toLinearMap := by
    apply LinearMap.ext
    intro v
    apply e.toLinearEquiv.injective
    change E (E.symm (S (E (ρ g v)))) =
      E (ρ h (E.symm (S (E v))))
    rw [E.apply_symm_apply, hE, hE, E.apply_symm_apply]
    exact congrArg (fun f : Module.End K U =>
      f (E v)) hh
  have hS'2 : S'.toLinearMap * S'.toLinearMap = 1 := by
    apply LinearMap.ext
    intro v
    apply e.toLinearEquiv.injective
    have heq := congrArg (fun f : Module.End K U =>
      f (E v)) hS2
    simpa only [S', E, Module.End.mul_apply, LinearEquiv.coe_coe, LinearEquiv.trans_apply,
      LinearEquiv.apply_symm_apply, Module.End.one_apply] using heq
  have heq := involutions_eq_of_common_targets ρ T S' (fun g => by
    obtain ⟨k, hT, hS⟩ := h g
    exact ⟨k, hT, hS' g k hS⟩) hT2 hS'2
  intro v
  have hv := congrArg (fun f : Module.End K W => e (f v)) heq
  change E (T v) = S (E v)
  change E (T v) = E (E.symm (S (E v))) at hv
  exact hv.trans (E.apply_symm_apply _)

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (σ : Representation (ZMod 2) G V) [σ.IsIrreducible]
  (A : Subgroup (linearNormalizer σ))
  (hl : ∀ t ∈ A, SchurNormalizer.IsSchurLinear σ t)

/-- The normalizer equation holds on the actual scalar-extended module,
for every pair of representatives related by the image automorphism. -/
theorem absoluteActor_intertwines (a : A) {g h : G}
    (hh : actionHom σ h = (actionImage σ).normalizerMonoidHom a.val (actionHom σ g)) :
    absoluteActorRepresentation σ A hl a * absoluteRep σ g =
      absoluteRep σ h * absoluteActorRepresentation σ A hl a := by
  have hu : σ.asGroupHom h = a.val.val * σ.asGroupHom g * a.val.val⁻¹ :=
    congrArg Subtype.val hh
  have hb : a.val.val.val * σ g = σ h * a.val.val.val := by
    have hv := congrArg Units.val hu
    change σ h = a.val.val.val * σ g * (↑a.val.val⁻¹ : Module.End (ZMod 2) V) at hv
    rw [hv, mul_assoc, Units.inv_mul, mul_one]
  have hs : schurActorRepresentation σ A hl a * σ.endFieldRep g =
      σ.endFieldRep h * schurActorRepresentation σ A hl a := by
    ext v
    apply σ.asModuleEquiv.injective
    exact congrArg (fun f : Module.End (ZMod 2) V => f (σ.asModuleEquiv v)) hb
  simpa only [absoluteActorRepresentation, absoluteRep, extendScalars_apply,
    LinearMap.baseChange_mul] using
    congrArg (fun f : Module.End (SchurField σ) σ.asModule =>
      f.baseChange (Closure σ)) hs


variable {F : Type*} [Field F] (J : BenderSuzuki.MatrixGroups.HermitianForm 3 F)
  (σ : Representation (ZMod 2) J.specialSubgroup V) [σ.IsIrreducible]
  (A : Subgroup (linearNormalizer σ))
  (hl : ∀ t ∈ A, SchurNormalizer.IsSchurLinear σ t)

/-- The actual actor agrees exactly with an involutory model intertwiner;
the possible Schur scalar is proved to be one. -/
theorem absoluteActor_eq_graph_intertwiner
    (ι : F →+* Closure σ) (e : (absoluteRep σ).Equiv (adjoint J ι))
    (a : A) (ha : a ^ 2 = 1)
    (S : AdjointSpace (Closure σ) ≃ₗ[Closure σ] AdjointSpace (Closure σ))
    (hS2 : S.toLinearMap * S.toLinearMap = 1)
    (hS : ∀ g h : J.specialSubgroup,
      actionHom σ h = (actionImage σ).normalizerMonoidHom a.val (actionHom σ g) →
      S.toLinearMap * adjoint J ι g = adjoint J ι h * S.toLinearMap) :
    ∀ v, e (absoluteActorRepresentation σ A hl a v) = S (e v) := by
  have hT2 : absoluteActorRepresentation σ A hl a * absoluteActorRepresentation σ A hl a = 1 := by
    simpa only [pow_two, map_mul, map_one] using
      congrArg (absoluteActorRepresentation σ A hl) ha
  refine map_eq_of_common_targets (K := Closure σ) (W := AbsoluteSpace σ)
    (U := AdjointSpace (Closure σ)) (G := J.specialSubgroup) (absoluteRep σ) (adjoint J ι) e
    (absoluteActorRepresentation σ A hl a) S ?_ hT2 hS2
  have hp : Function.Surjective (actionHom σ) := σ.asGroupHom.rangeRestrict_surjective
  intro g
  exact (hp ((actionImage σ).normalizerMonoidHom a.val (actionHom σ g))).imp
    (fun h hh => ⟨absoluteActor_intertwines σ A hl a hh, hS g h hh⟩)

/-- Transfer geometric transpose coordinates to the specified actual actor. -/
theorem isTransposeOperator_of_adjointGraphIntertwiner
    (ι : F →+* Closure σ) (e : (absoluteRep σ).Equiv (adjoint J ι))
    (a : A) (ha : a ^ 2 = 1)
    (hg : AdjointGraphIntertwiner J ι (actionHom σ)
      ((actionImage σ).normalizerMonoidHom a.val)) :
    IsTransposeOperator (K := Closure σ) (W := AbsoluteSpace σ)
      (absoluteActorRepresentation σ A hl a) := by
  obtain ⟨S, htr, hS⟩ := hg
  have heq := absoluteActor_eq_graph_intertwiner J σ A hl ι e a ha S
    (IsTransposeOperator.square_one (K := Closure σ) (W := AdjointSpace (Closure σ)) htr) hS
  obtain ⟨c, hc⟩ := htr
  refine ⟨e.toLinearEquiv.trans c, ?_⟩
  intro v
  change adjointMatrix (c (e (absoluteActorRepresentation σ A hl a v))) =
    (adjointMatrix (c (e v))).transpose
  exact (congrArg (fun w => adjointMatrix (c w)) (heq v)).trans (hc (e v))

end Representation.SU3.CubicDegree.SchurOuter.AdjointBounds.OuterTranspose
