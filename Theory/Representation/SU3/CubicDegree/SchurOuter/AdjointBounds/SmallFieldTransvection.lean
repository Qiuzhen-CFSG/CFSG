module

public import Theory.Representation.SU3.CubicDegree.SchurOuter.AdjointBounds.OperatorModels
public import Theory.Representation.SU3.CubicDegree.SchurOuter.AdjointBounds.SmallFieldTransvection.NaturalCoordinates

/-!
# A literal transvection actor at SU₃(4)

The outer automorphism group has two-rank at most one. An elementary actor
of rank at least two therefore contains a nonidentity inner actor. Binary
Schur theory puts that involution in the actual representation image,
removing scalar ambiguity. At the even exponent two, the special-to-projective
map is injective and the projective group is centerless, so a central-kernel
representation is faithful and the actor lifts to a nonidentity involution.

The supplied adjoint Schur intertwiner and the natural transvection coordinates
identify the original scalar-extended operator. Exact Schur-field transport
then gives binary common fixed codimension at least eight. The elementary
subgroup and its literal operators are retained throughout, and no outer
actor is an additional hypothesis.

This discharges the small-field realization contract for the parent adjoint
bounds assembly. Source: Guralnick–Malle, Classification of 2F-modules II,
Proposition 4.11, author manuscript pp.31–32, the adjoint-module exclusion.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false

open BenderSuzuki.MatrixGroups Representation Representation.BinaryOffender
open Subgroup Theory.GroupTheory
namespace Representation.SU3.CubicDegree.SchurOuter.AdjointBounds.SmallField
open HermitianForm.EvenProjectiveComparison
open HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport
variable {F V : Type*} [Field F] [Finite F] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (J : HermitianForm 3 F)
  (hcard : Nat.card F = (2 ^ 2) ^ 2)
  (hconj : ∀ x, J.conj x = x ^ (2 ^ 2))
  (σ : Representation (ZMod 2) J.specialSubgroup V)
  (hk : σ.ker ≤ center J.specialSubgroup)

include hcard hconj hk

omit [FiniteDimensional (ZMod 2) V] in
private theorem faithful : Function.Injective σ := by
  have hz := J.specialToProjective_ker_eq_center
    (center_eq_bot J (by decide : 0 < 2) hcard hconj)
  have hz' : center J.specialSubgroup = ⊥ := hz.symm.trans
    (J.specialToProjective.ker_eq_bot_iff.mpr
      (specialToProjective_injective J (by decide : Even 2) hconj))
  exact σ.ker_eq_bot_iff.mp (le_bot_iff.mp (hz' ▸ hk))

omit [FiniteDimensional (ZMod 2) V] in
private theorem outer_rank_le_one : primeRank 2 (MulAut.Outer (actionImage σ)) ≤ 1 := by
  have hσ : Function.Injective σ.asGroupHom := by
    intro x y h
    apply faithful J hcard hconj σ hk
    exact congrArg Units.val h
  let eσ : J.specialSubgroup ≃* actionImage σ := MonoidHom.ofInjective hσ
  have hf := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 2
    (by decide) hcard hconj
  obtain ⟨eJ⟩ := exists_projectiveEquiv J (2 ^ 2) hcard hf
  let e := eσ.symm.trans
    ((specialProjectiveEquiv J (by decide : Even 2) hconj).trans eJ)
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup (standardForm J)) :=
    Finite.of_surjective (standardForm J).specialToProjective
      (standardForm J).specialToProjective_surjective
  rw [primeRank_equiv 2 (MulAut.outerCongr e)]
  exact HermitianForm.EvenTwoRank.outer_two_rank_le_of_coverage (standardForm J) rfl
    ((standardForm J).semilinear_coverage 2 (by decide) rfl hcard hf)

variable [σ.IsIrreducible]

private theorem exists_inner_actor (A : Subgroup (linearNormalizer σ))
    (hA : IsElementaryTwo A) (hr : 2 ≤ rank A) :
    ∃ a : A, a ≠ 1 ∧
      (a.val : (Module.End (ZMod 2) V)ˣ) ∈ actionImage σ := by
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let : Finite (Module.End (ZMod 2) V) := Finite.of_injective
    (fun f : Module.End (ZMod 2) V => (f : V → V)) DFunLike.coe_injective
  let : IsElementaryAbelian 2 A := hA.2
  let q : A →* MulAut.Outer (actionImage σ) :=
    (QuotientGroup.mk' (MulAut.innerSubgroup (actionImage σ))).comp
      ((actionImage σ).normalizerMonoidHom.comp A.subtype)
  have hn : q.ker ≠ ⊥ := by
    intro hq
    have hi := q.ker_eq_bot_iff.mp hq
    let : IsElementaryAbelian 2 q.range :=
      IsElementaryAbelian.of_surjective q.rangeRestrict q.rangeRestrict_surjective
    have hc := (primeRank_le_iff_elementary_card_le
      (MulAut.Outer (actionImage σ))).mp (outer_rank_le_one J hcard hconj σ hk)
      q.range inferInstance
    have hca : Nat.card A ≤ 2 ^ 1 :=
      (Nat.card_congr (MonoidHom.ofInjective hi).toEquiv).le.trans hc
    have hh := Nat.log_mono_right (b := 2) hca
    have : rank A ≤ 1 := by simpa only [rank, Nat.log_pow (by decide : 1 < 2)] using hh
    omega
  obtain ⟨a, ha, hne⟩ := q.ker.bot_or_exists_ne_one.resolve_left hn
  have hinner : (actionImage σ).normalizerMonoidHom a.val ∈
      MulAut.innerSubgroup (actionImage σ) :=
    (QuotientGroup.eq_one_iff _).mp (show q a = 1 from ha)
  have ha2 : a.val ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian a.val a.property
  exact ⟨a, hne, involution_mem_image_of_inner σ inferInstance a.val ha2 hinner⟩

end Representation.SU3.CubicDegree.SchurOuter.AdjointBounds.SmallField

open Representation Representation.BinaryOffender Representation.FrobeniusTensor
namespace Representation.SU3.CubicDegree.SchurOuter.AdjointBounds.SmallField
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  (σ : Representation (ZMod 2) G V) [σ.IsIrreducible]
  (A : Subgroup (linearNormalizer σ))
  (hl : ∀ t ∈ A, SchurNormalizer.IsSchurLinear σ t)

private theorem absoluteActor_eq_of_image (a : A) (g : G)
    (hg : σ.asGroupHom g = a.val.val) :
    absoluteActorRepresentation σ A hl a = absoluteRep σ g := by
  have hs : schurActorRepresentation σ A hl a = σ.endFieldRep g := by
    ext v
    apply σ.asModuleEquiv.injective
    rw [schurActorRepresentation_apply, endFieldRep_apply, LinearEquiv.apply_symm_apply]
    exact congrArg (fun u : (Module.End (ZMod 2) V)ˣ => u.val (σ.asModuleEquiv v)) hg.symm
  change (schurActorRepresentation σ A hl a).baseChange (Closure σ) =
    (σ.endFieldRep g).baseChange (Closure σ)
  rw [hs]

end Representation.SU3.CubicDegree.SchurOuter.AdjointBounds.SmallField

open BenderSuzuki.MatrixGroups Representation Representation.BinaryOffender
open Representation.FrobeniusTensor Subgroup
namespace Representation.SU3.CubicDegree.SchurOuter.AdjointBounds
open SmallField
private theorem transvection_transport {K U W : Type*} [Field K]
    [AddCommGroup U] [Module K U] [AddCommGroup W] [Module K W]
    (f : Module.End K U) (g : Module.End K W) (e : U ≃ₗ[K] W)
    (he : ∀ u, e (f u) = g (e u)) (hg : IsTransvectionOperator g) :
    IsTransvectionOperator f := by
  obtain ⟨c, hc⟩ := hg
  refine ⟨e.trans c, ?_⟩
  intro u
  simpa only [LinearEquiv.trans_apply, he] using hc (e u)

variable {F V : Type*} [Field F] [Finite F] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (J : HermitianForm 3 F)
  (hcard : Nat.card F = (2 ^ 2) ^ 2)
  (hconj : ∀ x, J.conj x = x ^ (2 ^ 2))
  (σ : Representation (ZMod 2) J.specialSubgroup V) [σ.IsIrreducible]
  (hk : σ.ker ≤ center J.specialSubgroup)
include hcard hconj hk

omit [Finite F] hcard hconj hk in
private theorem absoluteRep_isTransvection (hm : AdjointSchurModel J σ 2)
    (g : J.specialSubgroup) (hg2 : g ^ 2 = 1) (hgne : g ≠ 1) :
    IsTransvectionOperator (absoluteRep σ g) := by
  obtain ⟨ι, ⟨e⟩⟩ := hm.model
  apply transvection_transport (K := Closure σ) (U := AbsoluteSpace σ)
    (W := Representation.SL3.BinaryDefiningFactors.AdjointSpace (Closure σ))
    (absoluteRep σ g) (adjoint J ι g) e.toLinearEquiv
  · intro v
    exact LinearMap.congr_fun (e.isIntertwining' g) v
  · exact adjoint_isTransvection J ι g hg2 hgne

/-- At SU₃(4), every elementary Schur-linear actor of rank at least two contains
an actual operator with transvection coordinates on the adjoint model. -/
theorem smallFieldTransvectionRealization : SmallFieldTransvectionRealization J σ := by
  intro hm A hA hl hr
  let : IsElementaryAbelian 2 A := hA.2
  obtain ⟨a, hane, g, hg⟩ := exists_inner_actor J hcard hconj σ hk A hA hr
  have hi : Function.Injective σ.asGroupHom := by
    intro x y h
    exact faithful J hcard hconj σ hk (congrArg Units.val h)
  have hg2 : g ^ 2 = 1 := by
    apply hi
    rw [map_pow, hg, map_one]
    exact congrArg Subtype.val (elemPow_eq_one_of_isElementaryAbelian a.val a.property)
  have hgne : g ≠ 1 := by
    intro hg1
    apply hane
    apply Subtype.ext
    apply Subtype.ext
    change a.val.val = 1
    simpa only [hg1, map_one] using hg.symm
  refine ⟨a, ?_⟩
  rw [absoluteActor_eq_of_image σ A hl a g hg]
  exact absoluteRep_isTransvection J σ hm g hg2 hgne

/-- Literal consumer: the original binary actor has common fixed codimension
at least eight, without an outer-actor premise. -/
theorem eight_le_fixedCodim_of_smallField (hm : AdjointSchurModel J σ 2)
    (A : Subgroup (linearNormalizer σ)) (hA : IsElementaryTwo A)
    (hl : ∀ t ∈ A, SchurNormalizer.IsSchurLinear σ t) (hr : 2 ≤ rank A) :
    8 ≤ fixedCodim (normalizerRepresentation σ) A := by
  obtain ⟨a, ha⟩ := smallFieldTransvectionRealization J hcard hconj σ hk hm A hA hl hr
  exact four_mul_le_fixedCodim σ A hl hm.fieldDegree a ha

end Representation.SU3.CubicDegree.SchurOuter.AdjointBounds
