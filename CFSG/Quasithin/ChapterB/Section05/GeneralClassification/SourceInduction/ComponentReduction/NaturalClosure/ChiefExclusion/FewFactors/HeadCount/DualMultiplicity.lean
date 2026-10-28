module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.NaturalClosure.ChiefExclusion.FewFactors.Head
public import Theory.Representation.EndFieldRep
public import Theory.Representation.SimpleHeadQuotient
public import Mathlib.RingTheory.Artinian.Module

/-!
# Dual multiplicity spaces and the literal head

For commuting representations τ and σ, the second actor acts on
Hom(τ,S) by precomposition with σ(q⁻¹). Scalars are the actual
endomorphisms of S and act by postcomposition. Thus the action is linear
over End(S); for a finite simple binary module this is a finite field of
characteristic two. No invariant flag for σ is required.

The literal quotient by the τ-module radical is semisimple. Precomposition
with its quotient map identifies its dual multiplicity spaces with those
of τ. Triviality on the spaces for all simple quotients implies triviality
on that same head: every displacement belongs to every maximal submodule.

Source: Aschbacher–Smith, B.5.9, printed p.108, the c = 2 centralizer
argument (1 March 2004 manuscript). These are representation-theoretic
constructions; the chief-flag dimension estimate is a separate step.
-/

@[expose] public section

open Representation
open scoped MonoidAlgebra
namespace CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.NaturalClosure.FewFactors
namespace HeadCount
set_option backward.isDefEq.respectTransparency false
variable {F P Q W S : Type*} [Field F] [Group P] [Group Q]
  [AddCommGroup W] [Module F W] [AddCommGroup S] [Module F S]

/-- Equivariant maps to a simple target, with its endomorphisms acting on the left. -/
abbrev DualMultiplicity (τ : Representation F P W) (π : Representation F P S) :=
  τ.asModule →ₗ[F[P]] π.asModule

/-- A commuting operator is an endomorphism of the literal first module. -/
noncomputable def commutingEnd (τ : Representation F P W) (σ : Representation F Q W)
    (hc : ∀ p q, τ p * σ q = σ q * τ p) (q : Q) :
    Module.End F[P] τ.asModule :=
  IntertwiningMap.equivAlgEnd τ ⟨σ q, fun p => (hc p q).symm⟩

/-- The endomorphism retains the original operator on vectors. -/
@[simp] theorem commutingEnd_apply (τ : Representation F P W) (σ : Representation F Q W)
    (hc : ∀ p q, τ p * σ q = σ q * τ p) (q : Q) (w : τ.asModule) :
    commutingEnd τ σ hc q w = τ.asModuleEquiv.symm (σ q (τ.asModuleEquiv w)) := rfl

/-- The contragredient commuting action, linear over the target endomorphism ring. -/
noncomputable def dualAction (τ : Representation F P W) (σ : Representation F Q W)
    (hc : ∀ p q, τ p * σ q = σ q * τ p) (π : Representation F P S) :
    Representation (Module.End F[P] π.asModule) Q (DualMultiplicity τ π) where
  toFun q := {
    toFun a := a.comp (commutingEnd τ σ hc q⁻¹)
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
  map_one' := by
    ext a w
    change a (τ.asModuleEquiv.symm (σ (1 : Q)⁻¹ (τ.asModuleEquiv w))) = a w
    simp
  map_mul' q r := by
    ext a w
    change a (τ.asModuleEquiv.symm (σ ((q * r)⁻¹) (τ.asModuleEquiv w))) =
      a (τ.asModuleEquiv.symm (σ r⁻¹ (σ q⁻¹ (τ.asModuleEquiv w))))
    rw [mul_inv_rev, map_mul, Module.End.mul_apply]

/-- The action evaluates by precomposition with the inverse actor. -/
@[simp] theorem dualAction_apply (τ : Representation F P W) (σ : Representation F Q W)
    (hc : ∀ p q, τ p * σ q = σ q * τ p) (π : Representation F P S)
    (q : Q) (a : DualMultiplicity τ π) (w : τ.asModule) :
    dualAction τ σ hc π q a w =
      a (τ.asModuleEquiv.symm (σ q⁻¹ (τ.asModuleEquiv w))) := rfl

/-- Over a finite field, the literal equivariant map space is finite. -/
instance dualMultiplicity_finite [Finite F] [Module.Finite F W] [Module.Finite F S]
    (τ : Representation F P W) (π : Representation F P S) :
    Finite (DualMultiplicity τ π) := by
  let : Finite τ.asModule := Module.finite_iff_finite.mp (inferInstance : Module.Finite F W)
  let : Finite π.asModule := Module.finite_iff_finite.mp (inferInstance : Module.Finite F S)
  exact Finite.of_injective (fun a : DualMultiplicity τ π => (a : τ.asModule → π.asModule))
    DFunLike.coe_injective

/-- Its vector-space dimension over the endomorphism field is finite. -/
instance dualMultiplicity_moduleFinite [Finite F] [Module.Finite F W] [Module.Finite F S]
    (τ : Representation F P W) (π : Representation F P S) :
    Module.Finite (Module.End F[P] π.asModule) (DualMultiplicity τ π) :=
  Module.Finite.of_finite

/-- The endomorphism field of a finite simple binary module has characteristic two. -/
instance endField_charTwo {P S : Type*} [Group P] [AddCommGroup S] [Module (ZMod 2) S]
    [Module.Finite (ZMod 2) S] (π : Representation (ZMod 2) P S) [IsIrreducible π] :
    CharP (Module.End (ZMod 2)[P] π.asModule) 2 := by
  exact charP_of_injective_algebraMap (algebraMap (ZMod 2)
    (Module.End (ZMod 2)[P] π.asModule)).injective 2

/-- The actual radical quotient map, linear for the original group algebra. -/
noncomputable def headMap (τ : Representation F P W) :
    τ.asModule →ₗ[F[P]] (Head.representation τ).asModule :=
  IntertwiningMap.equivLinearMapAsModule τ (Head.representation τ)
    ⟨(Head.radical τ).toSubmodule.mkQ, fun _ => rfl⟩

/-- Every head vector has a representative in the original module. -/
theorem headMap_surjective (τ : Representation F P W) : Function.Surjective (headMap τ) :=
  (Head.radical τ).toSubmodule.mkQ_surjective

/-- The kernel is exactly the original group-algebra radical. -/
theorem headMap_ker (τ : Representation F P W) :
    LinearMap.ker (headMap τ) = Module.jacobson F[P] τ.asModule := by
  ext w
  exact Submodule.Quotient.mk_eq_zero (Head.radical τ).toSubmodule

/-- The finite-dimensional literal radical quotient is semisimple. -/
theorem head_semisimple [Module.Finite F W] (τ : Representation F P W) :
    IsSemisimpleModule F[P] (Head.representation τ).asModule := by
  let : IsArtinian F[P] (Head.representation τ).asModule := isArtinian_of_tower F inferInstance
  apply (IsArtinian.isSemisimpleModule_iff_jacobson _ _).mpr
  rw [← Module.map_jacobson_of_ker_le (headMap_surjective τ) (headMap_ker τ).le]
  apply le_bot_iff.mp
  rintro _ ⟨w, hw, rfl⟩
  exact (show Module.jacobson F[P] τ.asModule ≤ LinearMap.ker (headMap τ) from
    (headMap_ker τ).ge) hw

/-- Pullback along the literal head quotient map is endomorphism-linear. -/
noncomputable def dualHeadRestriction (τ : Representation F P W) (π : Representation F P S) :
    DualMultiplicity (Head.representation τ) π →ₗ[Module.End F[P] π.asModule]
      DualMultiplicity τ π where
  toFun a := a.comp (headMap τ)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Every map to a simple module factors uniquely through the actual head. -/
noncomputable def dualHeadEquiv (τ : Representation F P W) (π : Representation F P S)
    [IsIrreducible π] :
    DualMultiplicity (Head.representation τ) π ≃ₗ[Module.End F[P] π.asModule]
      DualMultiplicity τ π := by
  let : IsSimpleModule F[P] π.asModule :=
    (irreducible_iff_isSimpleModule_asModule π).mp inferInstance
  apply LinearEquiv.ofBijective (dualHeadRestriction τ π)
  constructor
  · intro a b he
    ext w
    obtain ⟨v, rfl⟩ := headMap_surjective τ w
    exact DFunLike.congr_fun he v
  · intro a
    let ai := (IntertwiningMap.equivLinearMapAsModule τ π).symm a
    have hk : (Head.radical τ).toSubmodule ≤ LinearMap.ker ai.toLinearMap :=
      IsSemisimpleModule.jacobson_le_ker _ _ _ _ a
    let bi : (Head.representation τ).IntertwiningMap π := {
      toLinearMap := (Head.radical τ).toSubmodule.liftQ ai.toLinearMap hk
      isIntertwining' g := by
        apply LinearMap.ext
        intro w
        induction w using Submodule.Quotient.induction_on with
        | _ v => exact IntertwiningMap.isIntertwining τ π ai g v }
    exact ⟨IntertwiningMap.equivLinearMapAsModule _ _ bi, by ext w; rfl⟩

/-- The comparison is pullback by the actual quotient map. -/
@[simp] theorem dualHeadEquiv_apply (τ : Representation F P W) (π : Representation F P S)
    [IsIrreducible π] (a : DualMultiplicity (Head.representation τ) π) :
    dualHeadEquiv τ π a = a.comp (headMap τ) := rfl

/-- Pullback intertwines the two actual dual commuting actions. -/
theorem dualHeadEquiv_equivariant (τ : Representation F P W) (σ : Representation F Q W)
    (hc : ∀ p q, τ p * σ q = σ q * τ p) (π : Representation F P S)
    [IsIrreducible π] (q : Q) (a : DualMultiplicity (Head.representation τ) π) :
    dualHeadEquiv τ π
        (dualAction (Head.representation τ) (Head.action τ σ hc)
          (Head.action_commute τ σ hc) π q a) =
      dualAction τ σ hc π q (dualHeadEquiv τ π a) := by
  ext w
  rfl

/-- Passing to the head preserves every simple dual multiplicity over its endomorphism field. -/
theorem dualMultiplicity_finrank_head [Finite F] [Module.Finite F S]
    (τ : Representation F P W) (π : Representation F P S) [IsIrreducible π] :
    Module.finrank (Module.End F[P] π.asModule) (DualMultiplicity (Head.representation τ) π) =
      Module.finrank (Module.End F[P] π.asModule) (DualMultiplicity τ π) :=
  (dualHeadEquiv τ π).finrank_eq


/-- Simple quotient maps jointly detect the commuting action on the literal head. -/
theorem head_action_eq_one_of_dualAction_eq_one
    (τ : Representation F P W) (σ : Representation F Q W)
    (hc : ∀ p q, τ p * σ q = σ q * τ p)
    (h : ∀ N : Subrepresentation τ, IsCoatom N →
      dualAction τ σ hc N.quotientRepresentation = 1) : Head.action τ σ hc = 1 := by
  apply (Head.action_eq_one_iff τ σ hc).mpr
  intro q w
  change τ.asModuleEquiv.symm (σ q w - w) ∈ Module.jacobson F[P] τ.asModule
  simp only [Module.jacobson, Submodule.mem_sInf, Set.mem_ofPred_eq]
  intro N hN
  let Nr : Subrepresentation τ := Subrepresentation.ofSubmodule' N
  have hNr : IsCoatom Nr :=
    (Subrepresentation.subrepresentationSubmoduleOrderIso.symm.isCoatom_iff N).mpr hN
  let a : DualMultiplicity τ Nr.quotientRepresentation :=
    IntertwiningMap.equivLinearMapAsModule τ Nr.quotientRepresentation
      ⟨Nr.toSubmodule.mkQ, fun _ => rfl⟩
  have he := congrArg (fun t => t q⁻¹ a (τ.asModuleEquiv.symm w)) (h Nr hNr)
  have he' : Nr.toSubmodule.mkQ (σ q w) = Nr.toSubmodule.mkQ w := by
    change Nr.toSubmodule.mkQ (σ (q⁻¹)⁻¹ w) = Nr.toSubmodule.mkQ w at he
    simpa only [inv_inv] using he
  exact (Submodule.Quotient.eq Nr.toSubmodule).mp he'

end HeadCount
end CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.NaturalClosure.FewFactors
