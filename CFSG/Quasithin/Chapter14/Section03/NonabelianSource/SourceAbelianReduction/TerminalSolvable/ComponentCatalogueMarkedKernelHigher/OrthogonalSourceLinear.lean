module
public import Theory.Representation.IsotypicCopies
public import Theory.Representation.CentralizerMultiplicity
public import Theory.Representation.NormalComponentConstituents.Orthogonal
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Binary fixed intertwiners for the marked higher-multiplicity construction

An involution on a binary space fixes at least half its dimension. Applying
this to the intertwining space of a homogeneous normal restriction bounds
its multiplicity when all fixed simple images lie in one constituent. These
linear-algebra tools also give a perfect-pairing decomposition with one
isotropic constituent.

Source: Aschbacher--Smith, G.11.9(1), printed p.369.
-/

namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.MarkedHigherOrthogonal
open Module
open scoped MonoidAlgebra
public noncomputable section
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

section HomDimension
variable {A k S V : Type*} [Ring A] [Field k] [Algebra k A]
  [AddCommGroup S] [Module A S] [Module k S] [IsScalarTower k A S]
  [AddCommGroup V] [Module A V] [Module k V] [IsScalarTower k A V]
  [SMulCommClass A k S] [SMulCommClass A k V]
  [FiniteDimensional k S] [FiniteDimensional k V]

def homCoordinates {n : ℕ} (e : V ≃ₗ[A] (Fin n → S)) :
    (S →ₗ[A] V) ≃ₗ[k] (Fin n → (S →ₗ[A] S)) where
  toFun f := fun i => (LinearMap.proj i).comp (e.toLinearMap.comp f)
  invFun f := e.symm.toLinearMap.comp (LinearMap.pi f)
  left_inv f := by ext v; simp
  right_inv f := by ext i v; simp
  map_add' f g := by ext i v; simp
  map_smul' a f := by
    ext i v
    change e (a • f v) i = a • e (f v) i
    exact congrFun ((e.restrictScalars k).map_smul a (f v)) i

theorem hom_dimension_ratio [IsSemisimpleModule A V]
    (h : IsIsotypicOfType A V S) :
    finrank k (S →ₗ[A] V) * finrank k S =
      finrank k V * finrank k (S →ₗ[A] S) := by
  let : FiniteDimensional k (S →ₗ[A] S) :=
    FiniteDimensional.of_injective
      ({ toFun := fun f : S →ₗ[A] S => f.restrictScalars k
         map_add' := fun _ _ => rfl
         map_smul' := fun _ _ => rfl } : (S →ₗ[A] S) →ₗ[k] (S →ₗ[k] S))
      (LinearMap.restrictScalars_injective k)
  let : Module.Finite A V := Module.Finite.of_restrictScalars_finite k A V
  obtain ⟨n,⟨e⟩⟩ := h.linearEquiv_fun
  have hv := (e.restrictScalars k).finrank_eq
  have hf := (homCoordinates (k := k) e).finrank_eq
  change finrank k V = finrank k (Fin n → S) at hv
  rw [Module.finrank_pi_fintype] at hv
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,nsmul_eq_mul] at hv
  change finrank k (S →ₗ[A] V) = finrank k (Fin n → (S →ₗ[A] S)) at hf
  simp only [finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at hf
  rw [hv, hf]
  ac_rfl
end HomDimension

section Involution
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
theorem involution_half_fixed (t : Module.End (ZMod 2) V)
    (ht : t.comp t = LinearMap.id) :
    finrank (ZMod 2) V ≤ 2 * finrank (ZMod 2) (t - LinearMap.id).ker := by
  let d := t - LinearMap.id
  have hr : d.range ≤ d.ker := by
    rintro _ ⟨v,rfl⟩
    change t (t v - v) - (t v - v) = 0
    have ht' := LinearMap.congr_fun ht v
    change t (t v) = v at ht'
    rw [map_sub, ht']
    have hc : ∀ w : V, w + w = 0 := fun w => by
      simpa only [two_smul, zero_smul] using congrArg (fun a : ZMod 2 => a • w) (by decide : (2 : ZMod 2) = 0)
    have hn : ∀ w : V, -w = w := fun w => neg_eq_iff_add_eq_zero.mpr (hc w)
    simp only [sub_eq_add_neg,hn]
    rw [add_assoc,← add_assoc (t v),hc,zero_add,hc]
  have hf := d.finrank_range_add_finrank_ker
  change finrank (ZMod 2) V ≤ 2 * finrank (ZMod 2) d.ker
  have hm := Submodule.finrank_mono hr
  omega
end Involution

open Representation Subgroup Representation.BinaryOffender
section Conjugation
variable {D W : Type*} [Group D] [AddCommGroup W] [Module (ZMod 2) W]
  (ρ : Representation (ZMod 2) D W) (H : Subgroup D) [H.Normal]
  (R J : Subrepresentation (ρ.comp H.subtype)) (x : D)
  (hxR : x ∈ subspaceStabilizer ρ R.toSubmodule)
  (hxJ : x ∈ subspaceStabilizer ρ J.toSubmodule)

def restrictedActor : Module.End (ZMod 2) R.toSubmodule :=
  ((ρ x).comp R.toSubmodule.subtype).codRestrict R.toSubmodule
    (fun w => (hxR w).mpr w.property)

def conjugateHom : Module.End (ZMod 2)
    (IntertwiningMap R.toRepresentation J.toRepresentation) where
  toFun f := {
    toLinearMap := (restrictedActor ρ H J x hxJ).comp
      (f.toLinearMap.comp (restrictedActor ρ H R x⁻¹
        ((subspaceStabilizer ρ R.toSubmodule).inv_mem hxR)))
    isIntertwining' h := by
      let h' : H := ⟨x⁻¹ * h * x, by
        have hn : x⁻¹ ∈ normalizer (H : Set D) := by rw [H.normalizer_eq_top]; trivial
        simpa only [inv_inv] using (mem_normalizer_iff.mp hn h).mp h.property⟩
      have hmove (w : R.toSubmodule) :
          restrictedActor ρ H R x⁻¹ ((subspaceStabilizer ρ R.toSubmodule).inv_mem hxR)
            (R.toRepresentation h w) =
          R.toRepresentation h' (restrictedActor ρ H R x⁻¹
            ((subspaceStabilizer ρ R.toSubmodule).inv_mem hxR) w) := by
        apply Subtype.ext
        change ρ x⁻¹ (ρ h w.val) = ρ (h' : D) (ρ x⁻¹ w.val)
        simp only [h', map_mul, Module.End.mul_apply]
        simp
      apply LinearMap.ext
      intro w
      change restrictedActor ρ H J x hxJ (f (restrictedActor ρ H R x⁻¹
        ((subspaceStabilizer ρ R.toSubmodule).inv_mem hxR) (R.toRepresentation h w))) =
        J.toRepresentation h (restrictedActor ρ H J x hxJ (f (restrictedActor ρ H R x⁻¹
        ((subspaceStabilizer ρ R.toSubmodule).inv_mem hxR) w)))
      rw [hmove,f.isIntertwining]
      apply Subtype.ext
      change ρ x (ρ (h' : D) _) = ρ h (ρ x _)
      simp only [h',map_mul,Module.End.mul_apply]
      simp }
  map_add' f g := by ext w; exact map_add _ _ _
  map_smul' a f := by
    apply IntertwiningMap.ext
    apply LinearMap.ext
    intro w
    exact map_smul (restrictedActor ρ H J x hxJ) a (f
      (restrictedActor ρ H R x⁻¹ ((subspaceStabilizer ρ R.toSubmodule).inv_mem hxR) w))

theorem conjugateHom_sq (hx : x * x = 1) :
    (conjugateHom ρ H R J x hxR hxJ).comp
      (conjugateHom ρ H R J x hxR hxJ) = LinearMap.id := by
  have hxi : x⁻¹ * x⁻¹ = 1 := by rw [← mul_inv_rev, hx, inv_one]
  have hR (w : R.toSubmodule) :
      restrictedActor ρ H R x⁻¹ ((subspaceStabilizer ρ R.toSubmodule).inv_mem hxR)
        (restrictedActor ρ H R x⁻¹ ((subspaceStabilizer ρ R.toSubmodule).inv_mem hxR) w) = w := by
    apply Subtype.ext
    change ρ x⁻¹ (ρ x⁻¹ w.val) = w.val
    rw [← Module.End.mul_apply,← map_mul,hxi,map_one]
    rfl
  apply LinearMap.ext
  intro f
  apply IntertwiningMap.ext
  apply LinearMap.ext
  intro w
  apply Subtype.ext
  change ρ x (ρ x (f (restrictedActor ρ H R x⁻¹
    ((subspaceStabilizer ρ R.toSubmodule).inv_mem hxR) (restrictedActor ρ H R x⁻¹
    ((subspaceStabilizer ρ R.toSubmodule).inv_mem hxR) w))).val) = (f w).val
  rw [hR,← Module.End.mul_apply,← map_mul,hx,map_one]
  rfl
end Conjugation

section IsotypicBridge
variable {D W : Type*} [Group D] [AddCommGroup W] [Module (ZMod 2) W]
  (σ : Representation (ZMod 2) D W) (R : Subrepresentation σ)

def subtypeIntertwiner : IntertwiningMap R.toRepresentation σ where
  toLinearMap := R.toSubmodule.subtype
  isIntertwining' _ := by ext; rfl

def subtypeModuleEquiv : R.toRepresentation.asModule ≃ₗ[(ZMod 2)[D]] R.asSubmodule := by
  let f := (IntertwiningMap.equivLinearMapAsModule R.toRepresentation σ
    (subtypeIntertwiner σ R)).codRestrict R.asSubmodule (fun w => w.property)
  exact LinearEquiv.ofBijective f ⟨fun v w he => Subtype.ext (congrArg Subtype.val he),
    fun w => ⟨⟨w.val,w.property⟩,rfl⟩⟩

theorem isotypic_of_sameModule
    (hh : ∀ J : Subrepresentation σ, IsIrreducible J.toRepresentation →
      Homogeneous.SameModule R J) :
    IsIsotypicOfType (ZMod 2)[D] σ.asModule R.toRepresentation.asModule := by
  intro m hm
  let J := Subrepresentation.ofSubmodule' m
  have hj : IsIrreducible J.toRepresentation := by
    apply (Subrepresentation.irreducible_iff_isAtom J).mpr
    exact (Subrepresentation.subrepresentationSubmoduleOrderIso.isAtom_iff J).mp
      (isSimpleModule_iff_isAtom.mp hm)
  obtain ⟨e⟩ := (Homogeneous.sameModule_iff_linearEquiv R J).mp (hh J hj)
  exact ⟨e.symm.trans (subtypeModuleEquiv σ R).symm⟩

variable [FiniteDimensional (ZMod 2) W]
theorem intertwining_dimension_ratio (J : Subrepresentation σ)
    (hh : IsIsotypicOfType (ZMod 2)[D] σ.asModule R.toRepresentation.asModule)
    [IsSemisimpleModule (ZMod 2)[D] σ.asModule] :
    finrank (ZMod 2) (IntertwiningMap R.toRepresentation J.toRepresentation) *
      finrank (ZMod 2) R.toSubmodule =
    finrank (ZMod 2) J.toSubmodule *
      finrank (ZMod 2) (IntertwiningMap R.toRepresentation R.toRepresentation) := by
  let j := IntertwiningMap.equivLinearMapAsModule J.toRepresentation σ
    (subtypeIntertwiner σ J)
  have hj : Function.Injective j := J.toSubmodule.subtype_injective
  let : IsSemisimpleModule (ZMod 2)[D] J.toRepresentation.asModule :=
    IsSemisimpleModule.of_injective j hj
  let : Module.Finite (ZMod 2) R.toRepresentation.asModule :=
    R.toRepresentation.asModuleEquiv.symm.finiteDimensional
  let : Module.Finite (ZMod 2) J.toRepresentation.asModule :=
    J.toRepresentation.asModuleEquiv.symm.finiteDimensional
  have h := hom_dimension_ratio (k := ZMod 2) (hh.of_injective j hj)
  rw [← (IntertwiningMap.equivLinearMapAsModule R.toRepresentation J.toRepresentation).finrank_eq,
    ← (IntertwiningMap.equivLinearMapAsModule R.toRepresentation R.toRepresentation).finrank_eq] at h
  simpa only [R.toRepresentation.asModuleEquiv.finrank_eq,
    J.toRepresentation.asModuleEquiv.finrank_eq] using h
end IsotypicBridge

section FixedRange
variable {D W : Type*} [Group D] [AddCommGroup W] [Module (ZMod 2) W]
  (ρ : Representation (ZMod 2) D W) (H : Subgroup D) [H.Normal]
  (R J : Subrepresentation (ρ.comp H.subtype)) (x : D)
  (hxR : x ∈ subspaceStabilizer ρ R.toSubmodule)
  (hxJ : x ∈ subspaceStabilizer ρ J.toSubmodule)

theorem fixedHom_intertwines_actor (f : IntertwiningMap R.toRepresentation J.toRepresentation)
    (hf : conjugateHom ρ H R J x hxR hxJ f = f) (w : R.toSubmodule) :
    ρ x (f w).val = (f (restrictedActor ρ H R x hxR w)).val := by
  have he := congrArg (fun q : IntertwiningMap R.toRepresentation J.toRepresentation =>
    (q (restrictedActor ρ H R x hxR w)).val) hf
  have hw : restrictedActor ρ H R x⁻¹ ((subspaceStabilizer ρ R.toSubmodule).inv_mem hxR)
      (restrictedActor ρ H R x hxR w) = w := by
    apply Subtype.ext
    exact ρ.inv_self_apply x w.val
  change ρ x (f (restrictedActor ρ H R x⁻¹
    ((subspaceStabilizer ρ R.toSubmodule).inv_mem hxR)
    (restrictedActor ρ H R x hxR w))).val = _ at he
  rw [hw] at he
  exact he

/-- The ambient image of an actual fixed intertwiner. -/
def ambientRange (f : IntertwiningMap R.toRepresentation J.toRepresentation) :
    Subrepresentation (ρ.comp H.subtype) := (subtypeIntertwiner _ J).comp f |>.range

omit [H.Normal] in
/-- Membership in the ambient image uses the original vectors and inclusion. -/
theorem mem_ambientRange_iff
    (f : IntertwiningMap R.toRepresentation J.toRepresentation) (w : W) :
    w ∈ (ambientRange ρ H R J f).toSubmodule ↔ ∃ u, (f u).val = w := Iff.rfl

theorem fixedHom_range_stable (hx : x * x = 1)
    (f : IntertwiningMap R.toRepresentation J.toRepresentation)
    (hf : conjugateHom ρ H R J x hxR hxJ f = f) :
    x ∈ subspaceStabilizer ρ (ambientRange ρ H R J f).toSubmodule := by
  have he := fixedHom_intertwines_actor ρ H R J x hxR hxJ f hf
  have hxx (w : W) : ρ x (ρ x w) = w := by
    rw [← Module.End.mul_apply,← map_mul,hx,map_one]; rfl
  intro w
  constructor
  · rintro ⟨u,hu⟩
    refine ⟨restrictedActor ρ H R x hxR u, ?_⟩
    change (f (restrictedActor ρ H R x hxR u)).val = w
    rw [← he,show (f u).val = ρ x w from hu,hxx]
  · rintro ⟨u,rfl⟩
    exact ⟨restrictedActor ρ H R x hxR u, (he u).symm⟩

omit [H.Normal] in
theorem ambientRange_irreducible [IsIrreducible R.toRepresentation]
    (f : IntertwiningMap R.toRepresentation J.toRepresentation) (hf : f ≠ 0) :
    IsIrreducible (ambientRange ρ H R J f).toRepresentation := by
  let f' := (subtypeIntertwiner (ρ.comp H.subtype) J).comp f
  have hi : Function.Injective f' := J.toSubmodule.subtype_injective.comp
    ((IsIrreducible.injective_or_eq_zero f).resolve_right hf)
  let q : IntertwiningMap R.toRepresentation (ambientRange ρ H R J f).toRepresentation := {
    toLinearMap := f'.toLinearMap.rangeRestrict
    isIntertwining' h := by
      apply LinearMap.ext
      intro w
      exact Subtype.ext (LinearMap.congr_fun (f'.isIntertwining' h) w) }
  have hq : Function.Bijective q := ⟨by
    intro u v he
    apply hi
    change (q u).val = (q v).val
    exact congrArg Subtype.val he, by
    rintro ⟨w,u,rfl⟩
    exact ⟨u,rfl⟩⟩
  let e := q.ofBijective hq
  let e' : R.toRepresentation ≃ₗ (ambientRange ρ H R J f).toRepresentation :=
    ⟨e.toLinearEquiv,e.isIntertwining'⟩
  exact (RepEquiv.irreducible_euqiv e').mp inferInstance
end FixedRange

section FixedDimension
variable {D W : Type*} [Group D] [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]
  (ρ : Representation (ZMod 2) D W) (H : Subgroup D) [H.Normal]
  (R J : Subrepresentation (ρ.comp H.subtype)) (x : D)
  (hxR : x ∈ subspaceStabilizer ρ R.toSubmodule)
  (hxJ : x ∈ subspaceStabilizer ρ J.toSubmodule)

def fixedHomToEnd
    (hall : ∀ f : IntertwiningMap R.toRepresentation J.toRepresentation,
      conjugateHom ρ H R J x hxR hxJ f = f → ∀ w, (f w).val ∈ R.toSubmodule) :
    (conjugateHom ρ H R J x hxR hxJ - LinearMap.id).ker →ₗ[ZMod 2]
      IntertwiningMap R.toRepresentation R.toRepresentation where
  toFun f := {
    toLinearMap := ((subtypeIntertwiner _ J).toLinearMap.comp f.val.toLinearMap).codRestrict
      R.toSubmodule (hall f.val (sub_eq_zero.mp f.property))
    isIntertwining' h := by
      apply LinearMap.ext
      intro w
      apply Subtype.ext
      exact congrArg (fun z : J.toSubmodule => z.val)
        (LinearMap.congr_fun (f.val.isIntertwining' h) w) }
  map_add' _ _ := by ext; rfl
  map_smul' _ _ := by ext; rfl

theorem fixedHom_finrank_le_end
    (hall : ∀ f : IntertwiningMap R.toRepresentation J.toRepresentation,
      conjugateHom ρ H R J x hxR hxJ f = f → ∀ w, (f w).val ∈ R.toSubmodule) :
    finrank (ZMod 2) (conjugateHom ρ H R J x hxR hxJ - LinearMap.id).ker ≤
      finrank (ZMod 2) (IntertwiningMap R.toRepresentation R.toRepresentation) := by
  apply LinearMap.finrank_le_finrank_of_injective (f := fixedHomToEnd ρ H R J x hxR hxJ hall)
  intro f g he
  apply Subtype.ext
  apply IntertwiningMap.ext
  apply LinearMap.ext
  intro w
  exact Subtype.ext (congrArg (fun q : IntertwiningMap R.toRepresentation R.toRepresentation =>
    (q w).val) he)

theorem dimension_le_twice_of_fixedHom_range
    [IsIrreducible R.toRepresentation]
    [IsSemisimpleModule (ZMod 2)[H] (Representation.asModule (ρ.comp H.subtype))]
    (hh : IsIsotypicOfType (ZMod 2)[H] (Representation.asModule (ρ.comp H.subtype))
      R.toRepresentation.asModule)
    (hx : x*x = 1)
    (hall : ∀ f : IntertwiningMap R.toRepresentation J.toRepresentation,
      conjugateHom ρ H R J x hxR hxJ f = f → ∀ w, (f w).val ∈ R.toSubmodule) :
    finrank (ZMod 2) J.toSubmodule ≤ 2 * finrank (ZMod 2) R.toSubmodule := by
  have hfix := fixedHom_finrank_le_end ρ H R J x hxR hxJ hall
  have hhalf := involution_half_fixed (conjugateHom ρ H R J x hxR hxJ)
    (conjugateHom_sq ρ H R J x hxR hxJ hx)
  have hratio := intertwining_dimension_ratio (ρ.comp H.subtype) R J hh
  let : Nontrivial R.toSubmodule := Subrepresentation.irreducible_module_nontrivial R.toRepresentation
  have he : (0 : ℕ) < finrank (ZMod 2)
      (IntertwiningMap R.toRepresentation R.toRepresentation) := by
    apply Module.finrank_pos_iff.mpr
    refine ⟨⟨IntertwiningMap.id R.toRepresentation,0,?_⟩⟩
    intro hz
    obtain ⟨w,hw⟩ := exists_ne (0 : R.toSubmodule)
    exact hw (congrArg (fun f : IntertwiningMap R.toRepresentation R.toRepresentation => f w) hz)
  have hb : finrank (ZMod 2) (IntertwiningMap R.toRepresentation J.toRepresentation) ≤
      2 * finrank (ZMod 2) (IntertwiningMap R.toRepresentation R.toRepresentation) := by omega
  nlinarith
end FixedDimension

section UniqueImage
variable {D W : Type*} [Group D] [AddCommGroup W] [Module (ZMod 2) W]
  (ρ : Representation (ZMod 2) D W) (H : Subgroup D) [H.Normal]
  (R J : Subrepresentation (ρ.comp H.subtype)) (x : D)
  (hxR : x ∈ subspaceStabilizer ρ R.toSubmodule)
  (hxJ : x ∈ subspaceStabilizer ρ J.toSubmodule)
  [IsIrreducible R.toRepresentation]

theorem fixedHom_range_of_unique_constituent (hx : x*x=1)
    (hunique : ∀ K : Subrepresentation (ρ.comp H.subtype),
      IsIrreducible K.toRepresentation → K ≤ J →
      x ∈ subspaceStabilizer ρ K.toSubmodule → K ≤ R)
    (f : IntertwiningMap R.toRepresentation J.toRepresentation)
    (hf : conjugateHom ρ H R J x hxR hxJ f = f) :
    ∀ w, (f w).val ∈ R.toSubmodule := by
  by_cases hz : f = 0
  · subst f
    intro w
    exact R.toSubmodule.zero_mem
  · have hle : ambientRange ρ H R J f ≤ R := hunique _
      (ambientRange_irreducible ρ H R J f hz)
      (by rintro _ ⟨w,rfl⟩; exact (f w).property)
      (fixedHom_range_stable ρ H R J x hxR hxJ hx f hf)
    exact fun w => hle (show (f w).val ∈ ambientRange ρ H R J f from ⟨w,rfl⟩)
end UniqueImage

section Pairing
variable {D W : Type*} [Group D] [AddCommGroup W] [Module (ZMod 2) W]
  (σ : Representation (ZMod 2) D W) (B : LinearMap.BilinForm (ZMod 2) W)
  (hpres : ∀ g v w, B (σ g v) (σ g w) = B v w)
include hpres

theorem paired_sum_nondegenerate (halt : B.IsAlt) (R J : Subrepresentation σ)
    (hi : IsIrreducible R.toRepresentation) (hj : IsIrreducible J.toRepresentation)
    (hiso : ∀ u ∈ R.toSubmodule, ∀ w ∈ R.toSubmodule, B u w = 0)
    (hne : ∃ u ∈ R.toSubmodule, ∃ w ∈ J.toSubmodule, B u w ≠ 0) :
    (B.restrict (R.toSubmodule ⊔ J.toSubmodule)).Nondegenerate := by
  have hf := bilinearCrossPairing_injective σ B hpres R J hi hne
  have hg := bilinearCrossPairing_injective σ B hpres J R hj (by
    obtain ⟨u,hu,w,hw,hn⟩ := hne
    exact ⟨w,hw,u,hu,fun he => hn (halt.isRefl _ _ he)⟩)
  have hl : (B.restrict (R.toSubmodule ⊔ J.toSubmodule)).SeparatingLeft := by
    intro z hz
    obtain ⟨i,hiI,j,hjJ,hij⟩ := Submodule.mem_sup.mp z.property
    have hzeroJ : j = 0 := by
      have he : bilinearCrossPairing σ B hpres J R ⟨j,hjJ⟩ =
          bilinearCrossPairing σ B hpres J R 0 := by
        ext w
        change B j w.val = B 0 w.val
        have hh := hz ⟨w.val,Submodule.mem_sup_left w.property⟩
        change B z.val w.val = 0 at hh
        rw [← hij,map_add,LinearMap.add_apply,hiso i hiI w.val w.property,zero_add] at hh
        exact hh.trans (by simp)
      exact congrArg Subtype.val (hg he)
    have hzeroI : i = 0 := by
      have he : bilinearCrossPairing σ B hpres R J ⟨i,hiI⟩ =
          bilinearCrossPairing σ B hpres R J 0 := by
        ext w
        change B i w.val = B 0 w.val
        have hh := hz ⟨w.val,Submodule.mem_sup_right w.property⟩
        change B z.val w.val = 0 at hh
        rw [← hij,hzeroJ,add_zero] at hh
        exact hh.trans (by simp)
      exact congrArg Subtype.val (hf he)
    apply Subtype.ext
    change z.val = 0
    rw [← hij,hzeroI,hzeroJ,add_zero]
  exact ⟨hl,fun w hw => hl w fun v => halt.isRefl _ _ (hw v)⟩
end Pairing

section SmallSubrepresentation
variable {D W : Type*} [Group D] [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]
  (σ : Representation (ZMod 2) D W)
  [IsSemisimpleModule (ZMod 2)[D] σ.asModule]

theorem irreducible_of_small_dimension (K : Subrepresentation σ)
    (d : ℕ)
    (heq : ∀ N : Subrepresentation σ, IsIrreducible N.toRepresentation →
      finrank (ZMod 2) N.toSubmodule = d)
    (hK : K ≠ ⊥) (hsmall : finrank (ZMod 2) K.toSubmodule ≤ d) :
    IsIrreducible K.toRepresentation := by
  obtain ⟨m,hm,hi⟩ := (IsSemisimpleModule.eq_bot_or_exists_simple_le K.asSubmodule).resolve_left
    (fun hz => hK (Subrepresentation.subrepresentationSubmoduleOrderIso.injective hz))
  let N := Subrepresentation.ofSubmodule' m
  have hirr : IsIrreducible N.toRepresentation := by
    apply (Subrepresentation.irreducible_iff_isAtom N).mpr
    exact (Subrepresentation.subrepresentationSubmoduleOrderIso.isAtom_iff N).mp
      (isSimpleModule_iff_isAtom.mp hi)
  have hle : N ≤ K := hm
  have hd := heq N hirr
  have hdim := Submodule.finrank_mono (show N.toSubmodule ≤ K.toSubmodule from hle)
  have hn : N = K := Subrepresentation.toSubmodule_injective
    (Submodule.eq_of_le_of_finrank_eq hle (by omega))
  exact hn ▸ hirr
end SmallSubrepresentation

end
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.MarkedHigherOrthogonal
