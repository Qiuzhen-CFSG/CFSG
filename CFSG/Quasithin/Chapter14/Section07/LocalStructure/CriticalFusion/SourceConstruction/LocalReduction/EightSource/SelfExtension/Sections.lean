module
public import Theory.Representation.SubspaceQuotient
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.Algebra.Group.Submonoid.Operations
import Mathlib.Tactic.Abel

/-!
# Sections of an extension with specified constituent coordinates

A linear section of the quotient gives the literal off-diagonal cochain.
Correcting that section on a generating set gives an invariant complement to
the specified subrepresentation. The kernel and quotient coordinates may have
different dimensions, so the construction applies to both original S₈ covers.
-/

public noncomputable section
open Representation
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightSource.SelfExtension
variable {k G W U V : Type*} [Field k] [Group G]
  [AddCommGroup W] [Module k W] [AddCommGroup U] [Module k U]
  [AddCommGroup V] [Module k V]

/-- A chosen linear splitting, its specified kernel, and its off-diagonal cochain. -/
structure SectionData (ρ : Representation k G W) (X : Subrepresentation ρ)
    (τ : Representation k G U) (σ : Representation k G V) where
  inclusion : U →ₗ[k] W
  projection : W →ₗ[k] V
  lift : V →ₗ[k] W
  cochain : G → V →ₗ[k] U
  inclusion_injective : Function.Injective inclusion
  inclusion_range : inclusion.range = X.toSubmodule
  projection_ker : projection.ker = X.toSubmodule
  projection_section : ∀ v, projection (lift v) = v
  projection_inclusion : ∀ u, projection (inclusion u) = 0
  inclusion_equivariant : ∀ g u, ρ g (inclusion u) = inclusion (τ g u)
  projection_equivariant : ∀ g w, projection (ρ g w) = σ g (projection w)
  block : ∀ g v, ρ g (lift v) = inclusion (cochain g v) + lift (σ g v)
  cochain_mul : ∀ g h, cochain (g*h) = (τ g).comp (cochain h) + (cochain g).comp (σ h)

/-- Any given constituent identifications admit literal triangular section data. -/
theorem exists_section_data (ρ : Representation k G W) (X : Subrepresentation ρ)
    (τ : Representation k G U) (σ : Representation k G V)
    (eX : X.toSubmodule ≃ₗ[k] U) (eQ : (W ⧸ X.toSubmodule) ≃ₗ[k] V)
    (heX : ∀ g x, eX (X.toRepresentation g x) = τ g (eX x))
    (heQ : ∀ g x, eQ (X.quotientRepresentation g x) = σ g (eQ x)) :
    Nonempty (SectionData ρ X τ σ) := by
  let i : U →ₗ[k] W := X.toSubmodule.subtype.comp eX.symm.toLinearMap
  let q : W →ₗ[k] V := eQ.toLinearMap.comp X.toSubmodule.mkQ
  have hi : Function.Injective i := Subtype.val_injective.comp eX.symm.injective
  have hq : Function.Surjective q := eQ.surjective.comp X.toSubmodule.mkQ_surjective
  have hie (g : G) (u : U) : ρ g (i u) = i (τ g u) := by
    have hh := heX g (eX.symm u)
    rw [eX.apply_symm_apply] at hh
    have hh' := congrArg eX.symm hh
    rw [eX.symm_apply_apply] at hh'
    exact congrArg Subtype.val hh'
  have hqe (g : G) (w : W) : q (ρ g w) = σ g (q w) :=
    heQ g (X.toSubmodule.mkQ w)
  have hqi (u : U) : q (i u) = 0 := by
    change eQ (X.toSubmodule.mkQ (eX.symm u).val) = 0
    rw [show X.toSubmodule.mkQ (eX.symm u).val = 0 from
      (Submodule.Quotient.mk_eq_zero _).mpr (eX.symm u).property, map_zero]
  have hqker (w : W) : q w = 0 ↔ w ∈ X.toSubmodule := by
    change eQ (X.toSubmodule.mkQ w) = 0 ↔ _
    rw [eQ.map_eq_zero_iff]
    exact Submodule.Quotient.mk_eq_zero _
  obtain ⟨j,hj⟩ := q.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hq)
  have hqj (v : V) : q (j v) = v := LinearMap.congr_fun hj v
  let δ (g : G) : V →ₗ[k] W := (ρ g).comp j - j.comp (σ g)
  have hδ (g : G) (v : V) : δ g v ∈ X.toSubmodule := by
    apply (hqker _).mp
    change q (ρ g (j v) - j (σ g v)) = 0
    rw [map_sub,hqe,hqj,hqj,sub_self]
  let d (g : G) : V →ₗ[k] U :=
    eX.toLinearMap.comp ((δ g).codRestrict X.toSubmodule (hδ g))
  have hid (g : G) (v : V) : i (d g v) = ρ g (j v) - j (σ g v) := by
    change (eX.symm (eX ⟨δ g v,hδ g v⟩)).val = _
    rw [eX.symm_apply_apply]
    rfl
  refine ⟨⟨i,q,j,d,hi,?_,?_,hqj,hqi,hie,hqe,?_,?_⟩⟩
  · ext w
    constructor
    · rintro ⟨u,rfl⟩
      exact (eX.symm u).property
    · intro hw
      exact ⟨eX ⟨w,hw⟩,congrArg Subtype.val (eX.symm_apply_apply ⟨w,hw⟩)⟩
  · ext w
    exact hqker w
  · intro g v
    rw [hid,sub_add_cancel]
  · intro g h
    apply LinearMap.ext
    intro v
    apply hi
    simp only [LinearMap.add_apply,LinearMap.comp_apply,map_add]
    rw [hid,←hie,hid,hid,map_sub,map_mul,map_mul,
      Module.End.mul_apply,Module.End.mul_apply]
    abel

/-- A coboundary correction on generators yields a complement to the same
specified submodule, together with the original quotient action on that complement. -/
theorem SectionData.complement_of_generator_correction
    {ρ : Representation k G W} {X : Subrepresentation ρ}
    {τ : Representation k G U} {σ : Representation k G V}
    (s : SectionData ρ X τ σ) (S : Set G) (hS : Submonoid.closure S = ⊤)
    (D : V →ₗ[k] U)
    (hD : ∀ g ∈ S, s.cochain g = (τ g).comp D - D.comp (σ g)) :
    ∃ K : Subrepresentation ρ, IsCompl X.toSubmodule K.toSubmodule ∧
      ∃ eK : K.toSubmodule ≃ₗ[k] V,
        ∀ g v, eK (K.toRepresentation g v) = σ g (eK v) := by
  let j : V →ₗ[k] W := s.lift - s.inclusion.comp D
  have hj (v : V) : j v = s.lift v - s.inclusion (D v) := rfl
  have hqj (v : V) : s.projection (j v) = v := by
    rw [hj,map_sub,s.projection_section,s.projection_inclusion,sub_zero]
  let P : Submonoid G := {
    carrier := {g | ∀ v, ρ g (j v) = j (σ g v)}
    one_mem' := by simp
    mul_mem' := by
      intro g h hg hh v
      simp only [map_mul,Module.End.mul_apply]
      rw [hh,hg] }
  have hSP : S ⊆ P := by
    intro g hg v
    rw [hj,hj,map_sub,s.block,s.inclusion_equivariant,hD g hg]
    simp only [LinearMap.sub_apply,LinearMap.comp_apply,map_sub]
    abel
  have hP : P = ⊤ := top_unique (hS ▸ Submonoid.closure_le.mpr hSP)
  have hje (g : G) (v : V) : ρ g (j v) = j (σ g v) := by
    exact (show g ∈ P from hP ▸ trivial) v
  have hji : Function.Injective j := fun v w he => by
    have hh := congrArg s.projection he
    rwa [hqj,hqj] at hh
  let K : Subrepresentation ρ := {
    toSubmodule := j.range
    apply_mem_toSubmodule g := by
      rintro w ⟨v,rfl⟩
      exact ⟨σ g v,(hje g v).symm⟩ }
  have hdisj : Disjoint X.toSubmodule K.toSubmodule := by
    apply Submodule.disjoint_def.mpr
    rintro w hw ⟨v,rfl⟩
    have hv : v = 0 := by
      rw [←s.projection_ker] at hw
      exact (hqj v).symm.trans hw
    rw [hv,map_zero]
  have hsup : X.toSubmodule ⊔ K.toSubmodule = ⊤ := by
    apply top_unique
    intro w _
    apply Submodule.mem_sup.mpr
    refine ⟨w-j (s.projection w),?_,j (s.projection w),⟨s.projection w,rfl⟩,
      sub_add_cancel _ _⟩
    rw [←s.projection_ker]
    change s.projection (w-j (s.projection w)) = 0
    rw [map_sub,hqj,sub_self]
  let E : V ≃ₗ[k] K.toSubmodule := LinearEquiv.ofInjective j hji
  refine ⟨K,⟨hdisj,codisjoint_iff.mpr hsup⟩,E.symm,?_⟩
  intro g v
  apply E.injective
  apply Subtype.ext
  change j (E.symm (K.toRepresentation g v)) = j (σ g (E.symm v))
  rw [←hje]
  have hE (w : K.toSubmodule) : j (E.symm w) = w :=
    congrArg Subtype.val (E.apply_symm_apply w)
  rw [hE,hE]
  rfl

/-- The chosen inclusion and quotient lift give coordinates on the whole extension. -/
@[expose] def SectionData.totalEquiv
    {ρ : Representation k G W} {X : Subrepresentation ρ}
    {τ : Representation k G U} {σ : Representation k G V}
    (s : SectionData ρ X τ σ) : (U × V) ≃ₗ[k] W :=
  LinearEquiv.ofBijective (s.inclusion.coprod s.lift) (by
    constructor
    · apply LinearMap.ker_eq_bot.mp
      apply le_antisymm _ bot_le
      rintro ⟨u,v⟩ h
      have hp := congrArg s.projection h
      change s.projection (s.inclusion u+s.lift v) = s.projection 0 at hp
      rw [map_add,s.projection_inclusion,s.projection_section,zero_add,map_zero] at hp
      have hu : u = 0 := by
        apply s.inclusion_injective
        change s.inclusion u+s.lift v=0 at h
        simpa only [hp,map_zero,add_zero] using h
      exact Prod.ext hu hp
    · intro w
      have hw : w-s.lift (s.projection w) ∈ X.toSubmodule := by
        rw [←s.projection_ker]
        change s.projection (w-s.lift (s.projection w)) = 0
        rw [map_sub,s.projection_section,sub_self]
      rw [←s.inclusion_range] at hw
      obtain ⟨u,hu⟩ := hw
      exact ⟨(u,s.projection w),by
        change s.inclusion u+s.lift (s.projection w)=w
        rw [hu,sub_add_cancel]⟩)

theorem SectionData.totalEquiv_apply
    {ρ : Representation k G W} {X : Subrepresentation ρ}
    {τ : Representation k G U} {σ : Representation k G V}
    (s : SectionData ρ X τ σ) (u : U) (v : V) :
    s.totalEquiv (u,v) = s.inclusion u+s.lift v := rfl

/-- An equivariant chosen complement gives whole-module product coordinates. -/
theorem equiv_prod_of_complement
    (ρ : Representation k G W) (X K : Subrepresentation ρ)
    (hK : IsCompl X.toSubmodule K.toSubmodule)
    (τ : Representation k G U) (σ : Representation k G V)
    (eX : X.toSubmodule ≃ₗ[k] U) (eK : K.toSubmodule ≃ₗ[k] V)
    (heX : ∀ g x, eX (X.toRepresentation g x) = τ g (eX x))
    (heK : ∀ g x, eK (K.toRepresentation g x) = σ g (eK x)) :
    ∃ E : W ≃ₗ[k] U × V, ∀ g w, E (ρ g w) = (τ.prod σ) g (E w) := by
  let p := Submodule.prodEquivOfIsCompl X.toSubmodule K.toSubmodule hK
  let e := p.symm.trans (eX.prodCongr eK)
  refine ⟨e,?_⟩
  intro g w
  obtain ⟨⟨x,v⟩,rfl⟩ := p.surjective w
  have hp : ρ g (p (x,v)) = p (X.toRepresentation g x,K.toRepresentation g v) := by
    change ρ g ((x : W)+(v : W)) = _
    rw [map_add]
    rfl
  rw [hp]
  have he (x : X.toSubmodule) (v : K.toSubmodule) : e (p (x,v)) = (eX x,eK v) := by
    change (eX.prodCongr eK) (p.symm (p (x,v))) = _
    rw [p.symm_apply_apply]
    rfl
  rw [he,he]
  exact Prod.ext (heX g x) (heK g v)

/-- The first product coordinate is a surjective equivariant retraction
onto the original chosen kernel model. -/
theorem surjective_retraction_of_complement
    (ρ : Representation k G W) (X K : Subrepresentation ρ)
    (hK : IsCompl X.toSubmodule K.toSubmodule)
    (τ : Representation k G U) (σ : Representation k G V)
    (eX : X.toSubmodule ≃ₗ[k] U) (eK : K.toSubmodule ≃ₗ[k] V)
    (heX : ∀ g x, eX (X.toRepresentation g x) = τ g (eX x))
    (heK : ∀ g x, eK (K.toRepresentation g x) = σ g (eK x)) :
    ∃ p : W →ₗ[k] U, Function.Surjective p ∧ ∀ g w, p (ρ g w) = τ g (p w) := by
  obtain ⟨e,he⟩ := equiv_prod_of_complement ρ X K hK τ σ eX eK heX heK
  refine ⟨(LinearMap.fst k U V).comp e.toLinearMap,?_,?_⟩
  · intro u
    exact ⟨e.symm (u,0),by simp⟩
  · intro g w
    exact congrArg Prod.fst (he g w)

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightSource.SelfExtension
