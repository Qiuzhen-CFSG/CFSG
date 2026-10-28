module

public import CFSG.Quasithin.ChapterG.Section09.TwoComponents.CommonField.Interfaces
public import Theory.Representation.Quotient
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Comparison of homogeneous constituents under quasiequivalence

Transporting the actor isomorphism turns a constituent of the first restriction
into a simple submodule of the second restriction, or of its contragredient.
In the first case, homogeneity identifies it with the chosen second constituent.
In the second case, duality gives a simple quotient of the second restriction;
semisimplicity realizes this quotient as a submodule, so homogeneity again applies.

Finite-dimensional duality preserves irreducibility and binary dimension.
Transposition identifies the full endomorphism ring with the opposite ring of
the dual. Together with the equivariant constituent identification, this proves
both numerical clauses of `ConstituentComparisonTheorem`. No tensor realization
or identification of fields without an equivariant module comparison is used.

Source: Aschbacher--Smith, combined manuscript, G.9.3, first paragraph,
printed p.356 (PDF p.367).
-/

public noncomputable section

open scoped MonoidAlgebra
open Representation

namespace CFSG.Quasithin.ChapterG.Section09.TwoComponents.CommonField.Comparison

variable {k G H V W : Type*} [Field k] [Group G] [Group H]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

private def dualMap {ρ : Representation k G V} {σ : Representation k G W}
    (f : ρ.IntertwiningMap σ) : σ.dual.IntertwiningMap ρ.dual where
  toLinearMap := f.toLinearMap.dualMap
  isIntertwining' g := by
    ext l v
    exact congrArg l (LinearMap.congr_fun (f.isIntertwining' g⁻¹) v).symm

private def bidualEquiv (ρ : Representation k G V) [FiniteDimensional k V] :
    ρ.Equiv ρ.dual.dual where
  toLinearEquiv := Module.evalEquiv k V
  isIntertwining' g := by
    ext v l
    change l (ρ g v) = l (ρ (g⁻¹)⁻¹ v)
    rw [inv_inv]

private theorem dual_irreducible (ρ : Representation k G V) [FiniteDimensional k V]
    [IsIrreducible ρ] : IsIrreducible ρ.dual := by
  let : Nontrivial V := Subrepresentation.irreducible_module_nontrivial ρ
  let : Nontrivial (Module.Dual k V) := by
    have hp : 0 < Module.finrank k (Module.Dual k V) := by
      rw [Subspace.dual_finrank_eq]
      exact Module.finrank_pos
    exact Module.nontrivial_of_finrank_pos hp
  refine ⟨fun S => ?_⟩
  let T : Subrepresentation ρ := {
    toSubmodule := S.toSubmodule.dualCoannihilator
    apply_mem_toSubmodule := fun g v hv => by
      rw [Submodule.mem_dualCoannihilator] at hv ⊢
      intro l hl
      have h := hv (ρ.dual g⁻¹ l) (S.apply_mem_toSubmodule g⁻¹ hl)
      change l (ρ (g⁻¹)⁻¹ v) = 0 at h
      simpa only [inv_inv] using h }
  have ht := IsSimpleOrder.eq_bot_or_eq_top T
  have he := Subspace.dualCoannihilator_dualAnnihilator_eq (W := S.toSubmodule)
  rcases ht with ht | ht
  · right
    apply Subrepresentation.toSubmodule_injective
    have h : S.toSubmodule.dualCoannihilator = ⊥ := congrArg Subrepresentation.toSubmodule ht
    rw [h, Submodule.dualAnnihilator_bot] at he
    exact he.symm
  · left
    apply Subrepresentation.toSubmodule_injective
    have h : S.toSubmodule.dualCoannihilator = ⊤ := congrArg Subrepresentation.toSubmodule ht
    rw [h, Submodule.dualAnnihilator_top] at he
    exact he.symm

private def dualEndHom (ρ : Representation k G V) :
    ρ.IntertwiningMap ρ →+* (ρ.dual.IntertwiningMap ρ.dual)ᵐᵒᵖ where
  toFun f := MulOpposite.op (dualMap f)
  map_one' := by rfl
  map_zero' := by apply MulOpposite.unop_injective; ext l v; exact l.map_zero
  map_add' f g := by apply MulOpposite.unop_injective; ext l v; exact l.map_add _ _
  map_mul' f g := by rfl

private def dualEndEquiv (ρ : Representation k G V) [FiniteDimensional k V] :
    ρ.IntertwiningMap ρ ≃+* (ρ.dual.IntertwiningMap ρ.dual)ᵐᵒᵖ := by
  apply RingEquiv.ofBijective (dualEndHom ρ)
  constructor
  · intro f g h
    ext v
    apply (Module.evalEquiv k V).injective
    ext l
    exact congrArg (fun a : (ρ.dual.IntertwiningMap ρ.dual)ᵐᵒᵖ => a.unop l v) h
  · intro f
    let e := bidualEquiv ρ
    refine ⟨e.symm.toIntertwiningMap.comp ((dualMap f.unop).comp e.toIntertwiningMap), ?_⟩
    apply MulOpposite.unop_injective
    ext l v
    change l ((Module.evalEquiv k V).symm
      (f.unop.toLinearMap.dualMap (Module.evalEquiv k V v))) = f.unop l v
    simp only [Module.apply_evalEquiv_symm_apply, LinearMap.dualMap_apply,
      Module.evalEquiv_apply, Module.Dual.eval_apply]
    rfl

private theorem end_card_dual (ρ : Representation k G V) [FiniteDimensional k V] :
    Nat.card (Module.End k[G] ρ.asModule) =
      Nat.card (Module.End k[G] ρ.dual.asModule) := by
  calc
    _ = Nat.card (ρ.IntertwiningMap ρ) :=
      Nat.card_congr (IntertwiningMap.equivAlgEnd (ρ := ρ)).toEquiv.symm
    _ = Nat.card (ρ.dual.IntertwiningMap ρ.dual) :=
      Nat.card_congr ((dualEndEquiv ρ).toEquiv.trans MulOpposite.opEquiv.symm)
    _ = _ := Nat.card_congr (IntertwiningMap.equivAlgEnd (ρ := ρ.dual)).toEquiv

private def submoduleEquiv (ρ : Representation k G V) (S : Subrepresentation ρ) :
    S.toRepresentation.asModule ≃ₗ[k[G]] S.asSubmodule := by
  let i : S.toRepresentation.IntertwiningMap ρ :=
    ⟨S.toSubmodule.subtype, fun _ => by ext; rfl⟩
  let f := (IntertwiningMap.equivLinearMapAsModule _ _ i).codRestrict
    S.asSubmodule (fun x => x.property)
  exact LinearEquiv.ofBijective f ⟨fun _ _ h => Subtype.ext (congrArg Subtype.val h),
    fun x => ⟨⟨x.val, x.property⟩, rfl⟩⟩

private def pullbackEndEquiv (σ : Representation k H W) (e : G ≃* H) :
    IntertwiningMap (σ.comp e.toMonoidHom) (σ.comp e.toMonoidHom) ≃+*
      σ.IntertwiningMap σ where
  toFun f := ⟨f.toLinearMap, fun h => by
    obtain ⟨g, rfl⟩ := e.surjective h
    exact f.isIntertwining' g⟩
  invFun f := ⟨f.toLinearMap, fun g => f.isIntertwining' (e g)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

private theorem end_card_pullback (σ : Representation k H W) (e : G ≃* H) :
    Nat.card (Module.End k[G] (Representation.asModule (σ.comp e.toMonoidHom))) =
      Nat.card (Module.End k[H] σ.asModule) :=
  Nat.card_congr ((IntertwiningMap.equivAlgEnd (ρ := σ.comp e.toMonoidHom)).toEquiv.symm.trans
    ((pullbackEndEquiv σ e).toEquiv.trans (IntertwiningMap.equivAlgEnd (ρ := σ)).toEquiv))

private theorem isotypic_simple_submodule {R M N S : Type*} [Ring R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup S] [Module R S] [IsSimpleModule R N]
    (h : IsIsotypicOfType R M S) (f : N →ₗ[R] M) (hf : Function.Injective f) :
    Nonempty (N ≃ₗ[R] S) := by
  let e := LinearEquiv.ofInjective f hf
  let : IsSimpleModule R f.range := IsSimpleModule.congr e.symm
  exact ⟨e.trans (h f.range).some⟩

private theorem isotypic_simple_quotient {R M N S : Type*} [Ring R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup S] [Module R S] [IsSimpleModule R N] [IsSemisimpleModule R M]
    (h : IsIsotypicOfType R M S) (f : M →ₗ[R] N) (hf : Function.Surjective f) :
    Nonempty (N ≃ₗ[R] S) := by
  obtain ⟨P, ⟨e⟩⟩ := IsSemisimpleModule.exists_submodule_linearEquiv_quotient f.ker
  let e' := e.trans (f.quotKerEquivOfSurjective hf)
  let : IsSimpleModule R P := IsSimpleModule.congr e'
  exact ⟨e'.symm.trans (h P).some⟩

private theorem finrank_of_moduleEquiv {ρ : Representation k G V} {σ : Representation k G W}
    (e : ρ.asModule ≃ₗ[k[G]] σ.asModule) : Module.finrank k V = Module.finrank k W := by
  calc
    _ = Module.finrank k ρ.asModule := ρ.asModuleEquiv.finrank_eq.symm
    _ = Module.finrank k σ.asModule := (e.restrictScalars k).finrank_eq
    _ = _ := σ.asModuleEquiv.finrank_eq

end CFSG.Quasithin.ChapterG.Section09.TwoComponents.CommonField.Comparison

namespace CFSG.Quasithin.ChapterG.Section09.TwoComponents.CommonField
open Comparison

universe u v

private theorem comparison_direct
    {G : Type u} [Group G] [Finite G]
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (L L₂ : Subgroup G)
    (C : ConstituentData ρ L) (D : ConstituentData ρ L₂)
    (hq : Quasiequivalent (ρ.comp L.subtype) (ρ.comp L₂.subtype)) :
    ConstituentComparison C D := by
  obtain ⟨a, f, hf⟩ := hq
  let τ : Representation (ZMod 2) L₂ C.space.toSubmodule :=
    C.space.toRepresentation.comp a.symm.toMonoidHom
  let : IsIrreducible τ := (irreducible_comp_surjective_iff
    a.symm.toMonoidHom a.symm.surjective C.space.toRepresentation).mpr C.irreducible
  let j : IntertwiningMap τ (ρ.comp L₂.subtype) := {
    toLinearMap := f.toLinearMap.comp C.space.toSubmodule.subtype
    isIntertwining' l := by
      apply LinearMap.ext
      intro x
      change f (ρ (a.symm l : L) x.val) = ρ (l : G) (f x.val)
      simpa only [MonoidHom.comp_apply, MulEquiv.apply_symm_apply, Subgroup.subtype_apply]
        using hf (a.symm l) x.val }
  have hj : Function.Injective j := f.injective.comp Subtype.val_injective
  let j' := IntertwiningMap.equivLinearMapAsModule _ _ j
  obtain ⟨e⟩ := isotypic_simple_submodule D.isotypic j' hj
  let e' := e.trans (submoduleEquiv (ρ.comp L₂.subtype) D.space).symm
  refine ⟨finrank_of_moduleEquiv e', ?_⟩
  calc
    Nat.card C.SchurField = Nat.card (Module.End (ZMod 2)[L₂] τ.asModule) :=
      (end_card_pullback C.space.toRepresentation a.symm).symm
    _ = Nat.card D.SchurField := Nat.card_congr e'.conjRingEquiv.toEquiv

private theorem comparison_dual
    {G : Type u} [Group G] [Finite G]
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (L L₂ : Subgroup G)
    (C : ConstituentData ρ L) (D : ConstituentData ρ L₂)
    (hq : Quasiequivalent (ρ.comp L.subtype) (Representation.dual (ρ.comp L₂.subtype))) :
    ConstituentComparison C D := by
  obtain ⟨a, f, hf⟩ := hq
  let τ : Representation (ZMod 2) L₂ C.space.toSubmodule :=
    C.space.toRepresentation.comp a.symm.toMonoidHom
  let σ : Representation (ZMod 2) L₂ V := ρ.comp L₂.subtype
  let : IsIrreducible τ := (irreducible_comp_surjective_iff
    a.symm.toMonoidHom a.symm.surjective C.space.toRepresentation).mpr C.irreducible
  let : IsIrreducible τ.dual := dual_irreducible τ
  let j : IntertwiningMap τ σ.dual := {
    toLinearMap := f.toLinearMap.comp C.space.toSubmodule.subtype
    isIntertwining' l := by
      apply LinearMap.ext
      intro x
      change f (ρ (a.symm l : L) x.val) = σ.dual l (f x.val)
      simpa only [MonoidHom.comp_apply, MulEquiv.apply_symm_apply, Subgroup.subtype_apply]
        using hf (a.symm l) x.val }
  have hj : Function.Injective j := f.injective.comp Subtype.val_injective
  let q : IntertwiningMap σ τ.dual := (dualMap j).comp (bidualEquiv σ).toIntertwiningMap
  have hq : Function.Surjective q :=
    (LinearMap.dualMap_surjective_of_injective hj).comp (Module.evalEquiv (ZMod 2) V).surjective
  let q' : σ.asModule →ₗ[(ZMod 2)[L₂]] τ.dual.asModule :=
    IntertwiningMap.equivLinearMapAsModule _ _ q
  have hq' : Function.Surjective q' := hq
  let : IsSemisimpleModule (ZMod 2)[L₂] σ.asModule := D.semisimple
  have he : Nonempty (τ.dual.asModule ≃ₗ[(ZMod 2)[L₂]] D.space.asSubmodule) :=
    isotypic_simple_quotient (M := σ.asModule) (N := τ.dual.asModule) D.isotypic q' hq'
  obtain ⟨e⟩ := he
  let e' := e.trans (submoduleEquiv σ D.space).symm
  refine ⟨?_, ?_⟩
  · exact Subspace.dual_finrank_eq.symm.trans (finrank_of_moduleEquiv e')
  · calc
      Nat.card C.SchurField = Nat.card (Module.End (ZMod 2)[L₂] τ.asModule) :=
        (end_card_pullback C.space.toRepresentation a.symm).symm
      _ = Nat.card (Module.End (ZMod 2)[L₂] τ.dual.asModule) := end_card_dual τ
      _ = Nat.card D.SchurField := Nat.card_congr e'.conjRingEquiv.toEquiv

/-- Actual constituents of quasiequivalent homogeneous restrictions have equal
binary dimensions and equal full Schur-ring orders, also when one restriction
is dualized. -/
theorem constituentComparison : ConstituentComparisonTheorem.{u,v} := by
  intro G _ _ V _ _ _ ρ L L₂ C D hq
  rcases hq with hq | hq
  · exact comparison_direct ρ L L₂ C D hq
  · exact comparison_dual ρ L L₂ C D hq

end CFSG.Quasithin.ChapterG.Section09.TwoComponents.CommonField
