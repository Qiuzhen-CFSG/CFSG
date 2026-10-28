module

public import CFSG.Quasithin.ChapterG.Section09.TwoComponents.Geometry
public import Theory.Representation.EndFieldRep
public import Theory.Representation.SubrepresentationLattice
public import Mathlib.RingTheory.SimpleModule.Isotypic

/-!
# Faithful homogeneous constituents for the commuting component pair

For two commuting subgroups whose join acts irreducibly, the homogeneous
component of any simple constituent for either subgroup is the whole module.
Indeed, every endomorphism preserves this component, so the other subgroup
preserves it. Irreducibility of the join then forces equality with the ambient
module. Consequently each restriction is a finite direct sum of copies of any
chosen constituent. Faithfulness of the ambient action passes to each copy.

`ConstituentData` records actual subrepresentations, not representation-family
labels. Its Schur field is their full binary endomorphism ring; finiteness and
the field structure use the existing finite Schur--Wedderburn construction.
The alignment of the two fields and the tensor equivalence are separate
obligations, not consequences asserted by this module.

Source: Aschbacher--Smith, combined manuscript, G.9.3, printed p.356,
first paragraph. The argument here needs only commutation of the two actors.
-/

@[expose] public noncomputable section

open scoped MonoidAlgebra
open Representation
namespace CFSG.Quasithin.ChapterG.Section09.TwoComponents.CommonField

universe u v

variable {G : Type u} {V : Type v} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (L L₂ : Subgroup G)

private def commutingEnd (hc : ⁅L, L₂⁆ = ⊥) (j : L₂) :
    Module.End (ZMod 2)[L] (Representation.asModule (ρ.comp L.subtype)) :=
  Representation.IntertwiningMap.equivLinearMapAsModule (ρ.comp L.subtype) (ρ.comp L.subtype)
    { toLinearMap := ρ j
      isIntertwining' l := by
        ext v
        change ρ (j : G) (ρ (l : G) v) = ρ (l : G) (ρ (j : G) v)
        rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
        exact congrArg (fun g : G => ρ g v)
          (Subgroup.mem_centralizer_iff.mp
            (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc l.property) j j.property) }

private def joinSubrepresentation (hc : ⁅L, L₂⁆ = ⊥)
    (M : Submodule (ZMod 2)[L] (Representation.asModule (ρ.comp L.subtype)))
    (hM : M.IsFullyInvariant) : Subrepresentation (ρ.comp (L ⊔ L₂).subtype) where
  toSubmodule := (Subrepresentation.ofSubmodule' M).toSubmodule
  apply_mem_toSubmodule g v hv := by
    have hg : (g : G) ∈ (productMap hc).range := by
      rw [productMap_range hc]
      exact g.property
    obtain ⟨⟨l, j⟩, heq⟩ := hg
    have hj : ρ (j : G) v ∈ M := hM (commutingEnd ρ L L₂ hc j) hv
    have hl := (Subrepresentation.ofSubmodule' M).apply_mem_toSubmodule l hj
    change ρ (l : G) (ρ (j : G) v) ∈ M at hl
    change ρ (g : G) v ∈ M
    rw [← heq]
    change ρ ((l : G) * (j : G)) v ∈ M
    simpa only [map_mul, Module.End.mul_apply] using hl

/-- Every occurring simple type fills the restriction. -/
theorem isotypicComponent_eq_top (hc : ⁅L, L₂⁆ = ⊥)
    (hirr : Representation.IsIrreducible (ρ.comp (L ⊔ L₂).subtype))
    (S : Submodule (ZMod 2)[L] (Representation.asModule (ρ.comp L.subtype)))
    [IsSimpleModule (ZMod 2)[L] S] :
    isotypicComponent (ZMod 2)[L] (Representation.asModule (ρ.comp L.subtype)) S = ⊤ := by
  let M := isotypicComponent (ZMod 2)[L] (Representation.asModule (ρ.comp L.subtype)) S
  have hM : M.IsFullyInvariant := Submodule.IsFullyInvariant.isotypicComponent _ _ _
  let W := joinSubrepresentation ρ L L₂ hc M hM
  let : Representation.IsIrreducible (ρ.comp (L ⊔ L₂).subtype) := hirr
  have hWne : W ≠ ⊥ := by
    intro hw
    have hbot : M = ⊥ := by
      ext v
      have heq := congrArg Subrepresentation.toSubmodule hw
      exact (congrArg (fun N : Submodule (ZMod 2) V => v ∈ N) heq).to_iff
    exact (bot_lt_isotypicComponent S).ne' hbot
  have hWtop : W = ⊤ := (IsSimpleOrder.eq_bot_or_eq_top W).resolve_left hWne
  ext v
  have heq := congrArg Subrepresentation.toSubmodule hWtop
  exact (congrArg (fun N : Submodule (ZMod 2) V => v ∈ N) heq).to_iff

/-- An irreducible subrepresentation is a simple group-algebra submodule. -/
theorem constituent_simple (S : Subrepresentation (ρ.comp L.subtype))
    (hS : Representation.IsIrreducible S.toRepresentation) :
    IsSimpleModule (ZMod 2)[L] S.asSubmodule := by
  apply isSimpleModule_iff_isAtom.mpr
  exact (Subrepresentation.subrepresentationSubmoduleOrderIso.isAtom_iff S).mpr
    ((Subrepresentation.irreducible_iff_isAtom S).mp hS)

/-- Commutation and joint irreducibility imply semisimplicity of the restriction. -/
theorem restriction_semisimple (hc : ⁅L, L₂⁆ = ⊥)
    (hirr : Representation.IsIrreducible (ρ.comp (L ⊔ L₂).subtype))
    (S : Subrepresentation (ρ.comp L.subtype))
    (hS : Representation.IsIrreducible S.toRepresentation) :
    IsSemisimpleModule (ZMod 2)[L] (Representation.asModule (ρ.comp L.subtype)) := by
  let : IsSimpleModule (ZMod 2)[L] S.asSubmodule := constituent_simple ρ L S hS
  have heq := isotypicComponent_eq_top ρ L L₂ hc hirr S.asSubmodule
  let e := (LinearEquiv.ofEq _ _ heq).trans Submodule.topEquiv
  exact IsSemisimpleModule.congr e.symm

/-- The restriction is an actual finite direct sum of copies of the chosen constituent. -/
theorem constituent_decomposition [FiniteDimensional (ZMod 2) V]
    (hc : ⁅L, L₂⁆ = ⊥)
    (hirr : Representation.IsIrreducible (ρ.comp (L ⊔ L₂).subtype))
    (S : Subrepresentation (ρ.comp L.subtype))
    (hS : Representation.IsIrreducible S.toRepresentation) :
    ∃ n : ℕ, Nonempty ((Representation.asModule (ρ.comp L.subtype))
      ≃ₗ[(ZMod 2)[L]] (Fin n → S.asSubmodule)) := by
  let : IsSimpleModule (ZMod 2)[L] S.asSubmodule := constituent_simple ρ L S hS
  let : IsSemisimpleModule (ZMod 2)[L] (Representation.asModule (ρ.comp L.subtype)) :=
    restriction_semisimple ρ L L₂ hc hirr S hS
  let : Module.Finite (ZMod 2)[L] (Representation.asModule (ρ.comp L.subtype)) :=
    Module.Finite.of_restrictScalars_finite (ZMod 2) _ _
  exact (IsIsotypicOfType.of_isotypicComponent_eq_top
    (isotypicComponent_eq_top ρ L L₂ hc hirr S.asSubmodule)).linearEquiv_fun

set_option backward.isDefEq.respectTransparency false in
/-- A kernel on one constituent is a kernel on every copy, hence on the ambient module. -/
theorem constituent_faithful [FiniteDimensional (ZMod 2) V]
    (hc : ⁅L, L₂⁆ = ⊥)
    (hirr : Representation.IsIrreducible (ρ.comp (L ⊔ L₂).subtype))
    (hρ : Function.Injective ρ)
    (S : Subrepresentation (ρ.comp L.subtype))
    (hS : Representation.IsIrreducible S.toRepresentation) :
    Function.Injective S.toRepresentation := by
  obtain ⟨n, ⟨e⟩⟩ := constituent_decomposition ρ L L₂ hc hirr S hS
  intro a b hab
  have hs (x : S.asSubmodule) :
      MonoidAlgebra.single a (1 : ZMod 2) • x =
        MonoidAlgebra.single b (1 : ZMod 2) • x := by
    apply Subtype.ext
    apply (Representation.asModuleEquiv (ρ.comp L.subtype)).injective
    simp only [SetLike.val_smul, Representation.asModuleEquiv_map_smul,
      Representation.asAlgebraHom_single, one_smul]
    have hx := congrArg Subtype.val (congrArg (fun f : Module.End (ZMod 2) S.toSubmodule =>
      f ⟨x.val, x.property⟩) hab)
    change ρ (a : G) (Representation.asModuleEquiv (ρ.comp L.subtype) x.val) =
      ρ (b : G) (Representation.asModuleEquiv (ρ.comp L.subtype) x.val) at hx ⊢
    exact hx
  apply Subtype.ext
  apply hρ
  ext v
  have he : MonoidAlgebra.single a (1 : ZMod 2) •
      (Representation.asModuleEquiv (ρ.comp L.subtype)).symm v =
      MonoidAlgebra.single b (1 : ZMod 2) •
      (Representation.asModuleEquiv (ρ.comp L.subtype)).symm v := by
    apply e.injective
    simp only [map_smul]
    exact funext (fun i => hs (e _ i))
  have he' := congrArg (Representation.asModuleEquiv (ρ.comp L.subtype)) he
  simpa only [Representation.asModuleEquiv_map_smul, Representation.asAlgebraHom_single,
    LinearMap.smul_apply, one_smul, LinearEquiv.apply_symm_apply,
    MonoidHom.comp_apply, Subgroup.subtype_apply] using he'

/-- A genuine irreducible constituent, with its faithful action and full homogeneous component. -/
structure ConstituentData where
  space : Subrepresentation (ρ.comp L.subtype)
  irreducible : Representation.IsIrreducible space.toRepresentation
  faithful : Function.Injective space.toRepresentation
  homogeneous : isotypicComponent (ZMod 2)[L]
    (Representation.asModule (ρ.comp L.subtype)) space.asSubmodule = ⊤

/-- Choose a faithful irreducible constituent with full homogeneous component. -/
theorem exists_constituentData [FiniteDimensional (ZMod 2) V]
    (hc : ⁅L, L₂⁆ = ⊥)
    (hirr : Representation.IsIrreducible (ρ.comp (L ⊔ L₂).subtype))
    (hρ : Function.Injective ρ) : Nonempty (ConstituentData ρ L) := by
  let : Representation.IsIrreducible (ρ.comp (L ⊔ L₂).subtype) := hirr
  let : Nontrivial V := Subrepresentation.irreducible_module_nontrivial
    (ρ.comp (L ⊔ L₂).subtype)
  obtain ⟨S, hS⟩ := Subrepresentation.irreducible_subrepresentation_of_finite_dimensional
    (ρ.comp L.subtype)
  let : IsSimpleModule (ZMod 2)[L] S.asSubmodule := constituent_simple ρ L S hS
  exact ⟨⟨S, hS, constituent_faithful ρ L L₂ hc hirr hρ S hS,
    isotypicComponent_eq_top ρ L L₂ hc hirr S.asSubmodule⟩⟩

namespace ConstituentData

variable {ρ L} (C : ConstituentData ρ L)

/-- The full binary endomorphism ring of the actual constituent. -/
abbrev SchurField : Type v := Module.End (ZMod 2)[L] C.space.toRepresentation.asModule

instance schurField_finite [FiniteDimensional (ZMod 2) V] : Finite C.SchurField :=
  Representation.endField_finite C.space.toRepresentation

noncomputable instance schurField_field [FiniteDimensional (ZMod 2) V] : Field C.SchurField := by
  let : Representation.IsIrreducible C.space.toRepresentation := C.irreducible
  exact Representation.endField_field C.space.toRepresentation

instance schurField_finiteDimensional [FiniteDimensional (ZMod 2) V] :
    FiniteDimensional (ZMod 2) C.SchurField :=
  Module.finite_iff_finite.mpr inferInstance

theorem simple : IsSimpleModule (ZMod 2)[L] C.space.asSubmodule :=
  constituent_simple ρ L C.space C.irreducible

include C in
theorem semisimple :
    IsSemisimpleModule (ZMod 2)[L] (Representation.asModule (ρ.comp L.subtype)) := by
  let : IsSimpleModule (ZMod 2)[L] C.space.asSubmodule := C.simple
  let e := (LinearEquiv.ofEq _ _ C.homogeneous).trans Submodule.topEquiv
  exact IsSemisimpleModule.congr e.symm

theorem isotypic : IsIsotypicOfType (ZMod 2)[L]
    (Representation.asModule (ρ.comp L.subtype)) C.space.asSubmodule := by
  let : IsSimpleModule (ZMod 2)[L] C.space.asSubmodule := C.simple
  exact IsIsotypicOfType.of_isotypicComponent_eq_top C.homogeneous

theorem decomposition [FiniteDimensional (ZMod 2) V] :
    ∃ n : ℕ, Nonempty ((Representation.asModule (ρ.comp L.subtype))
      ≃ₗ[(ZMod 2)[L]] (Fin n → C.space.asSubmodule)) := by
  let : IsSemisimpleModule (ZMod 2)[L] (Representation.asModule (ρ.comp L.subtype)) :=
    C.semisimple
  let : Module.Finite (ZMod 2)[L] (Representation.asModule (ρ.comp L.subtype)) :=
    Module.Finite.of_restrictScalars_finite (ZMod 2) _ _
  exact C.isotypic.linearEquiv_fun

end ConstituentData

end CFSG.Quasithin.ChapterG.Section09.TwoComponents.CommonField
