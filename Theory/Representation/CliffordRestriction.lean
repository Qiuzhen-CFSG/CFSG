module
public import Theory.Representation.NormalConstituentDisplacement.FixedLine
public import Mathlib.RepresentationTheory.Semisimple
public import Theory.Representation.BinaryOffender.Homogeneous.Selection.Geometry

/-!
# Clifford restriction through a normal chain

A semisimple binary representation restricts semisimply to a normal subgroup:
apply the proved irreducible Clifford restriction to each simple summand, then
use that a sum of semisimple submodules is semisimple. Surjective changes of
actors preserve the invariant-subspace lattice. These facts iterate Clifford
restriction through the two normal steps used for an exchanged component.

Source: Isaacs, *Character Theory of Finite Groups*, Theorem 6.5;
Aschbacher–Smith D.3.6–7, pp.196–197.
-/

@[expose] public noncomputable section
open scoped MonoidAlgebra
open Subgroup Representation
namespace Representation
variable {D V : Type*} [Group D]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V)

private def restrictSubrepresentation (H : Subgroup D) (S : Subrepresentation ρ) :
    Subrepresentation (ρ.comp H.subtype) where
  toSubmodule := S.toSubmodule
  apply_mem_toSubmodule h _ hv := S.apply_mem_toSubmodule h hv

theorem normal_restriction_semisimple (H : Subgroup D) [H.Normal]
    [IsSemisimpleModule (ZMod 2)[D] ρ.asModule] :
    IsSemisimpleModule (ZMod 2)[H] (Representation.asModule (ρ.comp H.subtype)) := by
  let e := Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := ρ)
  let τ : Representation (ZMod 2) H V := ρ.comp H.subtype
  let p (S : Subrepresentation ρ) := (restrictSubrepresentation ρ H S).asSubmodule
  apply isSemisimpleModule_of_isSemisimpleModule_submodule
    (s := {S : Subrepresentation ρ | IsIrreducible S.toRepresentation}) (p := p)
  · intro S hS
    let := NormalConstituentDisplacement.restriction_semisimple S.toRepresentation hS H
    let f : (S.toRepresentation.comp H.subtype) →ₗ τ := {
      toLinearMap := S.toSubmodule.subtype
      isIntertwining' h := by ext x; rfl }
    let f' := RepMap.equivLinearMapAsModule _ _ f
    have hr : LinearMap.range f' = p S := by
      ext x
      constructor
      · rintro ⟨v,rfl⟩
        exact v.property
      · intro hx
        exact ⟨⟨x,hx⟩,rfl⟩
    rw [← hr]
    exact IsSemisimpleModule.range f'
  · have htop : (⨆ S : Subrepresentation ρ, ⨆ (_ : IsIrreducible S.toRepresentation), S) = ⊤ := by
      apply e.injective
      rw [e.map_iSup,e.map_top]
      simp_rw [e.map_iSup]
      have hs := IsSemisimpleModule.sSup_simples_eq_top (ZMod 2)[D] ρ.asModule
      apply top_unique
      rw [← hs]
      apply sSup_le
      intro N hN
      let S := e.symm N
      have hS : IsIrreducible S.toRepresentation := by
        apply (Subrepresentation.irreducible_iff_isAtom S).mpr
        exact (e.isAtom_iff S).mp (by simpa [S] using isSimpleModule_iff_isAtom.mp hN)
      exact le_iSup_of_le S (le_iSup_of_le hS (by simp [S]))
    apply top_unique
    intro v _
    let Q : Submodule (ZMod 2)[H] (Representation.asModule τ) :=
      ⨆ S : Subrepresentation ρ, ⨆ (_ : IsIrreducible S.toRepresentation), p S
    have hv : τ.asModuleEquiv v ∈
        (⨆ S : Subrepresentation ρ, ⨆ (_ : IsIrreducible S.toRepresentation), S).toSubmodule :=
      htop.symm ▸ Submodule.mem_top
    rw [Representation.BinaryOffender.Homogeneous.toSubmodule_iSup] at hv
    simp_rw [Representation.BinaryOffender.Homogeneous.toSubmodule_iSup] at hv
    have hx := Submodule.iSup_induction _
      (motive := fun w : V => τ.asModuleEquiv.symm w ∈ Q) hv
      (fun S w hw => Submodule.iSup_induction _
        (motive := fun w : V => τ.asModuleEquiv.symm w ∈ Q) hw
        (fun hS w hw => (show p S ≤ Q from le_iSup_of_le S (le_iSup_of_le hS le_rfl)) hw)
        (by simpa only [map_zero] using Q.zero_mem)
        (fun x y hx hy => by simpa only [map_add] using Q.add_mem hx hy))
      (by simpa only [map_zero] using Q.zero_mem)
      (fun x y hx hy => by simpa only [map_add] using Q.add_mem hx hy)
    simpa only [LinearEquiv.symm_apply_apply, Q, τ, Set.mem_ofPred_eq] using hx

omit [FiniteDimensional (ZMod 2) V] in
/-- A surjective change of actors preserves the lattice of invariant subspaces. -/
theorem comp_semisimple_of_surjective {E : Type*} [Group E] (f : E →* D)
    (hf : Function.Surjective f) [IsSemisimpleModule (ZMod 2)[D] ρ.asModule] :
    IsSemisimpleModule (ZMod 2)[E] (Representation.asModule (ρ.comp f)) := by
  let e : Subrepresentation ρ ≃o Subrepresentation (ρ.comp f) := {
    toFun S := ⟨S.toSubmodule, fun x _ hv => S.apply_mem_toSubmodule (f x) hv⟩
    invFun S := ⟨S.toSubmodule, fun x _ hv => by
      obtain ⟨y,rfl⟩ := hf x
      exact S.apply_mem_toSubmodule y hv⟩
    left_inv _ := rfl
    right_inv _ := rfl
    map_rel_iff' := Iff.rfl }
  apply (isSemisimpleRepresentation_iff_isSemisimpleModule_asModule (ρ.comp f)).mp
  exact e.complementedLattice_iff.mp
    ((isSemisimpleRepresentation_iff_isSemisimpleModule_asModule ρ).mpr inferInstance)

/-- The two normal steps in the exchanged-component Clifford restriction. -/
theorem irreducible_restriction_semisimple_of_normal_chain
    (hi : IsIrreducible ρ) (K N : Subgroup D) [N.Normal]
    (hKN : K ≤ N) (hn : N ≤ normalizer (K : Set D)) :
    IsSemisimpleModule (ZMod 2)[K] (Representation.asModule (ρ.comp K.subtype)) := by
  let : (K.subgroupOf N).Normal := (normal_subgroupOf_iff_le_normalizer hKN).mpr hn
  let : IsSemisimpleModule (ZMod 2)[N] (Representation.asModule (ρ.comp N.subtype)) :=
    NormalConstituentDisplacement.restriction_semisimple ρ hi N
  let τ := (ρ.comp N.subtype).comp (K.subgroupOf N).subtype
  let : IsSemisimpleModule (ZMod 2)[K.subgroupOf N] (Representation.asModule τ) :=
    normal_restriction_semisimple (ρ.comp N.subtype) (K.subgroupOf N)
  let e := (subgroupOfEquivOfLe hKN).symm
  exact comp_semisimple_of_surjective τ e.toMonoidHom e.surjective

end Representation
