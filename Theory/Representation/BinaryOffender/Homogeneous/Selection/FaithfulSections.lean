module
public import Theory.Representation.BinaryOffender.Homogeneous.Selection.TwoCopies
public import Theory.Representation.BinaryOffender.FaithfulInvariantSection
public import Theory.GroupTheory.SolvableOuterQuotient

/-!
# Faithful chief-section transports

This module packages the two transports used in the D.3.9(1) local-type
argument.  Isotypy and semisimplicity provide two simple sections with the
same local type; a linear equivalence over the group algebra is upgraded to a
representation equivalence.  A faithful normal subgroup then forces a
starred elementary actor to act faithfully on the selected section.

Source: Aschbacher--Smith D.3.9(1), printed pp.199--200.
-/

@[expose] public noncomputable section
open scoped MonoidAlgebra
open Subgroup Representation
namespace Representation.BinaryOffender.Homogeneous

variable {G V W : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [AddCommGroup W] [Module (ZMod 2) W]

noncomputable def equiv_of_asSubmodule_equiv
    (ρ : Representation (ZMod 2) G V) (σ : Representation (ZMod 2) G W)
    (U : Subrepresentation ρ) (S : Subrepresentation σ)
    (f : U.asSubmodule ≃ₗ[(ZMod 2)[G]] S.asSubmodule) :
    U.toRepresentation.Equiv S.toRepresentation := by
  let e : U.toSubmodule ≃ₗ[ZMod 2] S.toSubmodule := {
    toFun v := ⟨(f ⟨v.val,v.property⟩).val,(f ⟨v.val,v.property⟩).property⟩
    invFun v := ⟨(f.symm ⟨v.val,v.property⟩).val,(f.symm ⟨v.val,v.property⟩).property⟩
    left_inv v := by apply Subtype.ext; exact congrArg Subtype.val (f.symm_apply_apply ⟨v.val,v.property⟩)
    right_inv v := by apply Subtype.ext; exact congrArg Subtype.val (f.apply_symm_apply ⟨v.val,v.property⟩)
    map_add' x y := by apply Subtype.ext; exact congrArg Subtype.val (f.map_add ⟨x.val,x.property⟩ ⟨y.val,y.property⟩)
    map_smul' r v := by
      apply Subtype.ext
      exact congrArg Subtype.val ((f.restrictScalars (ZMod 2)).map_smul r ⟨v.val,v.property⟩) }
  refine Representation.Equiv.mk e ?_
  intro g
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  have he := f.map_smul (MonoidAlgebra.single g (1 : ZMod 2))
    (show U.asSubmodule from ⟨v.val,v.property⟩)
  have hs : (MonoidAlgebra.single g (1 : ZMod 2) •
      (show U.asSubmodule from ⟨v.val,v.property⟩)) =
      (show U.asSubmodule from ⟨ρ g v.val,U.apply_mem_toSubmodule g v.property⟩) := by
    apply Subtype.ext
    exact (ρ.asModuleEquiv_symm_map_rho g v.val).symm
  rw [hs] at he
  change σ.asModuleEquiv (f ⟨ρ g v.val,_⟩).val =
    σ g (σ.asModuleEquiv (f ⟨v.val,v.property⟩).val)
  exact (congrArg (fun z : S.asSubmodule => σ.asModuleEquiv z.val) he).trans
    (by
      simpa only [Submodule.coe_smul, Representation.asAlgebraHom_single, one_smul] using
        (σ.asModuleEquiv_map_smul (MonoidAlgebra.single g (1 : ZMod 2))
          (f ⟨v.val,v.property⟩).val))

theorem faithful_on_actor_of_faithful_normal
    (N A H : Subgroup G) [N.Normal] (hNH : N ≤ H) (_hAH : A ≤ H)
    (σ : Representation (ZMod 2) H W)
    (hN : Function.Injective (σ.comp (inclusion hNH)))
    (hconj : Function.Injective ((MulAut.conjNormal : G →* MulAut N).comp A.subtype)) :
    ∀ a ∈ A.subgroupOf H, (∀ v, σ a v = v) → a = 1 := by
  intro a ha hf
  have hB : Function.Injective (σ.comp (N.subgroupOf H).subtype) :=
    hN.comp (subgroupOfEquivOfLe hNH).injective
  have hc : a ∈ centralizer (N.subgroupOf H : Set H) :=
    BinaryOffender.centralizes_of_fixes_faithful_section σ (N.subgroupOf H) ⊤
      (by intro n hn v; simp)
      (by
        intro n hn hh
        have he : (σ.comp (N.subgroupOf H).subtype) ⟨n,hn⟩ =
            (σ.comp (N.subgroupOf H).subtype) 1 := by
          ext v
          simpa only [MonoidHom.comp_apply, Subgroup.coe_subtype, Subgroup.coe_mk,
            Subgroup.coe_one, map_one, Module.End.one_apply]
            using hh v Submodule.mem_top
        exact congrArg Subtype.val (hB he))
      (le_normalizer_of_normal (mem_top a)) (fun v _ => hf v)
  have hcG : (a : G) ∈ centralizer (N : Set G) := by
    intro n hn
    exact congrArg Subtype.val (hc ⟨n,hNH hn⟩ hn)
  have he : (MulAut.conjNormal : G →* MulAut N) (a : G) = 1 := by
    change (a : G) ∈ (MulAut.conjNormal : G →* MulAut N).ker
    rwa [MulAut.conjNormal_ker_eq_centralizer]
  have heA := hconj (show ((MulAut.conjNormal : G →* MulAut N).comp A.subtype)
      ⟨(a : G),ha⟩ = ((MulAut.conjNormal : G →* MulAut N).comp A.subtype) 1 from
    he.trans (map_one _).symm)
  have heAG : (a : G) = 1 := congrArg (fun x : A => (x : G)) heA
  apply Subtype.ext
  exact heAG

theorem exists_two_restricted_sections_of_isotypic [Finite V] [Nontrivial V]
    (ρ : Representation (ZMod 2) G V) (N : Subgroup G) [N.Normal]
    [IsSemisimpleModule (ZMod 2)[N] (Representation.asModule (ρ.comp N.subtype))]
    (S : Subrepresentation (ρ.comp N.subtype))
    (htype : IsIsotypicOfType (ZMod 2)[N] (Representation.asModule (ρ.comp N.subtype)) S.asSubmodule)
    (A : Subgroup G) (hA : IsPGroup 2 A)
    (hred : ¬ Representation.IsIrreducible (ρ.comp N.subtype)) :
    let H := N ⊔ A
    let B := N.subgroupOf H
    let e := subgroupOfEquivOfLe (show N ≤ H from le_sup_left)
    ∃ (U : Subrepresentation (ρ.comp H.subtype))
      (W : Subrepresentation U.quotientRepresentation),
      Representation.IsIrreducible (U.toRepresentation.comp B.subtype) ∧
      Representation.IsIrreducible (W.toRepresentation.comp B.subtype) ∧
      Nonempty ((U.compActors B.subtype).asSubmodule ≃ₗ[(ZMod 2)[B]]
        (S.compActors e.toMonoidHom).asSubmodule) ∧
      Nonempty ((W.compActors B.subtype).asSubmodule ≃ₗ[(ZMod 2)[B]]
        (S.compActors e.toMonoidHom).asSubmodule) := by
  dsimp only
  let H := N ⊔ A
  let B := N.subgroupOf H
  let P := A.subgroupOf H
  let e := subgroupOfEquivOfLe (show N ≤ H from le_sup_left)
  let σ := ρ.comp H.subtype
  let S' := S.compActors e.toMonoidHom
  have htype' : IsIsotypicOfType (ZMod 2)[B] (Representation.asModule (σ.comp B.subtype)) S'.asSubmodule :=
    isotypic_comp_equiv (ρ.comp N.subtype) e S htype
  let : IsSemisimpleModule (ZMod 2)[B] (Representation.asModule (σ.comp B.subtype)) :=
    comp_semisimple_of_surjective (ρ.comp N.subtype) e.toMonoidHom e.surjective
  have hred' : ¬ Representation.IsIrreducible (σ.comp B.subtype) := by
    intro hh
    apply hred
    exact (irreducible_comp_surjective_iff e.toMonoidHom e.surjective (ρ.comp N.subtype)).mp hh
  have hP : IsPGroup 2 P := hA.of_injective
    (subgroupOfEquivOfLe (show A ≤ H from le_sup_right)).toMonoidHom
    (subgroupOfEquivOfLe (show A ≤ H from le_sup_right)).injective
  exact exists_two_simple_sections_of_isotypic σ B htype' P hP
    (codisjoint_subgroupOf_sup N A).eq_top hred'

end Representation.BinaryOffender.Homogeneous
