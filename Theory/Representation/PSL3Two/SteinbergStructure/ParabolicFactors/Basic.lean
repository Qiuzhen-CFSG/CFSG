module

public import Theory.Representation.PSL3Two.SteinbergStructure.Duality
public import Theory.SpecificGroups.PSL3Two.Parabolics.CompatibleMarking
public import Mathlib.Order.Cover

/-!
# Chief sections and transport for the actual Steinberg representation

A chief series is a chain of invariant subspaces whose adjacent terms cover
one another. The corresponding quotients are simple modules for the actual
restricted group-algebra action. A section is central precisely when every
group displacement in its upper term lies in its lower term. An automorphism
intertwining equivalence transports both covers and this centrality test.

This supplies the series and transport interfaces used in Aschbacher–Smith
H.6.3(3), printed pp.387–388 (1 March 2004 manuscript).
-/

public section
open Matrix Representation
open BinaryLinearThree
namespace BinaryLinearThree.SteinbergStructure.ParabolicFactors
/-- The actual action on B/A is trivial: every displacement in B lies in A. -/
@[expose] def CentralSection (H : Subgroup Group) (A B : Subrepresentation (S.comp H.subtype)) : Prop :=
  ∀ g : H, ∀ v ∈ B, S g.val v - v ∈ A
/-- A chief series for the restricted action, with exactly three noncentral sections.
The covers are in the lattice of invariant subspaces, so every section is simple. -/
@[expose] def HasThreeNoncentralChiefFactors (H : Subgroup Group) : Prop :=
  ∃ F : Fin 6 → Subrepresentation (S.comp H.subtype),
    F 0 = ⊥ ∧ F 5 = ⊤ ∧
    (∀ i : Fin 5, F i.castSucc ⋖ F i.succ) ∧
    ∃ I : Finset (Fin 5), I.card = 3 ∧
      ∀ i, i ∈ I ↔ ¬ CentralSection H (F i.castSucc) (F i.succ)

private theorem aut_intertwines (a : MulAut Group) (g : Group) (v : Steinberg) :
    (autEquiv a).toLinearEquiv (S g v) = S (a g) ((autEquiv a).toLinearEquiv v) :=
  IntertwiningMap.isIntertwining S (S.comp a.toMonoidHom)
    (autEquiv a).toIntertwiningMap g v

private noncomputable def transport (a : MulAut Group) (H : Subgroup Group) :
    Subrepresentation (S.comp H.subtype) ≃o
      Subrepresentation (S.comp (H.map a.toMonoidHom).subtype) where
  toFun P := {
    toSubmodule := P.toSubmodule.map (autEquiv a).toLinearEquiv.toLinearMap
    apply_mem_toSubmodule := by
      rintro ⟨g,hg⟩ v ⟨w,hw,rfl⟩
      obtain ⟨h,hh,rfl⟩ := hg
      exact ⟨S h w, P.apply_mem_toSubmodule ⟨h,hh⟩ hw, aut_intertwines a h w⟩ }
  invFun Q := {
    toSubmodule := Q.toSubmodule.comap (autEquiv a).toLinearEquiv.toLinearMap
    apply_mem_toSubmodule := by
      intro g v hv
      change (autEquiv a).toLinearEquiv (S g.val v) ∈ Q
      rw [aut_intertwines]
      exact Q.apply_mem_toSubmodule ⟨a g.val, ⟨g.val,g.property,rfl⟩⟩ hv }
  left_inv P := Subrepresentation.toSubmodule_injective
    (Submodule.comap_map_eq_of_injective (autEquiv a).toLinearEquiv.injective P.toSubmodule)
  right_inv Q := Subrepresentation.toSubmodule_injective
    (Submodule.map_comap_eq_of_surjective (autEquiv a).toLinearEquiv.surjective Q.toSubmodule)
  map_rel_iff' := by
    intro P Q
    exact Submodule.map_le_map_iff_of_injective (autEquiv a).toLinearEquiv.injective _ _

set_option backward.isDefEq.respectTransparency false in
private theorem central_transport (a : MulAut Group) (H : Subgroup Group)
    (A B : Subrepresentation (S.comp H.subtype)) :
    CentralSection (H.map a.toMonoidHom) (transport a H A) (transport a H B) ↔
      CentralSection H A B := by
  constructor
  · intro hc g v hv
    have hm : (autEquiv a).toLinearEquiv v ∈ transport a H B := ⟨v,hv,rfl⟩
    have hh := hc ⟨a g.val,⟨g.val,g.property,rfl⟩⟩ _ hm
    obtain ⟨w,hw,he⟩ := hh
    have he' : (autEquiv a).toLinearEquiv w =
        (autEquiv a).toLinearEquiv (S g.val v - v) := by
      change (autEquiv a).toLinearEquiv w =
        S (a g.val) ((autEquiv a).toLinearEquiv v) - (autEquiv a).toLinearEquiv v at he
      rw [map_sub (autEquiv a).toLinearEquiv, aut_intertwines]
      exact he
    exact (autEquiv a).toLinearEquiv.injective he' ▸ hw
  · intro hc g v hv
    obtain ⟨h,hh,he⟩ := g.property
    obtain ⟨w,hw,rfl⟩ := hv
    refine ⟨S h w - w, hc ⟨h,hh⟩ w hw, ?_⟩
    change (autEquiv a).toLinearEquiv (S h w - w) =
      S g.val ((autEquiv a).toLinearEquiv w) - (autEquiv a).toLinearEquiv w
    change a h = g.val at he
    rw [map_sub (autEquiv a).toLinearEquiv, aut_intertwines, he]

theorem HasThreeNoncentralChiefFactors.map (H : Subgroup Group)
    (hH : HasThreeNoncentralChiefFactors H) (a : MulAut Group) :
    HasThreeNoncentralChiefFactors (H.map a.toMonoidHom) := by
  obtain ⟨F,h0,h5,hchief,I,hI,hn⟩ := hH
  refine ⟨fun i => transport a H (F i), ?_, ?_, ?_, I,hI, ?_⟩
  · change transport a H (F 0) = ⊥
    rw [h0]; exact (transport a H).map_bot
  · change transport a H (F 5) = ⊤
    rw [h5]; exact (transport a H).map_top
  · intro i
    exact (apply_covBy_apply_iff (transport a H)).mpr (hchief i)
  · intro i
    rw [central_transport]
    exact hn i
open scoped MonoidAlgebra
/-- Every cover in the invariant-subspace lattice gives the genuine simple
quotient module for the restricted group-algebra action. -/
theorem chiefFactor_simple (H : Subgroup Group)
    (A B : Subrepresentation (S.comp H.subtype)) (h : A ⋖ B) :
    IsSimpleModule (ZMod 2)[H]
      (B.asSubmodule ⧸ Submodule.comap B.asSubmodule.subtype A.asSubmodule) := by
  have hc : A.asSubmodule ⋖ B.asSubmodule :=
    (apply_covBy_apply_iff Subrepresentation.subrepresentationSubmoduleOrderIso).mpr h
  exact (covBy_iff_quot_is_simple hc.le).mp hc

end BinaryLinearThree.SteinbergStructure.ParabolicFactors
