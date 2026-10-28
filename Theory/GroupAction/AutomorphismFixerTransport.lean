module

public import Theory.GroupAction.AutomorphismFixedResidualTransport
public import Mathlib.GroupTheory.GroupAction.FixingSubgroup

/-!
# Pointwise automorphism fixers under marked group equivalences

An equivalence of ambient groups transports the full automorphism group and
the pointwise fixer of an embedded subgroup. Compatibility with specified
automorphisms transports their embedded p-residuals by that same equivalence.
Thus the residual and its fixer retain their actual ambient markings; an
abstract isomorphism between residuals is not needed or substituted.

Application: the graph-field residual in Aschbacher–Smith, combined manuscript
of 1 March 2004, 15.3.38 and 16.4.9, printed pp.1137 and 1189.
-/

public section

namespace MulAut
open Subgroup
variable {G H : Type*} [Group G] [Group H]

/-- Transport of the full pointwise fixer by conjugation of automorphisms. -/
theorem map_fixingSubgroup_congr (e : G ≃* H) (P : Subgroup G) :
    (fixingSubgroup (MulAut G) (P : Set G)).map (MulAut.congr e).toMonoidHom =
      fixingSubgroup (MulAut H) (P.map e.toMonoidHom : Set H) := by
  ext b
  constructor
  · rintro ⟨a, ha, rfl⟩
    rw [mem_fixingSubgroup_iff]
    rintro _ ⟨x, hx, rfl⟩
    change e (a (e.symm (e x))) = e x
    rw [e.symm_apply_apply]
    exact congrArg e (ha ⟨x, hx⟩)
  · intro hb
    obtain ⟨a, rfl⟩ := (MulAut.congr e).surjective b
    refine ⟨a, ?_, rfl⟩
    change a ∈ fixingSubgroup (MulAut G) (P : Set G)
    rw [mem_fixingSubgroup_iff]
    intro x hx
    change a x = x
    apply e.injective
    have he := hb ⟨e x, ⟨x, hx, rfl⟩⟩
    change e (a (e.symm (e x))) = e x at he
    simpa only [e.symm_apply_apply] using he

/-- The full pointwise fixer has the same order under ambient transport. -/
theorem card_fixingSubgroup_map (e : G ≃* H) (P : Subgroup G) :
    Nat.card (fixingSubgroup (MulAut H) (P.map e.toMonoidHom : Set H)) =
      Nat.card (fixingSubgroup (MulAut G) (P : Set G)) := by
  rw [← map_fixingSubgroup_congr, card_map_of_injective (MulAut.congr e).injective]

/-- A marked ambient equivalence restricts to an equivalence of full fixers. -/
noncomputable def fixingSubgroupEquivOfMap (e : G ≃* H) (P : Subgroup G)
    (Q : Subgroup H) (hQ : P.map e.toMonoidHom = Q) :
    fixingSubgroup (MulAut G) (P : Set G) ≃*
      fixingSubgroup (MulAut H) (Q : Set H) :=
  ((MulAut.congr e).subgroupMap _).trans
    (MulEquiv.subgroupCongr ((map_fixingSubgroup_congr e P).trans (by rw [hQ])))

/-- Compatibility transports the embedded residual, including its ambient inclusion. -/
theorem map_embedded_fixedResidual_of_compatible (p : ℕ) (e : G ≃* H)
    (a : MulAut G) (b : MulAut H) (heq : ∀ x, e (a x) = b (e x)) :
    ((pResidual p a.fixedSubgroup).map a.fixedSubgroup.subtype).map e.toMonoidHom =
      (pResidual p b.fixedSubgroup).map b.fixedSubgroup.subtype := by
  let d := fixedSubgroupEquivOfCompatible e a b heq
  rw [← map_pResidual p d, map_map, map_map]
  have hd : e.toMonoidHom.comp a.fixedSubgroup.subtype =
      b.fixedSubgroup.subtype.comp d.toMonoidHom := by
    ext x
    exact (fixedSubgroupEquivOfCompatible_apply e a b heq x).symm
  rw [hd]

end MulAut
