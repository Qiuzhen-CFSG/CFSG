module

public import Theory.GroupAction.InnerInvolutionGeometry
public import Mathlib.GroupTheory.GroupAction.FixingSubgroup

/-!
# Pointwise fixers of embedded fixed residuals under isomorphisms

Conjugating an automorphism by a group isomorphism carries its embedded
p-residual to the embedded p-residual of the conjugate action. Conjugation
on the full automorphism group then identifies the two pointwise fixers.
Thus a calculation in standard coordinates applies to the actual marked
subgroup, without replacing that subgroup by an abstract isomorphism type.

This is the transport used in the centralizer inspection in
Aschbacher–Smith, *The Classification of Quasithin Groups*, 16.4.9(1),
printed p.1189 of the combined manuscript of 1 March 2004.
-/

public section

open Subgroup
namespace MulAut
variable {G H : Type*} [Group G] [Group H]

/-- Transport preserves the embedding of the fixed p-residual. -/
theorem map_embeddedFixedResidual [Finite G] (p : ℕ) (e : G ≃* H) (a : MulAut G) :
    (embeddedFixedResidual p a).map e.toMonoidHom =
      embeddedFixedResidual p (MulAut.congr e a) := by
  have hm : a.fixedSubgroup.map e.toMonoidHom = (MulAut.congr e a).fixedSubgroup := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [mem_fixedSubgroup]
      change e (a (e.symm (e x))) = e x
      rw [e.symm_apply_apply]
      exact congrArg e ((mem_fixedSubgroup a x).mp hx)
    · intro hy
      refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
      apply (mem_fixedSubgroup a _).mpr
      apply e.injective
      have hh := (mem_fixedSubgroup (MulAut.congr e a) y).mp hy
      change e (a (e.symm y)) = y at hh
      simpa only [e.apply_symm_apply] using hh
  rw [embeddedFixedResidual, map_embedded_pResidual, hm]
  rfl

/-- The full automorphism fixer transports with the marked subgroup. -/
theorem map_fixer (e : G ≃* H) (D : Subgroup G) :
    (fixingSubgroup (MulAut G) (D : Set G)).map (MulAut.congr e).toMonoidHom =
      fixingSubgroup (MulAut H) (D.map e.toMonoidHom : Set H) := by
  ext b
  constructor
  · rintro ⟨a, ha, rfl⟩
    apply (mem_fixingSubgroup_iff _).mpr
    rintro _ ⟨x, hx, rfl⟩
    change e (a (e.symm (e x))) = e x
    rw [e.symm_apply_apply]
    exact congrArg e ((mem_fixingSubgroup_iff _).mp ha x hx)
  · intro hb
    obtain ⟨a, rfl⟩ := (MulAut.congr e).surjective b
    refine ⟨a, ?_, rfl⟩
    apply (mem_fixingSubgroup_iff _).mpr
    intro x hx
    change a x = x
    apply e.injective
    have hh := (mem_fixingSubgroup_iff _).mp hb (e x) ⟨x, hx, rfl⟩
    change e (a (e.symm (e x))) = e x at hh
    simpa only [e.symm_apply_apply] using hh

/-- An isomorphism of the full pointwise fixers, induced by conjugation. -/
noncomputable def fixerEquivMap (e : G ≃* H) (D : Subgroup G) :
    fixingSubgroup (MulAut G) (D : Set G) ≃*
      fixingSubgroup (MulAut H) (D.map e.toMonoidHom : Set H) :=
  ((MulAut.congr e).subgroupMap _).trans (MulEquiv.subgroupCongr (map_fixer e D))

/-- Changing coordinates preserves the full fixer of the embedded residual. -/
noncomputable def embeddedFixedResidualFixerEquiv [Finite G] (p : ℕ) (e : G ≃* H)
    (a : MulAut G) :
    fixingSubgroup (MulAut G) (embeddedFixedResidual p a : Set G) ≃*
      fixingSubgroup (MulAut H)
        (embeddedFixedResidual p (MulAut.congr e a) : Set H) :=
  (fixerEquivMap e _).trans (MulEquiv.subgroupCongr
    (congrArg (fun D : Subgroup H => fixingSubgroup (MulAut H) (D : Set H))
      (map_embeddedFixedResidual p e a)))

/-- In particular, the pointwise-fixer cardinality is independent of coordinates. -/
theorem card_embeddedFixedResidual_fixer_congr [Finite G] (p : ℕ) (e : G ≃* H) (a : MulAut G) :
    Nat.card (fixingSubgroup (MulAut H)
      (embeddedFixedResidual p (MulAut.congr e a) : Set H)) =
    Nat.card (fixingSubgroup (MulAut G) (embeddedFixedResidual p a : Set G)) :=
  (Nat.card_congr (embeddedFixedResidualFixerEquiv p e a).toEquiv).symm

end MulAut
