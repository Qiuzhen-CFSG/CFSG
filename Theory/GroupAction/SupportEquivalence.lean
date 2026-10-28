module

public import Theory.GroupAction.Lemmas
public import Mathlib.Algebra.Group.Subgroup.Actions

/-!
# Action support under compatible group isomorphisms

Compatible isomorphisms of the actor group and acted-on group carry the
action commutator of a subgroup to the action commutator of its image.
The proof identifies their generators v⁻¹(a • v) in both directions.

This general transport controls the literal module supports in the
canonical-factor argument of Aschbacher--Smith, Lemma 3.2.13,
printed pp.584--585. No finiteness or faithfulness assumption is needed.
-/

public section

namespace ActionSupport
theorem equiv_commutatorAction
    {K L V W : Type*} [Group K] [Group L] [Group V] [Group W]
    [MulDistribMulAction K V] [MulDistribMulAction L W]
    (eK : K ≃* L) (eV : V ≃* W)
    (hcomp : ∀ k v, eV (k • v) = eK k • eV v)
    (A : Subgroup K) :
    (commutatorAction A V).map eV.toMonoidHom =
      commutatorAction (A.map eK.toMonoidHom) W := by
  rw [commutatorAction_eq_closure, commutatorAction_eq_closure, MonoidHom.map_closure]
  congr 1
  ext w
  constructor
  · rintro ⟨v, ⟨a, x, rfl⟩, rfl⟩
    refine ⟨⟨eK a, Subgroup.mem_map_of_mem eK.toMonoidHom a.property⟩, eV x, ?_⟩
    change eV (x⁻¹ * ((a : K) • x)) = (eV x)⁻¹ * (eK (a : K) • eV x)
    rw [map_mul, map_inv, hcomp]
  · rintro ⟨b, y, rfl⟩
    obtain ⟨a, ha, hba⟩ := b.property
    change eK a = (b : L) at hba
    refine ⟨(eV.symm y)⁻¹ * (a • eV.symm y), ⟨⟨a, ha⟩, eV.symm y, rfl⟩, ?_⟩
    change eV ((eV.symm y)⁻¹ * (a • eV.symm y)) = y⁻¹ * ((b : L) • y)
    rw [map_mul, map_inv, hcomp, eV.apply_symm_apply, hba]
end ActionSupport
