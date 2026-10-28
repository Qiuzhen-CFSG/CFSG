module

public import Theory.Representation.Mathieu.M22James.MinimumDegree
public import Theory.Representation.Mathieu.M22James.Uniqueness
public import Theory.Mathieu.M22.TripleCover.Recognition

/-!
# James classification and transport for the triple Mathieu cover

The genuine matrix triple cover has a faithful irreducible binary module of
minimum dimension twelve, unique at that dimension. Pullback through an
actual group isomorphism preserves faithfulness and the invariant-subspace
lattice. The uniqueness equivalence then transports back as the same linear
map, intertwining every element of the original group.

The central scalar is transported along the same isomorphism: it has order
three, is central, satisfies X² + X + 1 in every faithful irreducible binary
module, and fixes only zero. Cover recognition also discharges the group
isomorphism premise for existence on every finite quasisimple group with
center of order three and actual central quotient M₂₂.

Source: James, *The modular characters of the Mathieu groups*, J. Algebra
27 (1973), 57–111, Lemma 8.3, as used in Aschbacher–Smith H.12.1(1) and its
proof, printed pp.393–394. The three imported theorem families prove the
concrete degree bound, degree-twelve uniqueness, and cover recognition.
-/

public section

namespace Sporadic.Mathieu.M22TripleCover

variable {L W : Type*} [Group L] [AddCommGroup W] [Module (ZMod 2) W]

/-- The minimum binary degree transported through an actual group isomorphism.
No finite-dimensionality premise is required. -/
theorem faithful_irreducible_finrank_ge_twelve_of_equiv
    (e : L ≃* M22TripleCover) (ρ : Representation (ZMod 2) L W)
    (hf : Function.Injective ρ) [ρ.IsIrreducible] :
    12 ≤ Module.finrank (ZMod 2) W := by
  let : Representation.IsIrreducible (ρ.comp e.symm.toMonoidHom) :=
    (Representation.irreducible_comp_surjective_iff e.symm.toMonoidHom
      e.symm.surjective ρ).mpr inferInstance
  exact faithful_irreducible_finrank_ge_twelve (ρ.comp e.symm.toMonoidHom)
    (hf.comp e.symm.injective)

/-- Every faithful irreducible module of binary dimension twelve is equivalent
to the transported concrete module, by an intertwining linear equivalence. -/
theorem equiv_representationOfEquiv_of_finrank_twelve
    (e : L ≃* M22TripleCover) (ρ : Representation (ZMod 2) L W)
    (hf : Function.Injective ρ) [ρ.IsIrreducible]
    (hd : Module.finrank (ZMod 2) W = 12) :
    Nonempty (Representation.Equiv ρ (representationOfEquiv e)) := by
  let : Representation.IsIrreducible (ρ.comp e.symm.toMonoidHom) :=
    (Representation.irreducible_comp_surjective_iff e.symm.toMonoidHom
      e.symm.surjective ρ).mpr inferInstance
  obtain ⟨f⟩ := Uniqueness.equiv_of_finrank_twelve (ρ.comp e.symm.toMonoidHom)
    (hf.comp e.symm.injective) hd
  refine ⟨Representation.Equiv.mk f.toLinearEquiv fun g => ?_⟩
  have h := f.isIntertwining' (e g)
  simpa only [representationOfEquiv, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.symm_apply_apply] using h

/-- The transported central scalar satisfies the polynomial defining F₄. -/
theorem scalar_quadratic_of_equiv
    (e : L ≃* M22TripleCover) (ρ : Representation (ZMod 2) L W)
    (hf : Function.Injective ρ) [ρ.IsIrreducible] :
    ρ (e.symm scalar) ^ 2 + ρ (e.symm scalar) + 1 = 0 := by
  let : Representation.IsIrreducible (ρ.comp e.symm.toMonoidHom) :=
    (Representation.irreducible_comp_surjective_iff e.symm.toMonoidHom
      e.symm.surjective ρ).mpr inferInstance
  exact Uniqueness.scalar_quadratic (ρ.comp e.symm.toMonoidHom)
    (hf.comp e.symm.injective)

/-- The transported central scalar has no nonzero fixed vector. -/
theorem scalar_fixed_iff_of_equiv
    (e : L ≃* M22TripleCover) (ρ : Representation (ZMod 2) L W)
    (hf : Function.Injective ρ) [ρ.IsIrreducible] (v : W) :
    ρ (e.symm scalar) v = v ↔ v = 0 := by
  let : Representation.IsIrreducible (ρ.comp e.symm.toMonoidHom) :=
    (Representation.irreducible_comp_surjective_iff e.symm.toMonoidHom
      e.symm.surjective ρ).mpr inferInstance
  exact Uniqueness.scalar_fixed_iff (ρ.comp e.symm.toMonoidHom)
    (hf.comp e.symm.injective) v

/-- The transported scalar belongs to the actual center. -/
theorem scalar_mem_center_of_equiv (e : L ≃* M22TripleCover) :
    e.symm scalar ∈ Subgroup.center L := by
  rw [Subgroup.mem_center_iff]
  intro g
  apply e.injective
  simpa only [map_mul, e.apply_symm_apply] using
    (Subgroup.mem_center_iff.mp scalar_mem_center) (e g)

/-- The transported scalar has order three. -/
theorem scalar_order_of_equiv (e : L ≃* M22TripleCover) :
    orderOf (e.symm scalar) = 3 :=
  (e.symm.orderOf_eq scalar).trans scalar_order

/-- Every genuine finite quasisimple triple cover of M₂₂ admits the constructed
faithful irreducible binary module of dimension twelve. -/
theorem exists_faithful_irreducible_twelve
    [Finite L] [Theory.GroupTheory.IsQuasisimple L]
    (hc : Nat.card (Subgroup.center L) = 3)
    (hq : Nonempty ((L ⧸ Subgroup.center L) ≃* Sporadic.Mathieu.M22)) :
    ∃ ρ : Representation (ZMod 2) L BinarySpace,
      Function.Injective ρ ∧ ρ.IsIrreducible ∧
      Module.finrank (ZMod 2) BinarySpace = 12 := by
  obtain ⟨e⟩ := nonempty_mulEquiv hc hq
  exact exists_faithful_irreducible_twelve_of_equiv e

end Sporadic.Mathieu.M22TripleCover
