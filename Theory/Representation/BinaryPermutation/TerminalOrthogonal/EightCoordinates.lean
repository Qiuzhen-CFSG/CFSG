module

public import Theory.Representation.BinaryPermutation
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8.DeletedEightAction

/-!
# Quadratic coordinates on the natural eight-point module

The quotient of the even code by its constant line maps isomorphically onto
`BinaryPermutation.natural (Fin 8)`. This comparison intertwines the literal
permutation actions. Transporting the existing half-weight form and its
hyperbolic basis identifies this natural section with the split six-space.
Thus the quadratic module, as well as the group action, is retained.

The half-weight construction and split basis are reused from the attributed
ATLAS port in `Order20160A8.DeletedEightAction`; its license and attribution
remain in those modules. Source: Aschbacher–Smith, combined manuscript of
1 March 2004, G.11.2(5), printed p.364, and 12.8.13(5), printed pp.855–856.
-/

public section

open Module
namespace BinaryPermutation.TerminalOrthogonal
namespace Eight
abbrev Code := Atlas.Order20160A8.DeletedEight.evenCode
abbrev Quotient := Atlas.Order20160A8.DeletedEight.W
private noncomputable def projection : Code →ₗ[ZMod 2] natural (Fin 8) :=
  (((constants (Fin 8)).mkQ).comp (core (Fin 8)).subtype).codRestrict
    (natural (Fin 8)) (fun v => ⟨v.val, v.property, rfl⟩)

private lemma projection_ker : projection.ker = Atlas.Order20160A8.DeletedEight.constants := by
  ext v
  change (⟨(constants (Fin 8)).mkQ v.val, _⟩ : natural (Fin 8)) = 0 ↔ _
  rw [Subtype.ext_iff]
  change (Submodule.Quotient.mk v.val : Deleted (Fin 8)) = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero]
  simp only [BinaryPermutation.constants, Atlas.Order20160A8.DeletedEight.constants,
    Submodule.mem_span_singleton]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, Subtype.ext hc⟩
  · rintro ⟨c, hc⟩
    exact ⟨c, congrArg Subtype.val hc⟩

private noncomputable def quotientMap : Quotient →ₗ[ZMod 2] natural (Fin 8) :=
  Atlas.Order20160A8.DeletedEight.constants.liftQ projection projection_ker.ge

private lemma quotientMap_bijective : Function.Bijective quotientMap := by
  constructor
  · apply (LinearMap.ker_eq_bot).mp
    apply le_bot_iff.mp
    intro v hv
    induction v using Submodule.Quotient.induction_on with
    | _ v =>
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      rw [← projection_ker]
      exact hv
  · intro v
    obtain ⟨w, hw, he⟩ := v.property
    exact ⟨Submodule.Quotient.mk (⟨w, hw⟩ : Code), Subtype.ext he⟩

/-- The even-code quotient is the actual natural permutation section. -/
noncomputable def naturalEquiv : Quotient ≃ₗ[ZMod 2] natural (Fin 8) :=
  LinearEquiv.ofBijective quotientMap quotientMap_bijective

/-- The comparison uses the original quotient maps on every representative. -/
lemma naturalEquiv_mk (v : Code) :
    (naturalEquiv (Submodule.Quotient.mk v) : Deleted (Fin 8)) =
      (constants (Fin 8)).mkQ v.val := by rfl

/-- The comparison intertwines every coordinate permutation. -/
lemma naturalEquiv_equivariant (g : Equiv.Perm (Fin 8)) (v : Quotient) :
    naturalEquiv (Atlas.Order20160A8.DeletedEight.quotientPerm g v) =
      naturalRepresentation (Fin 8) g (naturalEquiv v) := by
  induction v using Submodule.Quotient.induction_on with
  | _ v => rfl

/-- Half-weight on the natural six-dimensional module. -/
noncomputable def form : QuadraticForm (ZMod 2) (natural (Fin 8)) :=
  Atlas.Order20160A8.DeletedEight.quotientQuadratic.comp naturalEquiv.symm.toLinearMap

lemma form_naturalEquiv (v : Quotient) :
    form (naturalEquiv v) = Atlas.Order20160A8.DeletedEight.quotientQuadratic v := by
  change Atlas.Order20160A8.DeletedEight.quotientQuadratic
    (naturalEquiv.symm (naturalEquiv v)) = _
  rw [naturalEquiv.symm_apply_apply]

/-- The equivariant comparison also preserves the original quadratic form. -/
noncomputable def naturalIsometry :
    Atlas.Order20160A8.DeletedEight.quotientQuadratic.IsometryEquiv form where
  __ := naturalEquiv
  map_app' := form_naturalEquiv

/-- A genuine quadratic identification with the split six-space. -/
noncomputable def splitIsometry :
    (ClassicalOrthogonal.formD 3 (ZMod 2)).IsometryEquiv form where
  __ := Atlas.Order20160A8.DeletedEight.splitEquiv.trans naturalEquiv
  map_app' v := by
    change Atlas.Order20160A8.DeletedEight.quotientQuadratic
      (naturalEquiv.symm (naturalEquiv (Atlas.Order20160A8.DeletedEight.splitEquiv v))) = _
    rw [naturalEquiv.symm_apply_apply]
    exact Atlas.Order20160A8.DeletedEight.splitIsometry.map_app v

lemma form_invariant (g : Equiv.Perm (Fin 8)) (v : natural (Fin 8)) :
    form (naturalRepresentation (Fin 8) g v) = form v := by
  obtain ⟨v, rfl⟩ := naturalEquiv.surjective v
  rw [← naturalEquiv_equivariant]
  change Atlas.Order20160A8.DeletedEight.quotientQuadratic
    (naturalEquiv.symm (naturalEquiv _)) =
      Atlas.Order20160A8.DeletedEight.quotientQuadratic (naturalEquiv.symm (naturalEquiv _))
  simp only [naturalEquiv.symm_apply_apply]
  exact (Atlas.Order20160A8.DeletedEight.permutationIsometry g).map_app v

lemma finrank_natural : finrank (ZMod 2) (natural (Fin 8)) = 6 := by
  simpa using finrank_natural_even (Fin 8) (by decide)

end Eight
end BinaryPermutation.TerminalOrthogonal
