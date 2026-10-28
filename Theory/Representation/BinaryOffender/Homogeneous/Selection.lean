module

public import Theory.Representation.BinaryOffender.Homogeneous.Selection.CentralAction

/-!
# Homogeneous simple central images

For a binary representation and a two-subgroup normalizing X, choose an
inertia-fixed copy of a prescribed simple X-type in its orbit span. The copy
is homogeneous in its own orbit span, and full commutator generation is
preserved by the actual equivariant equivalence. Homogeneity is equivalent
to inertia fixation, and distinct right conjugates form an independent
family whose sum is the entire orbit span.

This supplies the quotient geometry of Aschbacher–Smith, Lemma A.1.42(1–3),
printed p.32. The source's lift to Irr⁺ is supplied separately by
`commutatorLift_isIrrPlusWith`; no lifting or homogeneity premise is assumed
in the selection theorem here.
-/

@[expose] public section
noncomputable section
open scoped Classical DirectSum

namespace Representation.BinaryOffender.Homogeneous
variable {E W : Type*} [Group E] [AddCommGroup W] [Module (ZMod 2) W]
  {σ : Representation (ZMod 2) E W}

theorem SameModule.full_commutator {S A : Subrepresentation σ} (he : SameModule S A)
    (hfull : subspaceCommutator σ S.toSubmodule ⊤ = S.toSubmodule) :
    subspaceCommutator σ A.toSubmodule ⊤ = A.toSubmodule := by
  obtain ⟨e, he⟩ := he
  let f : S.toSubmodule →ₗ[ZMod 2] W := A.toSubmodule.subtype.comp e.toLinearMap
  have hf : (⊤ : Submodule (ZMod 2) S.toSubmodule).map f = A.toSubmodule := by
    rw [Submodule.map_top, LinearMap.range_comp, LinearMap.range_eq_top.mpr e.surjective,
      Submodule.map_top, Submodule.range_subtype]
  have hS : subspaceCommutator S.toRepresentation ⊤ ⊤ = ⊤ := by
    apply Submodule.map_injective_of_injective S.toSubmodule.subtype_injective
    have hh := subspaceCommutator_map_embedding σ S.toRepresentation (MonoidHom.id E)
      S.toSubmodule.subtype (fun _ _ => rfl) ⊤ ⊤
    simpa only [Subgroup.map_id, Submodule.map_top, Submodule.range_subtype, hfull] using hh.symm
  rw [← hf, subspaceCommutator_map_embedding σ S.toRepresentation (MonoidHom.id E) f
    (fun g v => (congrArg Subtype.val (he g v)).symm), Subgroup.map_id, hS]
end Representation.BinaryOffender.Homogeneous

namespace Representation.BinaryOffender.Homogeneous
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- Genuine homogeneous selection in the literal fixed-space quotient. -/
theorem exists_homogeneous_centralImage [FiniteDimensional (ZMod 2) V]
    {X T : Subgroup G} (hT : T ≤ Subgroup.normalizer X) (hP : IsPGroup 2 T)
    (S : Subrepresentation (fixedQuotientRepresentation ρ X))
    (hS : IsIrreducible S.toRepresentation)
    (hfull : subspaceCommutator (fixedQuotientRepresentation ρ X) S.toSubmodule ⊤ =
      S.toSubmodule) :
    ∃ A : Subrepresentation (fixedQuotientRepresentation ρ X),
      SameModule S A ∧ A.toSubmodule ≤ centralOrbitSpan ρ X T hT S.toSubmodule ∧
      IsIrreducible A.toRepresentation ∧
      subspaceCommutator (fixedQuotientRepresentation ρ X) A.toSubmodule ⊤ = A.toSubmodule ∧
      homogeneousPart A (centralOrbitSpan ρ X T hT A.toSubmodule) = A.toSubmodule := by
  let : Finite (V ⧸ fixedSpace ρ X) := Module.finite_of_finite (ZMod 2)
  obtain ⟨A, hle, he, hi, hh⟩ :=
    (centralTypeAction ρ X T hT).exists_homogeneous_copy hP S hS
  refine ⟨A, he, ?_, hi, he.full_commutator hfull, ?_⟩
  · exact (centralTypeAction_span ρ X T hT S) ▸ hle
  · rwa [centralTypeAction_span] at hh

/-- Inertia is the stabilizer of the actual X-module isomorphism class. -/
abbrev centralInertia (X T : Subgroup G) (hT : T ≤ Subgroup.normalizer X)
    (S : Subrepresentation (fixedQuotientRepresentation ρ X)) : Subgroup T :=
  (centralTypeAction ρ X T hT).inertia S

theorem mem_centralInertia_iff_right (X T : Subgroup G) (hT : T ≤ Subgroup.normalizer X)
    (S : Subrepresentation (fixedQuotientRepresentation ρ X)) (t : T) :
    t ∈ centralInertia ρ X T hT S ↔ SameModule S (centralRightConjugate ρ X T hT S t) := by
  change t ∈ (centralTypeAction ρ X T hT).inertia S ↔
    t⁻¹ ∈ (centralTypeAction ρ X T hT).inertia S
  exact inv_mem_iff.symm

/-- The source inertia criterion, using right conjugates throughout. -/
theorem central_homogeneous_iff_inertia_fixes (X T : Subgroup G)
    (hT : T ≤ Subgroup.normalizer X)
    (S : Subrepresentation (fixedQuotientRepresentation ρ X))
    (hS : IsIrreducible S.toRepresentation) :
    homogeneousPart S (centralOrbitSpan ρ X T hT S.toSubmodule) = S.toSubmodule ↔
      ∀ t ∈ centralInertia ρ X T hT S, centralRightConjugate ρ X T hT S t = S := by
  rw [← centralTypeAction_span]
  rw [(centralTypeAction ρ X T hT).homogeneous_iff_inertia_fixes S hS]
  constructor
  · intro h t ht
    exact h t⁻¹ ((centralInertia ρ X T hT S).inv_mem ht)
  · intro h t ht
    have he := h t⁻¹ ((centralInertia ρ X T hT S).inv_mem ht)
    simpa only [centralRightConjugate, inv_inv] using he

/-- The distinct source right-conjugate images, indexed without repetition. -/
def centralOrbit (X T : Subgroup G) (hT : T ≤ Subgroup.normalizer X)
    (S : Subrepresentation (fixedQuotientRepresentation ρ X)) :
    Set (Subrepresentation (fixedQuotientRepresentation ρ X)) :=
  Set.range (centralRightConjugate ρ X T hT S)

theorem centralOrbit_eq (X T : Subgroup G) (hT : T ≤ Subgroup.normalizer X)
    (S : Subrepresentation (fixedQuotientRepresentation ρ X)) :
    centralOrbit ρ X T hT S = (centralTypeAction ρ X T hT).orbit S := by
  ext A
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨t⁻¹, rfl⟩
  · rintro ⟨t, rfl⟩
    exact ⟨t⁻¹, by simp only [centralRightConjugate, inv_inv]⟩

/-- The entire conjugate family has supremum equal to the literal orbit span. -/
theorem centralOrbit_iSup (X T : Subgroup G) (hT : T ≤ Subgroup.normalizer X)
    (S : Subrepresentation (fixedQuotientRepresentation ρ X)) :
    (⨆ A : centralOrbit ρ X T hT S, A.val.toSubmodule) =
      centralOrbitSpan ρ X T hT S.toSubmodule := by
  rw [centralOrbit_eq, TypeAction.iSup_orbit, centralTypeAction_span]

/-- Distinct conjugates of a homogeneous simple central image are nonisomorphic. -/
theorem centralOrbit_not_sameModule (X T : Subgroup G) (hT : T ≤ Subgroup.normalizer X)
    (S : Subrepresentation (fixedQuotientRepresentation ρ X))
    (hS : IsIrreducible S.toRepresentation)
    (hh : homogeneousPart S (centralOrbitSpan ρ X T hT S.toSubmodule) = S.toSubmodule)
    (A B : centralOrbit ρ X T hT S) (hne : A ≠ B) : ¬ SameModule A.val B.val := by
  revert A B
  rw [centralOrbit_eq]
  intro A B hne
  apply (centralTypeAction ρ X T hT).orbit_not_sameModule S _ A B hne
  apply ((centralTypeAction ρ X T hT).homogeneous_iff_inertia_fixes S hS).mp
  rwa [centralTypeAction_span]

/-- Independence of the whole family, not merely disjointness of pairs. -/
theorem centralOrbit_independent (X T : Subgroup G) (hT : T ≤ Subgroup.normalizer X)
    (S : Subrepresentation (fixedQuotientRepresentation ρ X))
    (hS : IsIrreducible S.toRepresentation)
    (hh : homogeneousPart S (centralOrbitSpan ρ X T hT S.toSubmodule) = S.toSubmodule) :
    iSupIndep (fun A : centralOrbit ρ X T hT S => A.val.toSubmodule) := by
  rw [centralOrbit_eq]
  apply (centralTypeAction ρ X T hT).orbit_independent S hS
  rwa [centralTypeAction_span]

/-- The sum map from the direct sum of the distinct conjugates is injective. -/
theorem centralOrbit_directSum_injective (X T : Subgroup G) (hT : T ≤ Subgroup.normalizer X)
    (S : Subrepresentation (fixedQuotientRepresentation ρ X))
    (hS : IsIrreducible S.toRepresentation)
    (hh : homogeneousPart S (centralOrbitSpan ρ X T hT S.toSubmodule) = S.toSubmodule) :
    Function.Injective (DirectSum.coeLinearMap
      (fun A : centralOrbit ρ X T hT S => A.val.toSubmodule)) := by
  classical
  exact (centralOrbit_independent ρ X T hT S hS hh).dfinsupp_lsum_injective

/-- The direct sum of all distinct conjugates is the literal orbit span,
by the map adding the included vectors. -/
def centralOrbitDirectSumEquiv (X T : Subgroup G) (hT : T ≤ Subgroup.normalizer X)
    (S : Subrepresentation (fixedQuotientRepresentation ρ X))
    (hS : IsIrreducible S.toRepresentation)
    (hh : homogeneousPart S (centralOrbitSpan ρ X T hT S.toSubmodule) = S.toSubmodule) :
    (⨁ A : centralOrbit ρ X T hT S, A.val.toSubmodule) ≃ₗ[ZMod 2]
      centralOrbitSpan ρ X T hT S.toSubmodule :=
  (LinearEquiv.ofInjective _ (centralOrbit_directSum_injective ρ X T hT S hS hh)).trans
    (LinearEquiv.ofEq _ _ (DirectSum.range_coeLinearMap.trans (centralOrbit_iSup ρ X T hT S)))

/-- In a finite binary representation this is an actual finite family. -/
theorem centralOrbit_finite [FiniteDimensional (ZMod 2) V]
    (X T : Subgroup G) (hT : T ≤ Subgroup.normalizer X)
    (S : Subrepresentation (fixedQuotientRepresentation ρ X)) :
    Finite (centralOrbit ρ X T hT S) := by
  let : Finite (V ⧸ fixedSpace ρ X) := Module.finite_of_finite (ZMod 2)
  exact Finite.of_injective
    (fun A : centralOrbit ρ X T hT S => (A.val.toSubmodule : Set (V ⧸ fixedSpace ρ X)))
    (fun A B h => Subtype.ext (Subrepresentation.toSubmodule_injective (SetLike.coe_injective h)))

end Representation.BinaryOffender.Homogeneous
