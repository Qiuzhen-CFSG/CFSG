module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Mathieu.M22.SourceDefs
public import Theory.Mathieu.M22.BinaryCovers
public import Theory.Representation.Mathieu.SmallModules.M22Recognition
public import Theory.Representation.Mathieu.M22James.Classification
public import Theory.Representation.Mathieu.M22James.Unitary.Action

/-!
# Component recognition for the source M₂₂ branch

Central Sylow transfer first reduces all faithful binary covers to the simple
and triple covers. Small-degree recognition identifies the simple action with
the literal code hyperplane or cocode quotient; James uniqueness identifies
the triple action. Its given intertwiner then transports the native unitary
coordinates and the order-three scalar into the caller's module.

These are conditional source reductions: the bound dim V ≤ 12 is explicit.
They do not derive that bound from the cubic ratio, and do not classify the
extension from the component to the ambient actor. The final source assembly
must discharge those two independent obligations.

Source: Aschbacher–Smith, Chapter K, printed pp.451 and 457, and H.12,
printed pp.393–394; Guralnick–Malle I, Proposition 5.1 and Table 6.7.
See `Source.md` for the inspected primary references and their conventions.
-/

public section
open Subgroup Theory.GroupTheory Representation
open _root_.Sporadic.Mathieu
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.M22Source

variable {L V : Type*} [Group L] [Finite L] [IsQuasisimple L]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (σ : Representation (ZMod 2) L V) [σ.IsIrreducible]

/-- A degree bound of twelve suffices to identify every faithful irreducible
binary action of an arbitrary quasisimple M₂₂ cover. -/
theorem componentModels_of_degree_le_twelve (hf : Function.Injective σ)
    (eQ : (L ⧸ center L) ≃* M22)
    (hd : Module.finrank (ZMod 2) V ≤ 12) : ComponentModels σ := by
  rcases M22BinaryCovers.simple_or_triple_of_binary_irreducible σ hf eQ with hs | ht
  · obtain ⟨e⟩ := hs
    let τ := σ.comp e.symm.toMonoidHom
    let : Representation.IsIrreducible τ :=
      (irreducible_comp_surjective_iff _ e.symm.surjective σ).mpr inferInstance
    obtain ⟨m, hm⟩ := MathieuSmall.M22Recognition.of_small_degree τ
      (hf.comp e.symm.injective) hd
    left
    refine ⟨e.trans m, ?_⟩
    rcases hm with hE | hE
    · obtain ⟨E⟩ := hE
      left
      refine ⟨Representation.Equiv.mk E.toLinearEquiv (fun g => ?_)⟩
      have h := E.isIntertwining' (e g)
      simpa only [τ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        MulEquiv.symm_apply_apply, MulEquiv.trans_apply] using h
    · obtain ⟨E⟩ := hE
      right
      refine ⟨Representation.Equiv.mk E.toLinearEquiv (fun g => ?_)⟩
      have h := E.isIntertwining' (e g)
      simpa only [τ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        MulEquiv.symm_apply_apply, MulEquiv.trans_apply] using h
  · obtain ⟨e⟩ := ht
    right
    refine ⟨e, M22TripleCover.equiv_representationOfEquiv_of_finrank_twelve e σ hf ?_⟩
    exact Nat.le_antisymm hd
      (M22TripleCover.faithful_irreducible_finrank_ge_twelve_of_equiv e σ hf)

omit [Finite L] [IsQuasisimple L] [FiniteDimensional (ZMod 2) V] [σ.IsIrreducible] in
/-- A chosen triple-cover marking and binary intertwiner give the actual
six-dimensional F₄ coordinates, including the marked central scalar. -/
theorem triple_scalar_coordinates (e : L ≃* M22TripleCover)
    (E : Representation.Equiv σ (M22TripleCover.representationOfEquiv e)) :
    ∃ f : V ≃ₗ[ZMod 2] M22TripleCover.Unitary.Vector,
      (∀ g v, f (σ g v) = M22TripleCover.Unitary.fieldAction (e g) (f v)) ∧
      (∀ v, f (σ (e.symm M22TripleCover.scalar) v) =
        (QuadraticAlgebra.omega : Representation.SL2FourNatural.F) • f v) := by
  let f := E.toLinearEquiv.trans M22TripleCover.Unitary.binaryCoordinates
  refine ⟨f, ?_, ?_⟩
  · intro g v
    have h : E (σ g v) = M22TripleCover.representationOfEquiv e g (E v) :=
      LinearMap.congr_fun (E.isIntertwining' g) v
    change M22TripleCover.Unitary.coordinates (E (σ g v)) = _
    rw [h]
    change M22TripleCover.Unitary.coordinates (M22TripleCover.binaryRepresentation (e g) (E v)) =
      M22TripleCover.Unitary.coordinates
        (M22TripleCover.binaryRepresentation (e g)
          (M22TripleCover.Unitary.coordinates.symm (M22TripleCover.Unitary.coordinates (E v))))
    rw [LinearEquiv.symm_apply_apply]
  · intro v
    have h : E (σ (e.symm M22TripleCover.scalar) v) =
        M22TripleCover.representationOfEquiv e (e.symm M22TripleCover.scalar) (E v) :=
      LinearMap.congr_fun (E.isIntertwining' (e.symm M22TripleCover.scalar)) v
    change M22TripleCover.Unitary.coordinates (E (σ (e.symm M22TripleCover.scalar) v)) = _
    rw [h, M22TripleCover.representationOfEquiv_scalar]
    rw [M22TripleCover.Uniqueness.PointRestriction.field_scalar
      M22TripleCover.binaryRepresentation M22TripleCover.binaryRepresentation_faithful]
    exact M22TripleCover.Unitary.coordinates.map_smul _ _

omit [Finite L] [IsQuasisimple L] [FiniteDimensional (ZMod 2) V] [σ.IsIrreducible] in
/-- The literal model isomorphisms force binary degree ten or twelve. -/
theorem finrank_cases_of_models (h : ComponentModels σ) :
    Module.finrank (ZMod 2) V = 10 ∨ Module.finrank (ZMod 2) V = 12 := by
  rcases h with h | ⟨_, ⟨E⟩⟩
  · exact Or.inl h.finrank
  · exact Or.inr (E.toLinearEquiv.finrank_eq.trans M22TripleCover.binarySpace_finrank)

section Source
variable {G W : Type*} [Group G] [Finite G]
  [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
  (ρ : Representation (ZMod 2) G W) (N : Subgroup G)

/-- Application to the actual source actor. The degree bound is the remaining
representation-theoretic premise; cubic ratio at most two alone is not used
as a substitute for its proof. Ambient extension recognition is separate. -/
theorem source_componentModels_of_degree_le_twelve (h : SourceHypotheses ρ N)
    (hd : Module.finrank (ZMod 2) W ≤ 12) :
    ComponentModels (ρ.comp N.subtype) ∧
      (Module.finrank (ZMod 2) W = 10 ∨ Module.finrank (ZMod 2) W = 12) := by
  let := h.quasisimple
  let := h.irreducible
  obtain ⟨e⟩ := h.quotient
  have hm := componentModels_of_degree_le_twelve (ρ.comp N.subtype)
    (h.faithful.comp N.subtype_injective) e hd
  exact ⟨hm, finrank_cases_of_models _ hm⟩

end Source

section TripleSource
variable {G W : Type*} [Group G] [Finite G]
  [AddCommGroup W] [Module (ZMod 2) W]
  (ρ : Representation (ZMod 2) G W) (N : Subgroup G)

/-- The genuine source triple-cover branch, with binary dimension and
four-element scalar coordinates on the same component action. -/
theorem source_triple_coordinates_of_degree_le_twelve (h : SourceHypotheses ρ N)
    (hc : Nat.card (center N) = 3) (hd : Module.finrank (ZMod 2) W ≤ 12) :
    ∃ e : N ≃* M22TripleCover,
      Nonempty (Representation.Equiv (ρ.comp N.subtype) (M22TripleCover.representationOfEquiv e)) ∧
      Module.finrank (ZMod 2) W = 12 ∧
      ∃ f : W ≃ₗ[ZMod 2] M22TripleCover.Unitary.Vector,
        (∀ (n : N) w, f (ρ n w) = M22TripleCover.Unitary.fieldAction (e n) (f w)) ∧
        (∀ w, f (ρ (e.symm M22TripleCover.scalar) w) =
          (QuadraticAlgebra.omega : Representation.SL2FourNatural.F) • f w) := by
  let := h.quasisimple
  let := h.irreducible
  obtain ⟨e⟩ := M22TripleCover.nonempty_mulEquiv hc h.quotient
  have hf : Function.Injective (ρ.comp N.subtype) := h.faithful.comp N.subtype_injective
  have heq : Module.finrank (ZMod 2) W = 12 := Nat.le_antisymm hd
    (M22TripleCover.faithful_irreducible_finrank_ge_twelve_of_equiv e (ρ.comp N.subtype) hf)
  obtain ⟨E⟩ := M22TripleCover.equiv_representationOfEquiv_of_finrank_twelve e
    (ρ.comp N.subtype) hf heq
  exact ⟨e, ⟨E⟩, heq, triple_scalar_coordinates (ρ.comp N.subtype) e E⟩

end TripleSource

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.M22Source
