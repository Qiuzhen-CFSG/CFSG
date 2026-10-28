module

public import Theory.Representation.BinaryOffender.SylowFixedGeneration
public import Theory.SpecificGroups.SL2.TwoSubgroupExponent
public import Mathlib.Algebra.Algebra.ZMod

/-!
# Interfaces for binary SL₂ recognition from Sylow fixed spaces

The hypotheses of G.1.6 concern the original module, which may be a nonsplit
central extension. The output is an equivariant surjection with exactly the
global fixed space as kernel. The auxiliary quotient action is the literal
action on that quotient. No semisimplicity or recognition assertion is built
into the hypotheses.

Source: Aschbacher--Smith, G.1.6--7, printed pp.329--330.
-/

@[expose] public noncomputable section
open scoped MatrixGroups
open Representation.BinaryOffender
namespace Representation.SL2SylowFixedRecognition

variable {F V : Type*} [Field F] [CharP F 2]
  [AddCommGroup V] [Module (ZMod 2) V]

/-- The two hypotheses on the original module in G.1.6. -/
structure FixedSpaceHypotheses (ρ : Representation (ZMod 2) SL(2,F) V)
    (R : Sylow 2 SL(2,F)) : Prop where
  generated : (⨆ g : SL(2,F), (fixedSpace ρ R).map (ρ g)) = ⊤
  uniform : ∀ r ∈ (R : Subgroup SL(2,F)), r ≠ 1 →
    fixedSpace ρ (Subgroup.zpowers r) = fixedSpace ρ R

/-- The actual quotient by the global fixed space, with the original actors. -/
def centralQuotient (ρ : Representation (ZMod 2) SL(2,F) V) :
    Representation (ZMod 2) SL(2,F) (V ⧸ fixedSpace ρ ⊤) :=
  ρ.quotient (fixedSpace ρ ⊤) (by
    intro g v hv
    change ρ g v ∈ fixedSpace ρ ⊤
    have he : ρ g v = v := hv ⟨g, Subgroup.mem_top g⟩
    rw [he]
    exact hv)

omit [CharP F 2] in
theorem centralQuotient_mk (ρ : Representation (ZMod 2) SL(2,F) V)
    (g : SL(2,F)) (v : V) :
    centralQuotient ρ g ((fixedSpace ρ ⊤).mkQ v) =
      (fixedSpace ρ ⊤).mkQ (ρ g v) := rfl

local instance : Algebra (ZMod 2) F := ZMod.algebra F 2

/-- Actual direct-sum coordinates; the actor is not twisted by an automorphism. -/
def NaturalCoordinates (ρ : Representation (ZMod 2) SL(2,F) V) : Prop :=
  ∃ (m : ℕ) (e : V ≃ₗ[ZMod 2] (Fin m → Fin 2 → F)),
    ∀ g v i, e (ρ g v) i = Matrix.mulVec g.val (e v i)

/-- The G.1.6 output, including the precise central kernel. -/
structure QuotientCoordinates (ρ : Representation (ZMod 2) SL(2,F) V) where
  multiplicity : ℕ
  coordinates : V →ₗ[ZMod 2] (Fin multiplicity → Fin 2 → F)
  surjective : Function.Surjective coordinates
  kernel : LinearMap.ker coordinates = fixedSpace ρ ⊤
  intertwines : ∀ g v i, coordinates (ρ g v) i =
    Matrix.mulVec g.val (coordinates v i)

/-- Coordinates on the quotient give coordinates on the original module
without choosing a complement to its fixed space. -/
theorem quotientCoordinates_of_natural (ρ : Representation (ZMod 2) SL(2,F) V)
    (h : NaturalCoordinates (centralQuotient ρ)) : Nonempty (QuotientCoordinates ρ) := by
  obtain ⟨m,e,he⟩ := h
  refine ⟨⟨m,e.toLinearMap.comp (fixedSpace ρ ⊤).mkQ,
    e.surjective.comp (fixedSpace ρ ⊤).mkQ_surjective,?_,?_⟩⟩
  · ext v
    change e ((fixedSpace ρ ⊤).mkQ v) = 0 ↔ v ∈ fixedSpace ρ ⊤
    rw [map_eq_zero_iff e e.injective]
    exact Submodule.Quotient.mk_eq_zero _
  · intro g v i
    exact he g ((fixedSpace ρ ⊤).mkQ v) i

/-- A moved vector forces positive multiplicity, even for a central extension. -/
theorem QuotientCoordinates.positive_of_movement
    {ρ : Representation (ZMod 2) SL(2,F) V} (c : QuotientCoordinates ρ)
    (hmove : ∃ g v, ρ g v ≠ v) : 0 < c.multiplicity := by
  by_contra hn
  have hz : c.multiplicity = 0 := Nat.eq_zero_of_not_pos hn
  obtain ⟨g,v,hv⟩ := hmove
  have hvker : v ∈ LinearMap.ker c.coordinates := by
    change c.coordinates v = 0
    ext i
    exact (Fin.elim0 (hz ▸ i))
  rw [c.kernel] at hvker
  exact hv (hvker ⟨g, Subgroup.mem_top g⟩)

variable [Finite F]

omit [CharP F 2] in
/-- The Gaschütz step: fixed-space generation yields the moving space plus
global fixed vectors. It asserts a sum, not a direct sum. -/
theorem moved_sup_fixed (ρ : Representation (ZMod 2) SL(2,F) V)
    (R : Sylow 2 SL(2,F)) (h : FixedSpaceHypotheses ρ R) :
    subspaceCommutator ρ ⊤ ⊤ ⊔ fixedSpace ρ ⊤ = ⊤ :=
  moved_sup_fixedSpace_of_sylow_fixed_generators ρ ⊤ R (top_sup_eq _)
    (fixedSpace ρ R) le_rfl h.generated

end Representation.SL2SylowFixedRecognition
