module

public import Theory.PGroupCore
public import Theory.Representation.BinaryOffender.CommutatorRank
public import Theory.Representation.BinaryOffender.EquivariantOffender

/-!
# The literal quotient action used in 14.4.6--7

The star actor is H/O₂(H), the module is identified with U/Z(U), and the
intertwining equation uses conjugation by each h ∈ H on the actual normal
subgroup U. Faithfulness is the earlier 12.8.4(4) action-kernel input.
Images of marked subgroups are formed through the literal quotient map.
These definitions impose no involution-rank or two-core-equality conclusion.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004, notation
preceding 14.4.1 and Lemmas 14.4.6--7, printed pp.1006,1008--1009.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.RankCore
open Subgroup

variable (H : Type*) [Group H] (U : Subgroup H) [U.Normal]
  (V : Type*) [AddCommGroup V] [Module (ZMod 2) V]

/-- Coordinates for the actual central quotient with its faithful star action.
Both the quotient map and conjugation compatibility are part of the marking. -/
structure SourceAction where
  coordinates : (U ⧸ center U) ≃* Multiplicative V
  representation : Representation (ZMod 2) (H ⧸ pCore 2 H) V
  faithful : Function.Injective representation
  equivariant : ∀ (h : H) (u : U),
    (coordinates (QuotientGroup.mk' (center U) (MulAut.conjNormal h u))).toAdd =
      representation (QuotientGroup.mk' (pCore 2 H) h)
        (coordinates (QuotientGroup.mk' (center U) u)).toAdd

variable {H U V}

/-- The quotient vector of an actual element of U. -/
def SourceAction.vector (d : SourceAction H U V) (u : U) : V :=
  (d.coordinates (QuotientGroup.mk' (center U) u)).toAdd

/-- The image of a marked subgroup of H in U/Z(U), expressed as its binary
span. In particular `image V₂` is the distinguished source line Ṽ₂. -/
def SourceAction.image (d : SourceAction H U V) (A : Subgroup H) : Submodule (ZMod 2) V :=
  Submodule.span (ZMod 2) {v | ∃ u : U, (u : H) ∈ A ∧ d.vector u = v}

theorem SourceAction.vector_mem_image (d : SourceAction H U V)
    (A : Subgroup H) (u : U) (hu : (u : H) ∈ A) : d.vector u ∈ d.image A :=
  Submodule.subset_span ⟨u, hu, rfl⟩

/-- The actual displacement subspace of the star involution. -/
abbrev SourceAction.moved (d : SourceAction H U V) (a : H ⧸ pCore 2 H) :
    Submodule (ZMod 2) V := LinearMap.range (d.representation a - LinearMap.id)

/-- Its binary dimension, the source notation m([Ũ,a*]). -/
noncomputable def SourceAction.movedRank (d : SourceAction H U V)
    (a : H ⧸ pCore 2 H) : ℕ := Module.finrank (ZMod 2) (d.moved a)

theorem SourceAction.conjugation (d : SourceAction H U V) (h : H) (u : U) :
    d.vector (MulAut.conjNormal h u) =
      d.representation (QuotientGroup.mk' (pCore 2 H) h) (d.vector u) :=
  d.equivariant h u

/-- Intertwining transports the actual displacement subspace. -/
theorem SourceAction.moved_map
    (d : SourceAction H U V) (a : H ⧸ pCore 2 H)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (e : V ≃ₗ[ZMod 2] W) (t : W →ₗ[ZMod 2] W)
    (he : ∀ v, e (d.representation a v) = t (e v)) :
    (d.moved a).map e.toLinearMap = LinearMap.range (t - LinearMap.id) := by
  ext w
  constructor
  · rintro ⟨z, ⟨v, rfl⟩, rfl⟩
    refine ⟨e v, ?_⟩
    change t (e v) - e v = e (d.representation a v - v)
    rw [map_sub, he]
  · rintro ⟨z, rfl⟩
    refine ⟨d.representation a (e.symm z) - e.symm z,
      ⟨e.symm z, rfl⟩, ?_⟩
    change e (d.representation a (e.symm z) - e.symm z) = t z - z
    rw [map_sub, he, e.apply_symm_apply]

/-- Dimension transport uses the same displacement map and vector coordinates. -/
theorem SourceAction.movedRank_eq_of_equivariant
    (d : SourceAction H U V) (a : H ⧸ pCore 2 H)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (e : V ≃ₗ[ZMod 2] W) (t : W →ₗ[ZMod 2] W)
    (he : ∀ v, e (d.representation a v) = t (e v)) :
    d.movedRank a = Module.finrank (ZMod 2) (LinearMap.range (t - LinearMap.id)) := by
  rw [← d.moved_map a e t he, LinearEquiv.finrank_map_eq]
  rfl

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.RankCore
