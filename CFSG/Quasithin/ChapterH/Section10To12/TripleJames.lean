module

public import CFSG.Quasithin.ChapterH.Section10To12.TripleModel
public import Theory.Representation.Mathieu.M22James.Classification

/-!
# James classification for the source triple-cover condition

A finite group satisfying `IsTripleM22` is identified with the genuine matrix
triple cover. Pulling back its binary action constructs the faithful
irreducible module of dimension twelve. Transport of the minimum-degree and
uniqueness theorems gives the source assertion for every such group, with no
additional representation-theoretic premises.

The transported central generator has order three, generates the actual
center, and satisfies X² + X + 1 in every faithful irreducible binary action.
These retain the central scalar needed for the subsequent F₄ structure.

Source: James (1973), Lemma 8.3, as cited in Aschbacher–Smith H.12.1(1)
and its proof, printed pp.393–394 (PDF pp.404–405). Uniqueness is asserted
at dimension twelve; the lower bound applies to all faithful irreducibles.
-/

@[expose] public noncomputable section

universe u

namespace CFSG.Quasithin.ChapterH.Section10To12

open Sporadic.Mathieu

namespace IsTripleM22

variable {L : Type*} [Group L] [Finite L] (hL : IsTripleM22 L)

/-- Recognition using quasisimplicity, the actual central quotient, and center order. -/
def groupEquiv : L ≃* M22TripleCover := by
  let := hL.quasisimple
  exact Classical.choice (M22TripleCover.nonempty_mulEquiv hL.center_card hL.centralQuotient)

/-- The constructed James module for an arbitrary genuine triple cover. -/
def binaryRepresentation : Representation (ZMod 2) L M22TripleCover.BinarySpace :=
  M22TripleCover.representationOfEquiv hL.groupEquiv

theorem binaryRepresentation_faithful : Function.Injective hL.binaryRepresentation :=
  M22TripleCover.representationOfEquiv_faithful hL.groupEquiv

instance binaryRepresentation_irreducible : hL.binaryRepresentation.IsIrreducible :=
  M22TripleCover.representationOfEquiv_irreducible hL.groupEquiv

/-- A distinguished generator of the actual center, retained under transport. -/
def centralScalar : L := hL.groupEquiv.symm M22TripleCover.scalar

theorem centralScalar_order : orderOf hL.centralScalar = 3 :=
  M22TripleCover.scalar_order_of_equiv hL.groupEquiv

theorem centralScalar_mem_center : hL.centralScalar ∈ Subgroup.center L :=
  M22TripleCover.scalar_mem_center_of_equiv hL.groupEquiv

theorem center_eq_zpowers_centralScalar :
    Subgroup.center L = Subgroup.zpowers hL.centralScalar := by
  symm
  apply Subgroup.eq_of_le_of_card_ge
    (Subgroup.zpowers_le.mpr hL.centralScalar_mem_center)
  rw [Nat.card_zpowers, hL.centralScalar_order, hL.center_card]

/-- Transport retains the concrete central operator, not just its order. -/
theorem binaryRepresentation_centralScalar :
    hL.binaryRepresentation hL.centralScalar =
      M22TripleCover.binaryRepresentation M22TripleCover.scalar :=
  M22TripleCover.representationOfEquiv_scalar hL.groupEquiv

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
  (ρ : Representation (ZMod 2) L W) (hf : Function.Injective ρ) [ρ.IsIrreducible]

include hL hf

/-- The lower bound in the first paragraph of the proof of H.12.1. -/
theorem faithful_irreducible_finrank_ge_twelve : 12 ≤ Module.finrank (ZMod 2) W :=
  M22TripleCover.faithful_irreducible_finrank_ge_twelve_of_equiv hL.groupEquiv ρ hf

/-- The uniqueness in H.12.1(1), by an actual intertwining linear equivalence. -/
theorem equiv_binaryRepresentation_of_finrank_twelve
    (hd : Module.finrank (ZMod 2) W = 12) :
    Nonempty (Representation.Equiv ρ hL.binaryRepresentation) :=
  M22TripleCover.equiv_representationOfEquiv_of_finrank_twelve hL.groupEquiv ρ hf hd

/-- The primitive central scalar satisfies the polynomial defining F₄. -/
theorem centralScalar_quadratic :
    ρ hL.centralScalar ^ 2 + ρ hL.centralScalar + 1 = 0 :=
  M22TripleCover.scalar_quadratic_of_equiv hL.groupEquiv ρ hf

theorem centralScalar_fixed_iff (v : W) : ρ hL.centralScalar v = v ↔ v = 0 :=
  M22TripleCover.scalar_fixed_iff_of_equiv hL.groupEquiv ρ hf v

/-- Any two faithful irreducible modules of binary dimension twelve are equivalent. -/
theorem equiv_of_finrank_twelve
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (σ : Representation (ZMod 2) L V) (hσ : Function.Injective σ) [σ.IsIrreducible]
    (hW : Module.finrank (ZMod 2) W = 12) (hV : Module.finrank (ZMod 2) V = 12) :
    Nonempty (Representation.Equiv ρ σ) := by
  obtain ⟨e⟩ := hL.equiv_binaryRepresentation_of_finrank_twelve ρ hf hW
  obtain ⟨f⟩ := hL.equiv_binaryRepresentation_of_finrank_twelve σ hσ hV
  exact ⟨e.trans f.symm⟩

end IsTripleM22

/-- H.12.1(1): existence and uniqueness up to actual binary module equivalence.
The ambient finite overgroup does not enter this clause. -/
theorem source_lemma_H_12_1_1 {L : Type*} [Group L] [Finite L] (hL : IsTripleM22 L) :
    ∃ ρ : Representation (ZMod 2) L M22TripleCover.BinarySpace,
      Function.Injective ρ ∧ ρ.IsIrreducible ∧
      Module.finrank (ZMod 2) M22TripleCover.BinarySpace = 12 ∧
      ∀ (W : Type u) [AddCommGroup W] [Module (ZMod 2) W]
        (σ : Representation (ZMod 2) L W),
        Function.Injective σ → σ.IsIrreducible → Module.finrank (ZMod 2) W = 12 →
        Nonempty (Representation.Equiv σ ρ) := by
  refine ⟨hL.binaryRepresentation, hL.binaryRepresentation_faithful,
    hL.binaryRepresentation_irreducible, M22TripleCover.binarySpace_finrank, ?_⟩
  intro W _ _ σ hf hi hd
  let := hi
  exact hL.equiv_binaryRepresentation_of_finrank_twelve σ hf hd

end CFSG.Quasithin.ChapterH.Section10To12
