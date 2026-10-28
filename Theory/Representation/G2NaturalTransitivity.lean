module

public import Theory.Representation.G2NaturalBinary
public import Theory.Representation.G2NaturalTransitivity.FieldTransport
public import Mathlib.FieldTheory.Perfect

/-!
# Nonzero-vector transitivity of the derived natural G₂ action

Over a finite field of characteristic two, adding a scalar identity to a
trace-zero octonion can kill its norm, since squaring is surjective. Thus every
nonzero class in the six-dimensional natural quotient has a nonzero singular
representative. Root/Weyl reduction and a torus element send it to the first
basis vector. For fields larger than two, perfectness puts this transporter
in the derived group. For order two, genuine field, group and semilinear
module transport instead applies the checked binary derived-group orbit theorem.

This proves the intrinsic orbit fact for the natural module in
Aschbacher--Smith G.9.3(10), printed pp.354,356--357, used to exclude that
module in the proof of 15.3.58, printed p.1149. It imposes no orbit or model
recognition premise. The octonion geometry comes from the attributed ATLAS
ports underlying `G2Natural`; no additional ATLAS source is copied here.
-/

@[expose] public noncomputable section

namespace Atlas.G2.Natural

open Atlas.SplitOctonion

variable {F : Type*} [Field F] [CharP F 2]

omit [CharP F 2] in
private theorem norm_add_scalar_identity (x : Carrier F) (r : F) :
    SplitOctonion.norm (x + r • unit) = SplitOctonion.norm x + r * trace x + r ^ 2 := by
  simp [SplitOctonion.norm, trace, unit]
  ring

/-- Every natural-module class has a singular trace-zero representative.
Surjectivity of squaring allows its norm to be killed by a scalar identity. -/
theorem exists_singular_representative [Finite F] (x : Space F) :
    ∃ y : TraceZero F, SplitOctonion.norm y.val = 0 ∧ mk F y = x := by
  obtain ⟨y, rfl⟩ := mk_surjective F x
  obtain ⟨r, hr⟩ := surjective_frobenius F 2 (SplitOctonion.norm y.val)
  change r ^ 2 = SplitOctonion.norm y.val at hr
  refine ⟨y + r • identity F, ?_, ?_⟩
  · change SplitOctonion.norm (y.val + r • unit) = 0
    rw [norm_add_scalar_identity, (show trace y.val = 0 from y.property), hr]
    simp [CharTwo.add_self_eq_zero]
  · simp

private def firstVector : TraceZero F :=
  ⟨basisVector 0, by simp [mem_traceZero, trace, basisVector]⟩

/-- Singular-vector reduction followed by a torus element normalizes a class. -/
private theorem exists_to_first [Finite F] (x : Space F) (hx : x ≠ 0) :
    ∃ g : Model F, Natural.action F g x = mk F firstVector := by
  obtain ⟨y, hn, hy⟩ := exists_singular_representative x
  have hy0 : y.val ≠ 0 := by
    intro h
    apply hx
    rw [← hy, show y = 0 from Subtype.ext h, map_zero]
  obtain ⟨g, _, r, hr, hg⟩ := singular_vector_reduction_first y.val y.property hn hy0
  let t := torus (Units.mk0 r hr)⁻¹ (1 : Fˣ)
  have ht : (t * g).val y.val = basisVector 0 := by
    change t.val (g.val y.val) = _
    rw [hg, map_smul]
    dsimp [t]
    rw [torus_first_basis]
    simp [smul_smul, hr]
  refine ⟨t * g, ?_⟩
  rw [← hy, action_mk]
  congr 1
  exact Subtype.ext ht

/-- The full split G₂ group is transitive on the nonzero natural vectors. -/
theorem action_transitive [Finite F] {x y : Space F} (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ g : Model F, Natural.action F g x = y := by
  obtain ⟨g, hg⟩ := exists_to_first x hx
  obtain ⟨h, hh⟩ := exists_to_first y hy
  refine ⟨h⁻¹ * g, ?_⟩
  rw [map_mul, Module.End.mul_apply, hg, ← hh]
  change (Natural.action F h⁻¹ * Natural.action F h) y = y
  rw [← map_mul, inv_mul_cancel, map_one]
  rfl

/-- Transfer the checked binary orbit theorem through genuine field, group,
and semilinear module equivalences. -/
private theorem derived_transitive_binary [Finite F] (hF : Nat.card F = 2)
    {x y : Space F} (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ g : commutator (Model F), derivedAction F g x = y := by
  let := Fintype.ofFinite F
  let e : ZMod 2 ≃+* F := ZMod.ringEquiv F (by simpa using hF)
  let E := Transitivity.fieldTransport e
  obtain ⟨g, hg⟩ := Binary.natural_transitive
    (show E.symm x ≠ 0 by simpa using hx)
    (show E.symm y ≠ 0 by simpa using hy)
  refine ⟨Transitivity.derivedFieldTransport e g, ?_⟩
  have ht := Transitivity.fieldTransport_derivedAction e g (E.symm x)
  change E (derivedAction (ZMod 2) g (E.symm x)) =
    derivedAction F (Transitivity.derivedFieldTransport e g) (E (E.symm x)) at ht
  rw [hg, E.apply_symm_apply, E.apply_symm_apply] at ht
  exact ht.symm

/-- The derived split G₂ group is transitive on nonzero vectors of its actual
natural module over every finite field of characteristic two. In order two
this uses the actual proper derived subgroup, not the full automorphism group. -/
theorem derivedAction_transitive (F : Type*) [Field F] [Finite F] [CharP F 2]
    (x y : Space F) (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ g : commutator (Model F), derivedAction F g x = y := by
  by_cases hF : Nat.card F = 2
  · exact derived_transitive_binary hF hx hy
  · have hcard : 2 < Nat.card F := by
      let := Fintype.ofFinite F
      have : 1 < Fintype.card F := Fintype.one_lt_card
      rw [Nat.card_eq_fintype_card] at hF ⊢
      omega
    let := Atlas.G2.isPerfect hcard
    obtain ⟨g, hg⟩ := action_transitive hx hy
    exact ⟨⟨g, by rw [Group.IsPerfect.commutator_eq_top]; trivial⟩, hg⟩

end Atlas.G2.Natural
