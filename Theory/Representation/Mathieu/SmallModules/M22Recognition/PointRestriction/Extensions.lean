module

public import Theory.Representation.SimpleHeadQuotient
public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Field.ZMod

/-!
# Fixed vectors from the binary simple-degree gap

If every simple module of degree at most twelve has degree one or nine,
then a module of degree ten through twelve has a fixed vector or a fixed
covector. Take any simple quotient. A one-dimensional binary quotient is
trivial, and its dual embeds as a fixed line. A nine-dimensional quotient
leaves a nonzero submodule of dimension at most three; a simple submodule
of that kernel must be a trivial line. No splitting assumption is used.

This is the extension step in the point-stabilizer route to the M22 clause
of Aschbacher--Smith G.7.3(2), printed p.348. The simple-degree premise is
supplied separately by the actual PSL(3,4) tensor-word classification.
-/

public section

open Representation
namespace Representation.MathieuSmall.M22Recognition.PointRestriction
universe u
variable {G : Type*} [Group G]

private theorem binary_line_fixed {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) G W) (hd : Module.finrank (ZMod 2) W = 1)
    (g : G) (w : W) : σ g w = w := by
  by_cases hw : w = 0
  · simp [hw]
  obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one hd hw (σ g w)
  have hc0 : c ≠ 0 := by
    intro hz
    have hgw : σ g w = 0 := by simpa [hz] using hc.symm
    apply hw
    simpa only [σ.inv_self_apply, map_zero] using congrArg (σ g⁻¹) hgw
  have hc1 : c = 1 := (by decide : ∀ c : ZMod 2, c ≠ 0 → c = 1) c hc0
  simpa only [hc1, one_smul] using hc.symm

private theorem fixed_of_line_subrepresentation {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] (ρ : Representation (ZMod 2) G V)
    (S : Subrepresentation ρ) (hd : Module.finrank (ZMod 2) S.toSubmodule = 1) :
    ρ.invariants ≠ ⊥ := by
  let : Nontrivial S.toSubmodule := Module.nontrivial_of_finrank_eq_succ hd
  obtain ⟨v, hv⟩ := exists_ne (0 : S.toSubmodule)
  apply (Submodule.ne_bot_iff _).mpr
  refine ⟨v.val, ?_, fun hz => hv (Subtype.ext hz)⟩
  intro g
  exact congrArg Subtype.val (binary_line_fixed S.toRepresentation hd g v)

private theorem dual_fixed_of_line_quotient {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] (ρ : Representation (ZMod 2) G V)
    (N : Subrepresentation ρ)
    (hd : Module.finrank (ZMod 2) (V ⧸ N.toSubmodule) = 1) :
    ρ.dual.invariants ≠ ⊥ := by
  let : Nontrivial (V ⧸ N.toSubmodule) := Module.nontrivial_of_finrank_eq_succ hd
  obtain ⟨q, hq⟩ := exists_ne (0 : V ⧸ N.toSubmodule)
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one (ZMod 2) hq
  let l : Module.Dual (ZMod 2) V := f.comp N.toSubmodule.mkQ
  apply (Submodule.ne_bot_iff _).mpr
  refine ⟨l, ?_, ?_⟩
  · intro g
    ext v
    change f (N.quotientRepresentation g⁻¹ (N.toSubmodule.mkQ v)) =
      f (N.toSubmodule.mkQ v)
    rw [binary_line_fixed N.quotientRepresentation hd]
  · intro hz
    obtain ⟨v, hv⟩ := N.toSubmodule.mkQ_surjective q
    have hl : l v = 1 := by change f (N.toSubmodule.mkQ v) = 1; rw [hv, hf]
    rw [hz] at hl
    exact zero_ne_one hl

/-- A gap in binary simple degrees forces a fixed vector or a fixed covector,
including for nonsplit extensions. -/
theorem fixed_or_dual_of_simple_degrees
    (hdegrees : ∀ (W : Type u) [AddCommGroup W] [Module (ZMod 2) W]
      [FiniteDimensional (ZMod 2) W] (σ : Representation (ZMod 2) G W),
      σ.IsIrreducible → Module.finrank (ZMod 2) W ≤ 12 →
        Module.finrank (ZMod 2) W = 1 ∨ Module.finrank (ZMod 2) W = 9)
    {V : Type u} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) G V)
    (hlo : 10 ≤ Module.finrank (ZMod 2) V)
    (hhi : Module.finrank (ZMod 2) V ≤ 12) :
    ρ.invariants ≠ ⊥ ∨ ρ.dual.invariants ≠ ⊥ := by
  let : Nontrivial V := Module.nontrivial_of_finrank_pos (by omega :
    0 < Module.finrank (ZMod 2) V)
  let : IsCoatomic (Subrepresentation ρ) := SimpleHeadQuotient.subrepresentation_coatomic ρ
  obtain ⟨N, hN⟩ := IsCoatomic.exists_coatom (Subrepresentation ρ)
  have hsum := N.toSubmodule.finrank_quotient_add_finrank
  have hq := hdegrees _ N.quotientRepresentation
    (SimpleHeadQuotient.irreducible_quotient_of_isCoatom N hN) (by omega)
  rcases hq with hq | hq
  · exact Or.inr (dual_fixed_of_line_quotient ρ N hq)
  have hNpos : 0 < Module.finrank (ZMod 2) N.toSubmodule := by omega
  let : Nontrivial N.toSubmodule := Module.nontrivial_of_finrank_pos hNpos
  obtain ⟨S, hS⟩ :=
    Subrepresentation.irreducible_subrepresentation_of_finite_dimensional N.toRepresentation
  have hSle := Submodule.finrank_le S.toSubmodule
  have hdS := hdegrees _ S.toRepresentation hS (by omega)
  have hSone : Module.finrank (ZMod 2) S.toSubmodule = 1 := by rcases hdS with h | h <;> omega
  have hfix := fixed_of_line_subrepresentation N.toRepresentation S hSone
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).mp hfix
  left
  apply (Submodule.ne_bot_iff _).mpr
  refine ⟨v.val, ?_, fun hz => hv0 (Subtype.ext hz)⟩
  intro g
  exact congrArg Subtype.val (hv g)

end Representation.MathieuSmall.M22Recognition.PointRestriction
