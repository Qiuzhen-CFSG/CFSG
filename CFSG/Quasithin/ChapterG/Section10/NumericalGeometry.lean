module

public import CFSG.Quasithin.ChapterG.Section10.Basic
public import Theory.LinearAlgebra.AlternatingFinrank
public import Theory.ElementaryAbelian.GeneratorRank
public import Theory.ElementaryAbelian.Quotient
public import Mathlib.FieldTheory.Finiteness

/-!
# Numerical equality in the marked symplectic geometry of G.10

A nontrivial smaller actor strictly lowers the elementary abelian quotient
rank. Combining this with G.10.2 bounds the symplectic dimension by twice the
full actor dimension. At the small-actor bound, alternating parity and the
nonzero marked point force equality throughout: the smaller actor vanishes
and the marked isotropic space has half the ambient dimension.

Source: Aschbacher--Smith, G.10.1--2, printed p.357; the numerical step used
with this geometry in 14.3.12.
-/

@[expose] public noncomputable section
open Subgroup Module
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterG.Section10.Hypothesis

private theorem elementary_rank_eq_finrank (A : Type*) [Group A] [Finite A]
    [IsElementaryAbelian 2 A] : Group.rank A = finrank (ZMod 2) (Additive A) := by
  let : CommGroup A := IsMulCommutative.instCommGroup
  apply le_antisymm (IsElementaryAbelian.rank_le_finrank (p := 2) A)
  have hc : Nat.card A = 2 ^ finrank (ZMod 2) (Additive A) := by
    rw [Nat.card_congr Additive.ofMul]
    simpa only [Nat.card_zmod] using Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive A)
  apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
  rw [← hc]
  exact Nat.le_of_dvd (by positivity) (card_dvd_exponent_pow_rank' A
    (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 2 A)))

private theorem elementary_card (A : Type*) [Group A] [Finite A]
    [IsElementaryAbelian 2 A] : Nat.card A = 2 ^ Group.rank A := by
  rw [elementary_rank_eq_finrank, Nat.card_congr Additive.ofMul]
  simpa only [Nat.card_zmod] using Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive A)

private theorem quotient_rank_lt_of_ne_bot (A : Type*) [Group A] [Finite A]
    [IsElementaryAbelian 2 A] (N : Subgroup A) (hN : N ≠ ⊥) :
    Group.rank (A ⧸ N) < Group.rank A := by
  have hcard := N.card_mul_index
  rw [index_eq_card, elementary_card (A ⧸ N), elementary_card A] at hcard
  have hlarge : 1 < Nat.card N := N.one_lt_card_iff_ne_bot.mpr hN
  have hpos : 0 < 2 ^ Group.rank (A ⧸ N) := by positivity
  have hlt : 2 ^ Group.rank (A ⧸ N) < 2 ^ Group.rank A := by nlinarith
  exact (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp hlt

variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {B : LinearMap.BilinForm (ZMod 2) V}
  {v : V} {W : Submodule (ZMod 2) V} {X : Subgroup G}
  [IsElementaryAbelian 2 X] {X₀ : Subgroup X}
  (h : Hypothesis ρ B v W X X₀)
include h

/-- The nonzero marked point and alternating parity exclude dimensions zero and one. -/
theorem two_le_dimension : 2 ≤ finrank (ZMod 2) V := by
  have hp : 0 < finrank (ZMod 2) V := by
    let : Nontrivial V := ⟨⟨v, 0, h.point_ne_zero⟩⟩
    exact Module.finrank_pos
  obtain ⟨n, hn⟩ := AlternatingForm.even_finrank B h.alternating h.nondegenerate
  omega

/-- A nontrivial smaller actor removes one binary rank from the quotient, so
G.10.2 bounds the degree by twice the full actor dimension. -/
theorem dimension_le_twice_actor_of_smaller_ne_bot (hX₀ : X₀ ≠ ⊥) :
    finrank (ZMod 2) V ≤ 2 * finrank (ZMod 2) (Additive X) := by
  have hq := quotient_rank_lt_of_ne_bot X X₀ hX₀
  rw [elementary_rank_eq_finrank X] at hq
  have hb := h.dimension_bound.1
  omega

/-- At the source small-actor bound the smaller actor vanishes, the actor
has the maximal permitted rank, and the marked isotropic space is half-dimensional. -/
theorem numerical_equality_of_actor_dimension_le
    (hm : finrank (ZMod 2) (Additive X) ≤ finrank (ZMod 2) V / 2 - 1) :
    X₀ = ⊥ ∧ finrank (ZMod 2) (Additive X) = finrank (ZMod 2) V / 2 - 1 ∧
      finrank (ZMod 2) W = finrank (ZMod 2) V / 2 := by
  have hd := h.two_le_dimension
  obtain ⟨n, hn⟩ := AlternatingForm.even_finrank B h.alternating h.nondegenerate
  have hX₀ : X₀ = ⊥ := by
    by_contra hne
    have hb := h.dimension_le_twice_actor_of_smaller_ne_bot hne
    omega
  have hqle := Group.rank_le_of_surjective (QuotientGroup.mk' X₀)
    (QuotientGroup.mk'_surjective X₀)
  rw [elementary_rank_eq_finrank X] at hqle
  have hb := h.dimension_bound.1
  have hmeq : finrank (ZMod 2) (Additive X) = finrank (ZMod 2) V / 2 - 1 := by omega
  have hqeq : Group.rank (X ⧸ X₀) = finrank (ZMod 2) (Additive X) := by omega
  have hw := h.dimension
  exact ⟨hX₀, hmeq, by omega⟩

end CFSG.Quasithin.ChapterG.Section10.Hypothesis
