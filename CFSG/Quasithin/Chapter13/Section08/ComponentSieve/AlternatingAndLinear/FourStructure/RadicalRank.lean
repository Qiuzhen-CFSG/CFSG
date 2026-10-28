module

public import Theory.Representation.BinaryOffender.SmallRank
public import Mathlib.GroupTheory.Index
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The rank bound for the actor in the plane radical

Suppose an actor fixes a two-space P in a four-dimensional binary module and
displaces all vectors into P. Evaluation on a vector outside P is a group
homomorphism to P. Its kernel fixes the hyperplane spanned by P and that vector.
If every such hyperplane fixer has order at most two, the actor has order at
most eight. For an elementary actor, the exclusion of noncyclic hyperplane
fixers gives exactly this bound.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, the rank-at-most-three deduction in 13.8.25,
printed p.961. The splitting argument establishing the hyperplane exclusion
is a separate source obligation.
-/

public section
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure
open Representation.BinaryOffender
variable {H U : Type*} [Group H] [AddCommGroup U] [Module (ZMod 2) U]
  [FiniteDimensional (ZMod 2) U] (ρ : Representation (ZMod 2) H U)

/-- Evaluation on one vector bounds a subgroup of the radical of a plane
stabilizer, provided every subgroup fixing a hyperplane has order at most two. -/
theorem rank_le_three_of_plane_radical
    (hU : Module.finrank (ZMod 2) U = 4)
    (P : Submodule (ZMod 2) U) (hP : Module.finrank (ZMod 2) P = 2)
    (A : Subgroup H) (hfix : P ≤ fixedSpace ρ A)
    (hdisplace : ∀ a ∈ A, ∀ u : U, ρ a u - u ∈ P)
    (haxis : ∀ B ≤ A, fixedCodim ρ B ≤ 1 → Nat.card B ≤ 2) : rank A ≤ 3 := by
  classical
  let : Finite P := Module.finite_of_finite (ZMod 2)
  have hPt : P ≠ ⊤ := by
    intro h
    rw [h, finrank_top, hU] at hP
    omega
  obtain ⟨v, _, hv⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr hPt)
  let δ : A →* Multiplicative P := {
    toFun a := Multiplicative.ofAdd ⟨ρ a v - v, hdisplace a a.property v⟩
    map_one' := by
      apply Subtype.ext
      change ρ 1 v - v = 0
      simp
    map_mul' a b := by
      apply Subtype.ext
      change ρ ((a : H) * b) v - v = (ρ a v - v) + (ρ b v - v)
      have hb := hfix (hdisplace b b.property v) a
      change ρ a (ρ b v - v) = ρ b v - v at hb
      rw [map_sub] at hb
      rw [map_mul]
      change ρ a (ρ b v) - v = _
      rw [← hb]
      abel }
  let B := δ.ker.map A.subtype
  have hBA : B ≤ A := by
    rintro _ ⟨b, _, rfl⟩
    exact b.property
  have hvB : v ∈ fixedSpace ρ B := by
    intro b
    obtain ⟨a, ha, he⟩ := b.property
    have ha' : ρ a v - v = 0 := congrArg (fun x : Multiplicative P => (x.toAdd : U)) ha
    change ρ (b : H) v = v
    rw [← he]
    exact sub_eq_zero.mp ha'
  have hPB : P ≤ fixedSpace ρ B := by
    intro p hp b
    exact hfix hp ⟨b, hBA b.property⟩
  have hF : P ⊔ Submodule.span (ZMod 2) {v} ≤ fixedSpace ρ B :=
    sup_le hPB (Submodule.span_le.mpr (by
      intro u hu
      obtain rfl := Set.mem_singleton_iff.mp hu
      exact hvB))
  have hdimF : Module.finrank (ZMod 2) (P ⊔ Submodule.span (ZMod 2) {v} : Submodule (ZMod 2) U) = 3 := by
    rw [Submodule.finrank_sup_span_singleton hv, hP]
  have hcodim : fixedCodim ρ B ≤ 1 := by
    have := Submodule.finrank_mono hF
    have := fixedCodim_add_finrank ρ B
    omega
  have hker : Nat.card δ.ker ≤ 2 := by
    have hcard := Subgroup.card_map_of_injective (K := δ.ker) A.subtype_injective
    exact hcard ▸ haxis B hBA hcodim
  have hrange : Nat.card δ.range ≤ 4 := by
    have := Nat.card_le_card_of_injective (fun x : δ.range => (x : Multiplicative P))
      Subtype.val_injective
    have hc : Nat.card (Multiplicative P) = 4 := by
      rw [Nat.card_congr Multiplicative.toAdd, Module.natCard_eq_pow_finrank (K := ZMod 2),
        Nat.card_zmod, hP]
      decide
    omega
  have hcard : Nat.card A ≤ 8 := by
    have := δ.ker.card_mul_index
    rw [Subgroup.index_ker] at this
    have := Nat.mul_le_mul hker hrange
    omega
  exact (Nat.log_monotone hcard).trans (by decide : Nat.log 2 8 ≤ 3)

/-- For an elementary binary actor, excluding noncyclic hyperplane fixers
supplies the order bound needed by the evaluation argument. -/
theorem rank_le_three_of_no_noncyclic_axis [Finite H]
    (hU : Module.finrank (ZMod 2) U = 4)
    (P : Submodule (ZMod 2) U) (hP : Module.finrank (ZMod 2) P = 2)
    (A : Subgroup H) (hA : IsElementaryTwo A) (hfix : P ≤ fixedSpace ρ A)
    (hdisplace : ∀ a ∈ A, ∀ u : U, ρ a u - u ∈ P)
    (haxis : ∀ B ≤ A, 1 < rank B → 1 < fixedCodim ρ B) : rank A ≤ 3 := by
  apply rank_le_three_of_plane_radical ρ hU P hP A hfix hdisplace
  intro B hBA hcodim
  by_cases hB : B = ⊥
  · simp only [hB, Subgroup.card_bot]
    decide
  · have hBrank : rank B ≤ 1 := by
      by_contra h
      have := haxis B hBA (by omega)
      omega
    rw [(hA.of_le hBA hB).card_eq_two_pow_rank]
    exact (Nat.pow_le_pow_right (by decide : 0 < 2) hBrank).trans (by decide)

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure
