module
public import Theory.Representation.BinaryOffender.SubspaceAction
import Mathlib.Tactic.FinCases

/-!
# Faithful binary upper-unitriangular actions in dimension three

A square-one upper-unitriangular matrix has parameters (a,b,c) with ac = 0,
so a faithful exponent-two group has at most six elements and binary rank at
most two. If the first coordinate line is absent from the commutator space,
the last off-diagonal parameter is injective, bounding the group by two.
These calculations are applied to the actual exterior action in `Geometry`
and `Images`, for Aschbacher--Smith 12.5.7/10, printed pp.820--821.
-/

@[expose] public section
namespace Representation.SL5ExteriorSquare.FlagThreeActions
abbrev Three := Fin 3 → ZMod 2

def upper (p v : Three) : Three := ![v 0 + p 0 * v 1 + p 1 * v 2, v 1 + p 2 * v 2, v 2]

variable {K : Type*} [Group K] (σ : Representation (ZMod 2) K Three)
  (code : K → Three) (hσ : ∀ g v, σ g v = upper (code g) v)

include σ code hσ

private lemma code_injective (hf : Function.Injective σ) : Function.Injective code := by
  intro g h he
  apply hf
  apply LinearMap.ext
  intro v
  rw [hσ, hσ, he]

private lemma code_square {g : K} (hg : g * g = 1) : code g 0 * code g 2 = 0 := by
  have hs : σ g (σ g ![0,0,1]) = ![0,0,1] := by
    change (σ g * σ g) _ = _
    rw [← map_mul, hg, map_one]
    rfl
  rw [hσ, hσ] at hs
  have ht := congrFun hs 0
  exact (by decide : ∀ a b c : ZMod 2, b + a * c + b = 0 → a * c = 0)
    (code g 0) (code g 1) (code g 2) (by simpa [upper] using ht)

/-- A faithful upper-unitriangular exponent-two group has at most six elements. -/
lemma card_le_six [Finite K] (hf : Function.Injective σ)
    (hs : ∀ g : K, g * g = 1) : Nat.card K ≤ 6 := by
  let f : K → {p : Three // p 0 * p 2 = 0} :=
    fun g => ⟨code g, code_square σ code hσ (hs g)⟩
  have hi : Function.Injective f := fun g h he =>
    code_injective σ code hσ hf (congrArg Subtype.val he)
  have hc := Nat.card_le_card_of_injective f hi
  have hn : Nat.card {p : Three // p 0 * p 2 = 0} = 6 := by
    rw [Nat.card_eq_fintype_card]
    decide
  exact hn ▸ hc

/-- Rank two forces the first coordinate vector into every subspace containing all displacements. -/
lemma first_mem_of_rank_two [Finite K] (hf : Function.Injective σ)
    (hr : Nat.log 2 (Nat.card K) = 2) (C : Submodule (ZMod 2) Three)
    (hC : ∀ g v, σ g v - v ∈ C) : ![1,0,0] ∈ C := by
  by_contra hn
  have ha (g : K) : code g 0 = 0 := by
    rcases (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) (code g 0) with hz | ho
    · exact hz
    · have hc := hC g ![0,1,0]
      rw [hσ] at hc
      have he : upper (code g) ![0,1,0] - ![0,1,0] = ![1,0,0] := by
        ext i
        fin_cases i <;> simp [upper, ho]
      exact (hn (he ▸ hc)).elim
  have hi : Function.Injective (fun g => code g 2) := by
    intro g h he
    apply code_injective σ code hσ hf
    have hb : code g 1 = code h 1 := by
      by_contra hb
      have hd := C.sub_mem (hC g ![0,0,1]) (hC h ![0,0,1])
      rw [hσ, hσ] at hd
      have hdiff : code g 1 - code h 1 = 1 := by
        exact ((by decide : ∀ a b : ZMod 2, a ≠ b → a - b = 1) _ _ hb)
      have hd' : (upper (code g) ![0,0,1] - ![0,0,1]) -
          (upper (code h) ![0,0,1] - ![0,0,1]) = ![1,0,0] := by
        ext i
        fin_cases i <;> simp [upper, hdiff, he]
      exact hn (hd' ▸ hd)
    ext i
    fin_cases i
    · exact (ha g).trans (ha h).symm
    · exact hb
    · exact he
  have hc := Nat.card_le_card_of_injective _ hi
  have hc' : Nat.card K ≤ 2 := by simpa using hc
  have hl := Nat.log_lt_of_lt_pow' (b := 2) (x := 2) (by decide) (show Nat.card K < 2^2 by omega)
  omega
end Representation.SL5ExteriorSquare.FlagThreeActions
