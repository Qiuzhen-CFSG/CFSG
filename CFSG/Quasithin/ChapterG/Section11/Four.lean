module
public import CFSG.Quasithin.ChapterG.Section11.SmallCases
public import Theory.LinearAlgebra.BinaryAlternatingSevenLinear
public import Theory.Representation.NonsplitFour
public import Theory.GroupTheory.TwoThreeSolvable

/-!
# The nonsolvable four-dimensional branch of G.11.2

Faithfulness embeds the original group in GL₄(2), whose prime divisors are
2, 3, 5 and 7. Preservation of the nonzero alternating form excludes order
seven by the existing small-dimensional isometry theorem. If five did not
divide the group order, Burnside's two-prime theorem would make it solvable.
The marked low-rank witness supplies the remaining factor two. Together
with the solvable proof this gives G.11.2(2) in every four-dimensional case.

Source: Aschbacher--Smith G.11.2(2), printed p.364.
-/

public section
open Subgroup Module Representation Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterG.Section11
universe u v
variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {B : LinearMap.BilinForm (ZMod 2) V}
  {v : V} {W : Submodule (ZMod 2) V} {X : Subgroup G}
  [IsElementaryAbelian 2 X] {X₀ : Subgroup X}
  (h : Section10.Hypothesis ρ B v W X X₀)
include h

/-- The original alternating four-space admits no element of order seven. -/
theorem seven_not_dvd_card_of_degree_four (hd : finrank (ZMod 2) V = 4) :
    ¬ 7 ∣ Nat.card G := by
  intro h7
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 7 h7
  let α : G →* (V ≃ₗ[ZMod 2] V) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V).toMonoidHom.comp
      ρ.asGroupHom
  have hp : (α g) ^ 7 = 1 := by
    rw [← map_pow, ← hg, pow_orderOf_eq_one, map_one]
  have hB : B ≠ 0 := by
    intro hz
    exact h.point_ne_zero (h.nondegenerate.1 v (by simp [hz]))
  have he := BinaryAlternatingFour.nonzero_alternating_form_order_seven_eq_one
    (by omega : finrank (ZMod 2) V ≤ 4) B hB h.alternating (α g) hp (h.preserves g)
  have hg1 : g = 1 := by
    apply h.faithful
    apply LinearMap.ext
    intro w
    change (α g) w = (α 1) w
    rw [he]
    simp
  simp [hg1] at hg

/-- Nonsolvability forces the prime five in the original group order. -/
theorem five_dvd_card_of_nonsolvable_degree_four
    (hs : ¬ Group.IsSolvable G) (hd : finrank (ZMod 2) V = 4) :
    5 ∣ Nat.card G := by
  by_contra hn5
  have hn7 := seven_not_dvd_card_of_degree_four h hd
  have hdiv := Representation.card_dvd_card_GL_of_injective ρ h.faithful
  have hc : Nat.card G ∣ 20160 := by
    apply hdiv.trans
    rw [Matrix.card_GL_field, hd]
    norm_num [Fin.prod_univ_succ]
  apply hs
  apply isSolvable_of_prime_dvd_card_eq_two_or_three
  intro p hp hpd
  have hpd' : p ∣ 20160 := hpd.trans hc
  have hprimes : p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 := by
    have hh : p ∈ Nat.primeFactors 20160 :=
      Nat.mem_primeFactors.mpr ⟨hp, hpd', by decide⟩
    rw [show Nat.primeFactors 20160 = {2,3,5,7} by decide +kernel] at hh
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hh
  rcases hprimes with rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact (hn5 hpd).elim
  · exact (hn7 hpd).elim

/-- All four-dimensional low-rank source actions satisfy G.11.2(2). -/
theorem caseTwo_of_degree_four {K : GroupClass.{u}}
    (cover : Nonempty (Section09.SQTKCover K G))
    (hw : LowRankWitness ρ v X) (hd : finrank (ZMod 2) V = 4) : CaseTwo ρ B := by
  by_cases hs : Group.IsSolvable G
  · exact caseTwo_of_solvable_degree_four h cover hw hs hd
  have h5 := five_dvd_card_of_nonsolvable_degree_four h hs hd
  obtain ⟨a, _, ha, _⟩ := hw.exists_involution h.point_ne_zero
  have h2 : 2 ∣ Nat.card G := ha ▸ orderOf_dvd_natCard a
  exact ⟨hd, Or.inl ((show Nat.Coprime 2 5 by decide).mul_dvd_of_dvd_of_dvd h2 h5),
    h.faithful, h.alternating, h.nondegenerate, h.preserves⟩

end CFSG.Quasithin.ChapterG.Section11
