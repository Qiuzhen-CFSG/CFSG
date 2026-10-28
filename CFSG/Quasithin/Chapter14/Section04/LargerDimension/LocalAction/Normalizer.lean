module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.LocalAction.Basic
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity
public import Theory.SpecificGroups.PSL3Two.Parabolics.LinearModel

/-!
# Cubic source subgroups are not normal in a linear-three vertex

A member of the source X-family has order 3 · 2ⁿ. If it were normal in a
vertex with quotient PSL₃(2), its image would be trivial or the whole simple
quotient. The former makes it a two-group; the latter forces seven to divide
3 · 2ⁿ. Both are impossible. Maximality of XT then controls its relative
normalizer, as required in 14.4.13.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
14.4.8 and 14.4.13, printed pp.1009 and 1012.
-/

public section
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension

open Subgroup
open CFSG.Quasithin.Chapter14.Section04.LargerDimension
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem ThreeExtension.coreQuotient_card {H T X : Subgroup G} (h : ThreeExtension H T X) :
    Nat.card (coreQuotient X) = 3 := by
  have he := relIndex_map_map_of_injective (pCore 2 X) ⊤ X.subtype_injective
  rw [← MonoidHom.range_eq_map, range_subtype, relIndex_top_right] at he
  exact ((pCore 2 X).index_eq_card.symm.trans he.symm).trans h.index_three

theorem ThreeExtension.card_eq_three_mul_two_pow {H T X : Subgroup G} (h : ThreeExtension H T X) :
    ∃ n : ℕ, Nat.card X = 3 * 2 ^ n := by
  obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := X)).exists_card_eq
  exact ⟨n, by rw [card_eq_card_quotient_mul_card_subgroup (pCore 2 X), h.coreQuotient_card, hn]⟩

theorem ThreeExtension.not_normal_in_linear_vertex {H T X J : Subgroup G} (h : ThreeExtension H T X)
    (hXJ : X ≤ J) (e : coreQuotient J ≃* Matrix.PSL3Two.PSL) :
    ¬ J ≤ normalizer (X : Set G) := by
  let : IsSimpleGroup Matrix.PSL3Two.PSL :=
    Atlas.psl_simple_high_rank (F := ZMod 2) 3 (by decide)
  intro hn
  let A := X.subgroupOf J
  let : A.Normal := normal_subgroupOf_of_le_normalizer hn
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 J))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker = pCore 2 J := by
    dsimp only [f]
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
  have hAc : Nat.card A = Nat.card X :=
    Nat.card_congr (subgroupOfEquivOfLe hXJ).toEquiv
  obtain ⟨n,hnc⟩ := h.card_eq_three_mul_two_pow
  have hN : (A.map f).Normal := Normal.map inferInstance f hf
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (A.map f) hN with he | he
  · have hAP : A ≤ pCore 2 J := by
      rw [← hk]
      exact (Subgroup.map_eq_bot_iff _).mp he
    have hp : IsPGroup 2 A := (pCore_isPGroup (p := 2) (G := J)).of_injective
      (inclusion hAP) (inclusion_injective _)
    obtain ⟨m,hm⟩ := hp.exists_card_eq
    have hd : 3 ∣ 2 ^ m := by
      rw [← hm, hAc, hnc]
      exact dvd_mul_right _ _
    have := (show Nat.Prime 3 by decide).dvd_of_dvd_pow hd
    norm_num at this
  · have hd := A.card_map_dvd f
    rw [he, Nat.card_congr Subgroup.topEquiv.toEquiv, Matrix.PSL3Two.card_PSL,
      hAc, hnc] at hd
    have h7 : 7 ∣ 3 * 2 ^ n := (by decide : 7 ∣ 168).trans hd
    rcases (show Nat.Prime 7 by decide).dvd_mul.mp h7 with hh | hh
    · norm_num at hh
    · have := (show Nat.Prime 7 by decide).dvd_of_dvd_pow hh
      norm_num at this

/-- A source cubic subgroup cannot be contained in a two-group. -/
theorem ThreeExtension.not_le_twoGroup {H T X P : Subgroup G}
    (h : ThreeExtension H T X) (hP : IsPGroup 2 P) : ¬ X ≤ P := by
  intro hXP
  have hp : IsPGroup 2 X := hP.of_injective (inclusion hXP) (inclusion_injective _)
  obtain ⟨m,hm⟩ := hp.exists_card_eq
  obtain ⟨n,hn⟩ := h.card_eq_three_mul_two_pow
  have hd : 3 ∣ 2 ^ m := by
    rw [← hm, hn]
    exact dvd_mul_right _ _
  have := (show Nat.Prime 3 by decide).dvd_of_dvd_pow hd
  norm_num at this

end CFSG.Quasithin.Chapter14.Section04.LargerDimension
