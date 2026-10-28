module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSmall.TwentyFive.SourceGeometry.Field
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSmall.TwentyFive.SourceGeometry.Diagonal
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSize.OuterGeneration.Transfer
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSmall.TwentyFive.InnerInvolutions

/-!
# The actual PSL₂(25) actor geometry at the FF threshold

The proved field and diagonal calculations supply four inner conjugates of
every outer involution. Their conjugators lift into the original component,
and faithful conjugation lifts generation to the source group. An elementary
actor disjoint from the component has rank at most two. At the FF threshold
these conjugates force degree at most eight, contrary to the order-thirteen
degree bound twelve. An actor meeting the component is already excluded by
inner displacement at least six and full ambient rank at most three.

Source: Aschbacher--Smith B.4.2 and K.2; Guralnick--Malle Proposition 4.1.
This is an FF source exclusion, preserving the separate stronger cubic API.
-/

public section
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSmall.TwentyFive
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open RankOneSize
universe u v
variable {G : Type u} {V : Type v} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (h : SourceAction ρ)
include h

/-- Disjoint elementary actors retain their actual outer-group rank bound. -/
theorem source_disjoint_actor_rank
    (hm : ClassicalGroup.IsPSL
      ((generalizedFitting G) ⧸ center (generalizedFitting G)) 2 25)
    (A : Subgroup G) (hA : IsElementaryTwo A)
    (hmeet : A ⊓ generalizedFitting G = ⊥) : rank A ≤ 2 := by
  let : IsElementaryAbelian 2 A := hA.2
  let : IsIrreducible (ρ.comp (generalizedFitting G).subtype) := h.irreducible
  obtain ⟨F, _, _, hc, ⟨eL⟩⟩ :=
    source_component_isPSL ρ h (by decide) (by decide) (by decide) hm
  have hd := OuterGeneration.disjoint_actor_card_le ρ (generalizedFitting G)
    h.faithful eL (p := 5) (n := 2) (by decide) (by decide) (by simpa using hc)
    (by decide) (by omega) A hmeet
  have hpow : 2 ^ rank A ≤ 2 ^ 2 := by
    rw [← hA.card_eq_two_pow_rank]
    exact hd
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hpow

/-- Four conjugates of an actual outer involution generate over the original
component, including the field and diagonal-field cases. -/
theorem source_outer_four_conjugates
    (hm : ClassicalGroup.IsPSL
      ((generalizedFitting G) ⧸ center (generalizedFitting G)) 2 25)
    (t : G) (htL : t ∉ generalizedFitting G) (ht : t ^ 2 = 1) :
    ∃ g : Fin 4 → G, generalizedFitting G ≤
      closure (Set.range fun i => g i * t * (g i)⁻¹) := by
  let : IsIrreducible (ρ.comp (generalizedFitting G).subtype) := h.irreducible
  obtain ⟨F, _, _, hc, ⟨eL⟩⟩ :=
    source_component_isPSL ρ h (by decide) (by decide) (by decide) hm
  have hF : GorensteinWalter.IsOddPrimePower (Nat.card F) :=
    ⟨5, 2, by decide, by decide, by decide, by simpa using hc⟩
  have hcard : 3 < Nat.card F := by omega
  let f := OuterGeneration.semilinearAction (generalizedFitting G) eL hF hcard
  have hout : f t ∉ GorensteinWalter.pGammaL2PSLRange F := by
    intro hh
    exact htL ((OuterGeneration.involution_mem_inner_iff ρ (generalizedFitting G)
      h.faithful eL hF hcard ht).mp hh)
  have ht' : f t ^ 2 = 1 := by rw [← map_pow, ht, map_one]
  have hmodel : ∃ c : Fin 4 → GorensteinWalter.PSL2 F,
      GorensteinWalter.pGammaL2PSLRange F ≤ Subgroup.closure (Set.range fun i =>
        SemidirectProduct.inl (Matrix.ProjectiveSpecialLinearGroup.toPGL (c i)) * f t *
          (SemidirectProduct.inl (Matrix.ProjectiveSpecialLinearGroup.toPGL (c i)))⁻¹) := by
    by_cases hlinear : (f t).right = 1
    · exact SourceGeometry.diagonal_four_generation hc (f t) hout ht' hlinear
    · exact SourceGeometry.field_four_generation hc (f t) ht' hlinear
  obtain ⟨c, hgen⟩ := hmodel
  exact OuterGeneration.lift_semilinear_generators ρ (generalizedFitting G)
    h.faithful eL hF hcard ht htL c hgen

omit h [Finite G] in
private theorem cyclic_fixedCodim_le {A : Subgroup G} {t : G} (ht : t ∈ A) :
    fixedCodim ρ (zpowers t) ≤ fixedCodim ρ A := by
  have hfix : fixedSpace ρ A ≤ fixedSpace ρ (zpowers t) := by
    intro v hv a
    exact hv ⟨a, (zpowers_le.mpr ht) a.property⟩
  have hd := Submodule.finrank_mono hfix
  have hA := fixedCodim_add_finrank ρ A
  have ht := fixedCodim_add_finrank ρ (zpowers t)
  omega

/-- No FF module occurs for an actual PSL₂(25) central quotient of F*(G).
All actor generation and rank estimates are supplied by proved model facts. -/
theorem source_not_ff
    (hm : ClassicalGroup.IsPSL
      ((generalizedFitting G) ⧸ center (generalizedFitting G)) 2 25) :
    ¬ IsFFModule ρ := by
  intro hff
  have hc : cubicRatio ρ ≤ (1 : ENNReal) := (cubicRatio_le_quadraticRatio ρ).trans
    ((isFFModule_iff_quadraticRatio_le_one ρ).mp hff)
  obtain ⟨A, hA, _, hsmall⟩ := (cubicRatio_le_nat_iff ρ 1).mp (by simpa using hc)
  simp only [one_mul] at hsmall
  let : IsElementaryAbelian 2 A := hA.2
  by_cases hmeet : A ⊓ generalizedFitting G = ⊥
  · obtain ⟨t, ht, ht1⟩ := A.bot_or_exists_ne_one.resolve_left hA.1
    have htL : t ∉ generalizedFitting G := by
      intro htL
      have htbot : t ∈ (⊥ : Subgroup G) := hmeet ▸
        (show t ∈ A ⊓ generalizedFitting G from ⟨ht, htL⟩)
      exact ht1 htbot
    obtain ⟨g, hg⟩ := source_outer_four_conjugates ρ h hm t htL
      (elemPow_eq_one_of_isElementaryAbelian t ht)
    have hr := source_disjoint_actor_rank ρ h hm A hA hmeet
    have htbound : fixedCodim ρ (zpowers t) ≤ 2 :=
      (cyclic_fixedCodim_le ρ ht).trans (hsmall.trans hr)
    have hd := (finrank_le_mul_fixedCodim_of_conjugate_generation ρ _
      (source_fixedSpace_eq_bot ρ h) t g hg).trans (Nat.mul_le_mul_left 4 htbound)
    have hl := twelve_le_degree_twentyFive ρ h.faithful hm
    omega
  · obtain ⟨t, ht, ht1⟩ := (A ⊓ generalizedFitting G).bot_or_exists_ne_one.resolve_left hmeet
    have ht2 : orderOf t = 2 := orderOf_eq_prime
      (elemPow_eq_one_of_isElementaryAbelian t ht.1) ht1
    have hlow := source_inner_displacement_ge_six ρ h hm ht.2 ht2
    have hr : rank A ≤ 3 := by
      have hb := source_two_rank_pslTwo ρ h (p := 5) (e := 2)
        (by decide) (by decide) (Or.inr rfl) (by decide) (by simpa using hm)
      simpa using rank_le_of_primeRank_le hA hb
    have hu := (cyclic_fixedCodim_le ρ ht.1).trans (hsmall.trans hr)
    omega

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSmall.TwentyFive
