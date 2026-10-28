module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSize.OuterGeneration.Transfer
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSize.OuterGeneration.Models
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSize.OuterGeneration.Diagonal
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSize.OuterGeneration.Field
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSize.ProjectiveDegree

/-!
# Outer actors in the rank-one size bound

The actual component is PSL₂ by the already proved covering comparison.
Faithful outer conjugation then bounds a disjoint elementary actor's order by
2e, hence its binary rank by e for the two requested field degrees.
The diagonal and field calculations supply four conjugates generating the
literal PSL₂ range. Their PSL₂ conjugators lift to the original component,
and faithfulness on L⟨t⟩ lifts generation to G. This proves both outer clauses
of `SourceGenerationBounds`, without a ratio or degree hypothesis.

Source: Guralnick--Malle, Classification of 2F-modules I, Proposition 4.1,
manuscript pp.8--9; Aschbacher--Smith K.2, printed p.453.
-/

public section
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSize
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender

universe u v
variable {G : Type u} {V : Type v} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (h : SourceAction ρ)
include h

/-- The disjoint actor has rank at most the prime or quadratic field degree.
No ratio or representation-degree bound is assumed. -/
theorem source_disjoint_actor_rank {p e : ℕ} (hp : p.Prime) (ho : Odd p)
    (he : e = 1 ∨ e = 2) (hlarge : 25 < p ^ e)
    (hm : ClassicalGroup.IsPSL
      ((generalizedFitting G) ⧸ center (generalizedFitting G)) 2 (p ^ e))
    (A : Subgroup G) (hA : IsElementaryTwo A)
    (hmeet : A ⊓ generalizedFitting G = ⊥) : rank A ≤ e := by
  let : IsElementaryAbelian 2 A := hA.2
  let : IsIrreducible (ρ.comp (generalizedFitting G).subtype) := h.irreducible
  obtain ⟨F, _, _, hc, ⟨eL⟩⟩ :=
    source_component_isPSL ρ h (by omega) (ho.pow (n := e)) (by omega) hm
  have hn : 0 < e := by rcases he with rfl | rfl <;> decide
  have hd := OuterGeneration.disjoint_actor_card_le ρ (generalizedFitting G)
    h.faithful eL hp ho hc hn (by omega) A hmeet
  have hpow : 2 ^ rank A ≤ 2 ^ e := by
    rw [← hA.card_eq_two_pow_rank]
    exact hd.trans (by rcases he with rfl | rfl <;> norm_num)
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hpow

/-- The actual ambient four-conjugate clause follows from the two concrete
model calculations. The unconditional application is
`source_outer_four_conjugates` below. -/
theorem source_outer_four_conjugates_of_models
    (hdiag : OuterGeneration.DiagonalFourGeneration.{0})
    (hfield : OuterGeneration.FieldFourGeneration.{0})
    {p e : ℕ} (hp : p.Prime) (ho : Odd p) (he : e = 1 ∨ e = 2)
    (hlarge : 25 < p ^ e)
    (hm : ClassicalGroup.IsPSL
      ((generalizedFitting G) ⧸ center (generalizedFitting G)) 2 (p ^ e))
    (t : G) (htL : t ∉ generalizedFitting G) (ht : t ^ 2 = 1) :
    ∃ g : Fin 4 → G, generalizedFitting G ≤
      closure (Set.range fun i => g i * t * (g i)⁻¹) := by
  let : IsIrreducible (ρ.comp (generalizedFitting G).subtype) := h.irreducible
  obtain ⟨F, _, _, hc, ⟨eL⟩⟩ :=
    source_component_isPSL ρ h (by omega) (ho.pow (n := e)) (by omega) hm
  have hn : 0 < e := by rcases he with rfl | rfl <;> decide
  have hF : GorensteinWalter.IsOddPrimePower (Nat.card F) := ⟨p, e, hp, ho, hn, hc⟩
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
    · exact hdiag hp ho he hc hlarge (f t) hout ht' hlinear
    · exact hfield hp ho he hc hlarge (f t) hout ht' hlinear
  obtain ⟨c, hgen⟩ := hmodel
  exact OuterGeneration.lift_semilinear_generators ρ (generalizedFitting G)
    h.faithful eL hF hcard ht htL c hgen

/-- Four conjugates of every outer involution generate a subgroup containing
the actual source component. The diagonal and field model premises are proved;
the witnesses lie in the original ambient group. -/
theorem source_outer_four_conjugates
    {p e : ℕ} (hp : p.Prime) (ho : Odd p) (he : e = 1 ∨ e = 2)
    (hlarge : 25 < p ^ e)
    (hm : ClassicalGroup.IsPSL
      ((generalizedFitting G) ⧸ center (generalizedFitting G)) 2 (p ^ e))
    (t : G) (htL : t ∉ generalizedFitting G) (ht : t ^ 2 = 1) :
    ∃ g : Fin 4 → G, generalizedFitting G ≤
      closure (Set.range fun i => g i * t * (g i)⁻¹) :=
  source_outer_four_conjugates_of_models ρ h
    OuterGeneration.diagonalFourGeneration OuterGeneration.fieldFourGeneration
    hp ho he hlarge hm t htL ht

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSize
