module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Solvable.TwoFactors.MarkedGeometry
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Component.ModelExtension.SourceSetup

/-!
# The two-factor contradiction in the standing source configuration

The source setup retains Hypothesis 13.3.1, the counterexample exclusions,
the actual A₆ quotient and natural flag, and the abelian span of 13.8.2.
The earlier marked local alternatives are stated universally before H and
the transvection are selected. Their inputs are the actual standing setup;
no placement or cubic-action conclusion is included.

Quasithinness bounds the three-rank of N_G(V₁), hence of H. The marked
geometry theorem then constructs the invariant cubic subgroup and proves
the contradiction when the actual B.1.8 factor count is two. The parent
owns construction of those factors and the remaining one-factor branch.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.5.2(1),(3), printed pp.915–916; proof of 13.8.5, p.947 (PDF p.964).
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter13.Section08
open Components.Swapped.LinearThree.MarkedAutomizer
namespace CFSG.Quasithin.Chapter13.Section08.TransvectionRecognition.Solvable.TwoFactors
variable {G : Type*} [Group G] [Finite G]

open TransvectionRecognition.Component.ModelExtension

/-- The earlier local alternatives, with an actual equivariant natural-module
marking in each case. This is the consumed content of 13.5.2(1),(3) and
§13.2 before Notation 13.2.1, universally stated before choosing H or a
transvection. It is an earlier-theorem input, not a proof of those results. -/
def EarlierMarkedModels : Prop :=
  ∀ (T : Sylow 2 G) (L V V₁ V₂ V₃ M G₁ : Subgroup G)
    (s : LocalSetup T L V V₁ V₂ V₃ M G₁),
    Nonempty (SimplePointModel L V (le_sup_left.trans s.normalizes_V)) ∨
      Nonempty (CoverPointModel L V (le_sup_left.trans s.normalizes_V))

/-- Quasithinness applies to the genuine two-local N_G(V₁), and hence to H.
The two-local witness uses the actual order-two marked line. -/
theorem source_threeRank_le_two {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}
    (s : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (hH : H ∈ Source.Hz (sourceOne L T V₁) T G₁ M) : primeRank 3 H ≤ 2 := by
  have hne : V₁ ≠ ⊥ := by
    intro h
    have hc := s.line_card
    rw [h, card_bot] at hc
    omega
  have hlocal : IsTwoLocal G₁ := ⟨V₁, hne,
    IsPGroup.of_card (n := 1) (by simpa only [pow_one] using s.line_card), s.first_normalizer⟩
  exact (primeRank_mono 3 hH.2.1).trans
    ((Theory.GroupTheory.isQuasithin_iff_twoLocal.mp s.counterexample.qtke.quasithin)
      G₁ hlocal 3 (by decide) (by decide))

/-- The complete two-factor contradiction under the standing §13.8 setup.
The only earlier-theorem input is the universal marked local model alternative;
all its applicability conditions are supplied by the standing setup. In
particular no placement, invariant cubic subgroup or factor-transitivity
conclusion is assumed. The solvable-factor witness remains the explicit
conditional branch input, constructed by the parent from B.1.8. -/
theorem source_two_factors_impossible (T : Sylow 2 G)
    {L V V₁ V₂ V₃ M G₁ H : Subgroup G}
    (s : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (earlier : EarlierMarkedModels (G := G))
    (hH : H ∈ Source.Hz (sourceOne L T V₁) T G₁ M)
    [(V₁.subgroupOf (Source.UH H V₃)).Normal]
    [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (_hρ : IsConjugation H V₃ V₁ ρ)
    (t : Source.Hstar H) (ht : IsTransvection ρ t)
    (d : ChapterB.SolvableFFFactors (ρ.comp (normalClosure ({t} : Set (Source.Hstar H))).subtype))
    (hJ : offenderSubgroup (ρ.comp (normalClosure ({t} : Set (Source.Hstar H))).subtype) = ⊤)
    (hc : d.count = 2) : False := by
  exact two_factors_impossible_of_marked_models T hH (le_sup_left.trans s.normalizes_V)
    (earlier T L V V₁ V₂ V₃ M G₁ s) s.normalizes_L s.line_stable
    ((s.line_le_plane.trans s.plane_le_seed).trans s.seed_le) s.line_card
    (source_threeRank_le_two s hH) ρ t ht d hJ hc

end CFSG.Quasithin.Chapter13.Section08.TransvectionRecognition.Solvable.TwoFactors

end
