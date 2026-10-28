module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldParity.DisplacementThree
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalLinearFieldParityDegree

/-!
# The displacement source and both terminal parity branches

Under the original Hypothesis1223 and ChosenModule inputs, the completed
residual producer supplies maximality and nonfaithfulness. For every genuine
odd seed, the critical-pair degree reduction forces degree three, where the
literal quotient displacement is now at least nine. This discharges the
DisplacementSource interface with no constituent or action callback.

The final adapters combine that calculation with both proved terminal
critical-pair branches. They retain only the original seed, or
the displayed global TI and F.8 geometry. Constructing those hypotheses,
including the solvability consequence of 5.1.16(2), remains with final
assembly owner qt-d-1222-linear-field-parity. These conditional results do
not assert unconditional parity.

Source: Aschbacher–Smith 5.1.17, pp.640–642, and 12.2.2, p.795
(refs/quasithin.pdf).
-/

public noncomputable section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric LinearParity
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} {n : ℕ}
  (D : ChosenModule T L V)
include D

/-- The literal displacement source, with no constituent or action input remaining. -/
theorem rankOne_linear_displacement_source
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4) :
    DisplacementSource T L H n := by
  intro A B c ho s
  have hn3 := s.exponent_eq_three_of_odd D.sylow_normalizes_component hpsl c hn ho
  subst n
  have hi := D.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl
  obtain ⟨hm,hnf⟩ := D.rankOne_linear_residual_maximal_nonfaithful h hmany hH hlinear
  exact degree_three_largeDisplacement hi hH c hm hnf hlinear s

/-- With the displacement and both terminal branches proved, the original seed
is the sole remaining parity source. -/
theorem rankOne_even_exponent_of_seed
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hseed : OddSeedSource T L H n) : Even n :=
  D.rankOne_even_exponent_of_seed_and_displacement h hn hpsl hH hgen hseed
    (D.rankOne_linear_displacement_source h hmany hn hpsl hH hlinear)

/-- The original parity consumer now requires only global TI and F.8 geometry. -/
theorem rankOne_even_exponent_of_chosen_geometry
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hgeometry : ∀ A B : Subgroup G, CartanPair T L H A B → Odd n →
      (setup T L V H A).Hypothesis ∧
        ∀ g : G,
          (setup T L V H A).V₁ ⊓ (setup T L V H A).V₁.map (MulAut.conj g).toMonoidHom = ⊥ ∨
            (setup T L V H A).V₁.map (MulAut.conj g).toMonoidHom = (setup T L V H A).V₁) : Even n := by
  exact D.rankOne_even_exponent_of_chosen_geometry_and_displacement
    h hmany hn hpsl hH hgen hlinear hgeometry
    (D.rankOne_linear_displacement_source h hmany hn hpsl hH hlinear)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
