module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.Defs
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.FactorBlockInvolutionFusion
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.FactorOutsideInvolution
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.ParabolicIndex
public import CFSG.Quasithin.Chapter14.Section06.SourceClassificationInputs

/-!
# Final transfer for the E-specific nonabelian reduction

Core collapse Q=U changes the proved index |T:RQ|=2 into |T:RU|=2.
The original cubic action supplies an outside involution, and the marked
split A₆ block fuses every inside involution to the original point. Original
14.3.21(2) separates these classes, contradicting Thompson transfer in G.

The rank-two application retains the selected M, Mc and conjugate span.
Solvability, factor self-centralization, outside nonfusion and the conditional
core-collapse argument remain explicit independent source obligations. Thus
this module proves the final implication, not unconditional 14.3.16.

Source: Aschbacher--Smith, 14.3.15--22 and 14.6.25, printed pp.994--999,1042.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Recognition
variable {G : Type*} [Group G] [Finite G]

/-- The last paragraph of 14.3.16 with index, outside existence and inside
fusion discharged on the original subgroups. -/
theorem false_of_core_eq_span
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)]
    (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P (sourceResidual M Mc)) (hgH : g ∉ F.H)
    (hs : Group.IsSolvable F.TerminalHdot)
    (hQ : F.H.pCoreIn 2 = F.U)
    (hout : OutsidePointNonfusion F (sourceResidual M Mc)) : False := by
  have hi := (source_parabolic_core_sylow_index_of_solvable
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs).2
  rw [hQ] at hi
  obtain ⟨t, ht, ht2, htout⟩ := source_outside_involution_of_solvable
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hi
  have hzcard : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 (by decide)
  obtain ⟨z, hz1, _⟩ := (Nat.card_eq_two_iff' (1 : F.Vi 1)).mp hzcard
  have hzne : (z : G) ≠ 1 := fun he => hz1 (Subtype.ext he)
  apply source_false_of_ru_fusion_of_solvable
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
    z z.property hzne hi ⟨t, ht, ht2, htout⟩
  intro x hx hx2 hxout
  apply hout z z.property hzne x hx hx2
  simpa only [hQ] using hxout

/-- The source nonabelian implication used by 14.6.25. Its four extra
premises are independent source contracts, all still to be discharged. The
core-collapse producer may use the two earlier local conclusions. -/
theorem source_theoremE_of_nonabelian_of_inputs
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hrank : RankTwoHypothesis KnownSimple.IsKnownSimple T (sourceResidual M Mc) M)
    (hsolvable : ¬ ClassificationModels.IsTheoremEModel G →
      ∀ (F : InvariantFlag T (rankTwoSeed T M) 2), ¬ IsMulCommutative F.U →
      ∀ g ∈ F.P (sourceResidual M Mc), g ∉ F.H → Group.IsSolvable F.TerminalHdot)
    (hself : ¬ ClassificationModels.IsTheoremEModel G →
      ∀ (F : InvariantFlag T (rankTwoSeed T M) 2), ¬ IsMulCommutative F.U →
      ∀ g ∈ F.P (sourceResidual M Mc), g ∉ F.H → Group.IsSolvable F.TerminalHdot →
        FactorSelfCentralizing F (sourceResidual M Mc))
    (hnonfusion : ¬ ClassificationModels.IsTheoremEModel G →
      ∀ (F : InvariantFlag T (rankTwoSeed T M) 2), ¬ IsMulCommutative F.U →
      ∀ g ∈ F.P (sourceResidual M Mc), g ∉ F.H → Group.IsSolvable F.TerminalHdot →
        OutsidePointNonfusion F (sourceResidual M Mc))
    (hcollapse : ¬ ClassificationModels.IsTheoremEModel G →
      ∀ (F : InvariantFlag T (rankTwoSeed T M) 2), ¬ IsMulCommutative F.U →
      ∀ g ∈ F.P (sourceResidual M Mc), g ∉ F.H → Group.IsSolvable F.TerminalHdot →
        FactorSelfCentralizing F (sourceResidual M Mc) →
        OutsidePointNonfusion F (sourceResidual M Mc) → F.H.pCoreIn 2 = F.U)
    (hne : ¬ IsMulCommutative (conjugateSpanBy (localModule T M) Mc)) :
    ClassificationModels.IsTheoremEModel G := by
  classical
  by_contra hnot
  obtain ⟨hcard, ⟨e⟩⟩ := Section06.source_plane_of_rankTwo hrank
  obtain ⟨hs, F, _, _, hU, _, _, g, hgP, hgH, _⟩ :=
    source_terminal_hypothesis hG T hempty hM hu hmany hcard e hne
  let := hs
  have hneF : ¬ IsMulCommutative F.U := hU ▸ hne
  have hsol := hsolvable hnot F hneF g hgP hgH
  have hselfF := hself hnot F hneF g hgP hgH hsol
  have hout := hnonfusion hnot F hneF g hgP hgH hsol
  have hQ := hcollapse hnot F hneF g hgP hgH hsol hselfF hout
  exact false_of_core_eq_span hG T hempty hM hu hmany hcard e hnot F hneF
    g hgP hgH hsol hQ hout

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction
