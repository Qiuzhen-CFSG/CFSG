module

public import CFSG.Quasithin.ChapterE.Section05.RankBridge
public import CFSG.Quasithin.ChapterE.Section05.GenerationFromCenter.MinimalMembers
public import CFSG.Quasithin.ChapterE.Section05.GenerationFromCenter.Component
public import CFSG.Quasithin.ChapterE.Section05.GenerationFromCenter.OddMinimal

/-!
# Generation from E.5.1 center containment

The E2 structural branch is proved in `GenerationFromCenter.Component`.
The finite-lattice reduction selects minimal E-members outside the proposed
generating subgroup, so no centralizer bound on arbitrary E1 members is used.
For each selected member, either its residual centralizes the two-core and the
rank-cover theorem applies, or the E.5.1 center-containment hypothesis gives
the normal elementary overgroup used by the conjugate-centralizer cover.

The odd-prime reduction is proved in `GenerationFromCenter.OddMinimal`:
reducibility on the odd Frattini section would generate a minimal escaping
member by proper E-members. Thus both structural branches are discharged in
`thompsonCentralizerGenerators_eq_top_of_center`. Only the E.5.1
center-containment hypothesis remains explicit; the unconditional numbered
E.5.2 theorem belongs to the section assembly.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, E.5.2, printed p.243.
-/

open Subgroup Stellmacher CFSG.Quasithin.ChapterB
namespace CFSG.Quasithin.ChapterE
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem map_residual_le_centralizer_of_intrinsic {K : Subgroup G}
    (h : pResidual 2 K ≤ centralizer (pCore 2 K : Set K)) :
    (pResidual 2 K).map K.subtype ≤ centralizer ((pCore 2 K).map K.subtype : Set G) := by
  exact (map_mono h).trans (map_centralizer_le_centralizer_image _ _)

/-- Assembly with the minimal odd-member reduction supplied explicitly. -/
public theorem thompsonCentralizerGenerators_eq_top_of_center_and_minimal_odd
    (P : Sylow 2 G) (i j : ℕ) (hij : i + j < twoRank (P : Subgroup G))
    (hgen : IsEGenerated j G)
    (hcenter : ∀ A K : Subgroup G, A ∈ thompsonFamily (P : Subgroup G) i →
      IsEMemberAt j (P : Subgroup G) A K →
      WeakClosureCentralizerBound (P : Subgroup G) A K →
      higherThompsonCenter (P : Subgroup G) (i + j) ≤
        omegaOneCenterAmbient (higherThompsonCore (P : Subgroup G) K (i + j)))
    (hodd : ∀ A K : Subgroup G, A ∈ thompsonFamily (P : Subgroup G) i →
      IsMinimalEscapingEMember j (P : Subgroup G) A
        (thompsonCentralizerGenerators (P : Subgroup G) i j) K →
      ECaseOdd A K →
      pResidual 2 K ≤ centralizer (pCore 2 K : Set K) ∨
        pResidual 2 K ⊓ centralizer (pCore 2 K : Set K) ≤ weakClosureOddRadical K) :
    thompsonCentralizerGenerators (P : Subgroup G) i j = ⊤ := by
  apply eq_top_of_minimal_thompson_residuals P i j hgen _ le_sup_left
  intro A K hA hmin
  have hK : IsEMemberAt j (P : Subgroup G) A K := hmin.1.1
  have hcases : pResidual 2 K ≤ centralizer (pCore 2 K : Set K) ∨
      WeakClosureCentralizerBound (P : Subgroup G) A K := by
    rcases hK.1.2.2.2.2.2 with ho | hc
    · exact (hodd A K hA hmin ho).imp_right fun h => Or.inl ⟨ho, h⟩
    · exact hc.residual_centralizer_dichotomy.imp_right fun h => Or.inr ⟨hc, h⟩
  rcases hcases with hc | hb
  · exact residual_le_generators_of_centralizes_core P i j hij A K hA hK.core_rank_le
      (map_residual_le_centralizer_of_intrinsic hc)
  · exact residual_le_generators_of_core_center P i j hij A K hA hK
      (hcenter A K hA hK hb)

/-- The structural generation argument of E.5.2, conditional only on the
E.5.1 center-containment schema. Minimality supplies the odd-prime centralizer
bound, and the component-orbit argument supplies the E2 bound. -/
public theorem thompsonCentralizerGenerators_eq_top_of_center
    (P : Sylow 2 G) (i j : ℕ) (hj : 0 < j)
    (hij : i + j < twoRank (P : Subgroup G)) (hgen : IsEGenerated j G)
    (hcenter : ∀ A K : Subgroup G, A ∈ thompsonFamily (P : Subgroup G) i →
      IsEMemberAt j (P : Subgroup G) A K →
      WeakClosureCentralizerBound (P : Subgroup G) A K →
      higherThompsonCenter (P : Subgroup G) (i + j) ≤
        omegaOneCenterAmbient (higherThompsonCore (P : Subgroup G) K (i + j))) :
    thompsonCentralizerGenerators (P : Subgroup G) i j = ⊤ :=
  thompsonCentralizerGenerators_eq_top_of_center_and_minimal_odd P i j hij hgen hcenter
    (minimal_odd_thompson_centralizer_dichotomy P i j hj hij)

end CFSG.Quasithin.ChapterE
