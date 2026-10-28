module

public import CFSG.Quasithin.Chapter16.Section01To02.CoverAndSylowElimination.CoverStructure
public import CFSG.Quasithin.Chapter16.Section01To02.CoverAndSylowElimination.CoverRank
public import CFSG.Quasithin.Chapter16.Section01To02.CoverAndSylowElimination.PairAction
public import CFSG.Quasithin.Chapter16.Section01To02.CoverAndSylowElimination.CoverPlacement
public import CFSG.Quasithin.Chapter16.Section01To02.CoverAndSylowElimination.Sylow
public import CFSG.Quasithin.Chapter16.Section01To02.CoverAndSylowElimination.SylowFinal

/-!
# Conditional elimination arguments for 16.2.11–16.2.12

The earlier local inputs retain the actual component closure, its normalizer,
the swapping element, noncontainment and the external involution. From the
precise Suzuki cover input we construct the elementary Ω₁(T_L), its central
index eight, and the starred normalizer-action assertion, with an explicit
inducing involution. The final cover rank contradiction, both I.7.6
centralizations, and both centralizer-kernel counting arguments are proved.
The two-component action and |T_L⟨z⟩| = 2|T_L| are also available.

The covered case is eliminated below, proving conditional 16.2.11. The
descendants prove 16.2.12 using I.7.6, the exact 16.1.6 innerness input and
the residual identities used in 16.2.9. The final assembly supplies trivial
center and tight embedding to that argument. The section owner must still
construct the earlier geometry and discharge the intrinsic model inputs.
This module does not assert the final normality theorem 16.2.4.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, p.1176.
-/

public section
namespace CFSG.Quasithin.Chapter16.CoverAndSylowElimination

open Subgroup Theory.GroupTheory

variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {z u : G} {L : Subgroup G}

/-- The nontrivial Suzuki cover is impossible in the actual local geometry.
The intrinsic inputs are precisely those of I.2.2(4) and the Suzuki
automorphism calculation; the placement is constructed, not assumed. -/
theorem exclude_suzuki_cover (h : EarlierConclusions T z u L)
    (d : SuzukiCoverInput T L) : center L = ⊥ := by
  by_contra hc
  let hs := d.coverStructure h.localSetup
  exact not_coverPlacement h hc d hs (hs.placement h)

/-- Conditional Lemma 16.2.11. The center/core identity comes from (E1),
`cover_data` combines the nonsimple alternative of 16.2.5 with the precise
intrinsic Suzuki inputs, and the final disjunction is 16.2.8(2). The owner
of the source theorem must discharge all three earlier inputs. -/
theorem lemma_16_2_11_of_inputs (h : EarlierConclusions T z u L)
    (hcenter : center L = pCore 2 L)
    (cover_data : pCore 2 L ≠ ⊥ → SuzukiCoverInput T L)
    (tight_or_cover : IsTightlyEmbedded L ∨
      (pCore 2 L ≠ ⊥ ∧ Nonempty ((L ⧸ pCore 2 L) ≃*
        BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 1))) :
    pCore 2 L = ⊥ ∧ IsTightlyEmbedded L := by
  have hc : pCore 2 L = ⊥ := by
    by_contra hn
    exact hn (hcenter ▸ exclude_suzuki_cover h (cover_data hn))
  exact ⟨hc, tight_or_cover.resolve_right (fun he => he.1 hc)⟩

open ChapterI.Section06To08

/-- Assemble both elimination lemmas, discharging the trivial-center and
tight-embedding premises of 16.2.12 by the proved 16.2.11 implication.
The residual identities are those used in 16.2.9(2), and the model innerness
premise is 16.1.6 with its A₆ exception excluded by the 16.2.5 list. -/
theorem lemma_16_2_11_12_of_inputs (h : EarlierConclusions T z u L)
    (hcenter : center L = pCore 2 L)
    (cover_data : pCore 2 L ≠ ⊥ → SuzukiCoverInput T L)
    (tight_or_cover : IsTightlyEmbedded L ∨
      (pCore 2 L ≠ ⊥ ∧ Nonempty ((L ⧸ pCore 2 L) ≃*
        BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 1)))
    (p : ℕ) (hself : primeToResidual p (localComponentClosure z L) = ⊤)
    (hres : (primeToResidual p (localComponentNormalizer z L)).map
      (localComponentNormalizer z L).subtype = localComponentClosure z L)
    (hinner : SylowCentralizingInner L) :
    pCore 2 L = ⊥ ∧ IsTightlyEmbedded L ∧
      {S : Subgroup G | (∃ g : G, conjSubgroup (componentSylow T L) g = S) ∧ S ≤ T} =
        {componentSylow T L, componentSylow T (conjSubgroup L u)} := by
  obtain ⟨hc, ht⟩ := lemma_16_2_11_of_inputs h hcenter cover_data tight_or_cover
  exact ⟨hc, ht, lemma_16_2_12_of_inputs h ht (hcenter.trans hc) p hself hres hinner⟩

end CFSG.Quasithin.Chapter16.CoverAndSylowElimination
