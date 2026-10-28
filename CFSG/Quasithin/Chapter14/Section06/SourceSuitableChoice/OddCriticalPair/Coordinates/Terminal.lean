module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddCriticalPair.Coordinates.CoreRank
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddCriticalPair.Fusion.Source

/-!
# Applying the orthogonal core rank at the terminal source surface

The original core of Mc lies in Q_H. Movement of the same suitable vector
therefore supplies the core-centralizer rank bound. Combining this with the
proved crossing and parabolic construction removes that numerical premise
from the literal terminal consumer.

The residual seed coordinates and critical-pair construction still belong
to qt-e-suitable-orthogonal-marking. Earlier-source final discharge remains
with qt-e-suitable-existence. This conditional application is not the full
14.6.17 source theorem.
Source: Aschbacher--Smith 14.6.17--18, printed pp.1035--1036.
-/

public section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (d : SourceOrthogonalFourAction H (conjugateSpanBy (localModule T M) H)
      (centralInvolutions T) (H.pCoreIn 2))
    (critical : SourceOrthogonalCriticalPair d Mc)
    (u : G) (hu : u ∈ d.plane critical.first) (huz : u ∉ centralInvolutions T)
    (hindex : (suitableQuotientCentralizer
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) u).relIndex
        (T : Subgroup G) = 2)
    (hmove : ¬ Mc.pCoreIn 2 ≤ centralizer ({u} : Set G))
    (hproduct : ∀ t ∈ (T : Subgroup G), t ∉ suitableQuotientCentralizer
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) u →
        ¬ Mc.pCoreIn 2 ≤ centralizer ({u * (MulAut.conj t⁻¹) u} : Set G))
    (hU3 : Mc ⊓ normalizer (suitableQuotientCentralizer
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) u : Set G) =
        (T : Subgroup G))


include hG hempty hM hunique hmany hcard e hab hH hu hmove

/-- The literal module-rank premise of the terminal theorem follows from the
orthogonal action and the same suitable vector's movement of O₂(Mc). -/
theorem source_orthogonal_module_rank :
    4 ≤ Nat.log 2 ((centralizer (H.pCoreIn 2 : Set G)).relIndex
      (conjugateSpanBy (localModule T M) H)) := by
  let D : ChapterF.Section09.Setup G :=
    ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,H⟩
  let h : D.Hypothesis := source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH
  have hHMc : H ≤ Mc := by
    have he := (Section02.source_lemma_14_2_3 hG T hempty hM hunique hmany hcard e
      H hH.1 hH.2).1
    exact (show Mc ∈ maximalTwoLocalOvergroups H from he ▸ Set.mem_singleton Mc).2
  have hTMc : (T : Subgroup G) ≤ Mc := hH.1.2.trans hHMc
  have hQMcT : Mc.pCoreIn 2 ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTMc] using
      pCoreIn_le_sylow Mc (T.subtype hTMc)
  have hQle : Mc.pCoreIn 2 ≤ H.pCoreIn 2 :=
    (le_inf (hQMcT.trans hH.1.2) le_rfl).trans (inf_pCoreIn_le_of_le 2 hHMc)
  exact OddCriticalPair.orthogonal_module_rank (D := D) h d u (d.plane_le critical.first hu)
    (fun hc => hmove (hQle.trans hc))

include huz hindex hproduct hU3

/-- The complete crossing and numerical applications on the same chosen u.
Only the residual seed coordinates remain for the internal coordinate chain;
this theorem does not assert the existence of those coordinates. -/
theorem source_terminal_witness_of_orthogonal_coordinates
    (coordinates : SourceResidualSpanCoordinates (localModule T M) (centralInvolutions T)
      ((pResidual 2 ((source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab
        H hH).kernel (zpowers u))).map
        ((source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab
          H hH).kernel (zpowers u)).subtype)) :
    SourceTerminalWitness hG T hempty hM hunique hmany hcard e hab := by
  exact source_terminal_witness_of_orthogonal_fusion hG T hempty hM hunique hmany
    hcard e hab H hH d critical u hu huz hindex hmove hproduct hU3
    (source_orthogonal_module_rank hG T hempty hM hunique hmany hcard e hab H hH
      d critical u hu hmove) coordinates

end CFSG.Quasithin.Chapter14.Section06
