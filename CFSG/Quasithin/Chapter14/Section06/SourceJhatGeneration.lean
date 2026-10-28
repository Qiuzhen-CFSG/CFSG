module
public import CFSG.Quasithin.Chapter14.Section06.SourceMovedModule
public import CFSG.Quasithin.ChapterD.Section02.StarredConjugacy
public import Theory.GroupTheory.GeneralizedFitting.ResidualCentralizer
/-!
# The actual minimum-actor subgroup in the primitive plane branch

Uniqueness of the literal quotient action transports the proved quadratic
bound to any supplied action. Minimum cubic actors thus exist and their
normal span is nontrivial. The primitive two-residual is minimal normal
and contains its centralizer, so that normal span contains the residual.
The original mapped Sylow subgroup consequently supplements Jhat.

Source: Aschbacher--Smith, 14.6.12(2), printed p.1031. This removes the
actual source-generation input for the D.2.17 application; it does not
assume or conclude the later dihedral decomposition.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam
variable {G : Type*} [Group G] [Finite G]
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))

include hG hempty hM hu hmany hcard e hab




theorem source_rankTwo_quadratic_bound_of_action
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)]
    (a : LocalQuotientAction H (conjugateSpanBy (localModule T M) H) (centralInvolutions T)) :
    quadraticRatio a.representation ≤ 2 := by
  obtain ⟨hU,b,hb⟩ := source_rankTwo_quadratic_bound hG T hempty hM hu hmany hcard e hab H hH
  rw [a.representation_eq b]
  exact hb

theorem source_solvable_minimal_residual_le_Jhat
    (J : Subgroup G) (hJ : J ∈ Chapter3.HStar (T : Subgroup G) M)
    (hs : Group.IsSolvable J)
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) J)]
    (a : LocalQuotientAction J (conjugateSpanBy (localModule T M) J) (centralInvolutions T)) :
    pResidual 2 (J ⧸ pCore 2 J) ≤ ChapterD.Jhat a.representation := by
  obtain ⟨p,_hp,_hE,_hbound,_hne,hmin⟩ := source_solvable_minimal_elementary_residual
    hG T hempty hM hu hmany hcard e hab J hJ hs
  let P := pResidual 2 (J ⧸ pCore 2 J)
  let N := ChapterD.Jhat a.representation
  have hq : cubicRatio a.representation ≤ 2 := (cubicRatio_le_quadraticRatio _).trans
    (source_rankTwo_quadratic_bound_of_action hG T hempty hM hu hmany hcard e hab J hJ.1 a)
  obtain ⟨A,hA⟩ := (ChapterD.QhatStar_nonempty_iff a.representation).mpr hq
  have hNne : N ≠ ⊥ := by
    intro hz
    exact hA.1.2.1.1 (le_bot_iff.mp ((le_sSup hA).trans hz.le))
  let : N.Normal := ChapterD.Jhat_normal a.representation
  rcases hmin (P ⊓ N) inferInstance inf_le_left with hz | he
  · have hc : ⁅N,P⁆ = ⊥ := commutator_eq_bot_of_disjoint ((disjoint_iff.mpr hz).symm)
    have hNP : N ≤ P := (commutator_eq_bot_iff_le_centralizer.mp hc).trans
      (centralizer_pResidual_le_of_pCore_eq_bot (pCore_quotient_pCore_eq_bot 2))
    exact (hNne ((inf_eq_right.mpr hNP).symm.trans hz)).elim
  · exact he.symm.le.trans inf_le_right

theorem source_solvable_minimal_Jhat_sylow
    (J : Subgroup G) (hJ : J ∈ Chapter3.HStar (T : Subgroup G) M)
    (hs : Group.IsSolvable J)
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) J)]
    (a : LocalQuotientAction J (conjugateSpanBy (localModule T M) J) (centralInvolutions T)) :
    ChapterD.Jhat a.representation ⊔
      ((T : Subgroup G).subgroupOf J).map (QuotientGroup.mk' (pCore 2 J)) = ⊤ := by
  have hPN := source_solvable_minimal_residual_le_Jhat
    hG T hempty hM hu hmany hcard e hab J hJ hs a
  have hgen := pResidual_sup_sylow_eq_top
    ((T.subtype hJ.1.1.2).mapSurjective (QuotientGroup.mk'_surjective (pCore 2 J)))
  exact top_unique (hgen ▸ sup_le_sup_right hPN _)

end CFSG.Quasithin.Chapter14.Section06
