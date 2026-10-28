module
public import CFSG.Quasithin.Chapter10.SourceA5OffenderCentralization
public import CFSG.Quasithin.Chapter10.SourceA5OriginalModuleMarking.LocalRank
public import CFSG.Quasithin.ChapterE.Section03.Parameters.RankKernel

/-!
# Placement of a conjugate factor from its centralizing intersection

A noncentral element of the small intersection forces the original moved
factor to normalize the conjugate factor inside the conjugate maximal local
subgroup. The original factor has order at least sixteen, whereas the full
induced automizer has two-rank at most two. A nontrivial action kernel and
the original element-centralizer bound therefore place the entire conjugate
factor in M. This repairs the placement step of source 10.2.12 without using
the printed equality of the two different centralizers.

Chosen irreducibility and the earlier separate-factor and element-centralizer
inputs remain explicit. Source: Aschbacher–Smith, printed pp.754–755.
-/

public noncomputable section
open Subgroup Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterE
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
local instance (D : FundamentalSetup KnownSimple.IsKnownSimple T L) :
    IsElementaryAbelian 2 (⁅D.fullModule,L⁆ : Subgroup G) :=
  source_original_full_moved_elementary D

theorem source_a5_conjugate_moved_le_of_intersection_centralizes
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hi : (originalMovedQuotientAction D e).IsIrreducible)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G))
    (hcent : ∀ u ∈ ⁅D.fullModule,L⁆, u ≠ 1 → centralizer ({u} : Set G) ≤ D.maximalLocal)
    {g : G}
    (hsmall : subgroupCorank (D.fullModule.map (MulAut.conj g).toMonoidHom)
      (D.fullModule.map (MulAut.conj g).toMonoidHom ⊓ D.maximalLocal) ≤ 2)
    (hcentral : (⁅D.fullModule,L⁆).map (MulAut.conj g).toMonoidHom ⊓ D.maximalLocal ≤
      centralizer ((⁅D.fullModule,L⁆ : Subgroup G) : Set G)) :
    (⁅D.fullModule,L⁆).map (MulAut.conj g).toMonoidHom ≤ D.maximalLocal := by
  let W := ⁅D.fullModule,L⁆
  obtain ⟨b,hb,hbM,_,hbn⟩ :=
    source_a5_small_offender_exists_noncentral_normalizing_element D e hn hsmall
  have hWb : W ≤ centralizer ({b} : Set G) := by
    intro w hw
    exact mem_centralizer_singleton_iff.mpr ((hcentral ⟨hb,hbM⟩) w hw)
  have hWlocal := hWb.trans
    (source_nonnormal_conjugate_point_centralizer_normalizes D hn ht htn hcross hcent hb hbn)
  have hr := source_a5_original_local_primeRank_le_two D e hi
    (source_original_moved_stabilizer_le_component_normalizer D ht htn hcross)
  obtain ⟨w,hw,hwne,hwc⟩ := exists_nontrivial_centralizer_of_local_rank_map
    W W D.maximalLocal (MulAut.conj g) hWlocal hr
    (by have hh : 16 ≤ Nat.card W := source_a5_full_moved_card D e
        change 2 ^ 2 < Nat.card W
        omega)
  apply le_trans _ (hcent w hw hwne)
  intro p hp
  exact mem_centralizer_singleton_iff.mpr (hwc p hp)

end CFSG.Quasithin.Chapter10

