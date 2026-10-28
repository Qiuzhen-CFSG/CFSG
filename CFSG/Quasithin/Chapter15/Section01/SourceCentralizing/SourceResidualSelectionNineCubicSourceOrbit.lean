module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionNineCubicStarGeometry
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionNineCubicOrbit
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.NormalizerAction
public import Theory.GroupTheory.CentralizerModulo.ConjugateSpan
public import Theory.GroupTheory.ConjugateSpanSupplement

/-!
# The original FF module is the original central-seed orbit

The normalizer Sylow subgroup fixes the original central seed and normalizes
the component. Adding that Sylow subgroup to the acting component therefore
does not enlarge the seed's conjugate span. The literal FF normal closure
in L N_S(L) is this same ambient span.

When the original C.2.7 radical contains the seed, taking its normal closure
in LQ1 gives the identical subgroup. The two ambient joins and both original
subtype maps are retained; no core kernel or whole-core equality is assumed.

Source: Aschbacher--Smith 15.1.20(2), p.1094, and B.2.14, p.78.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open ChapterC ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open Section03 Section03.InitialSource
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- The actual FF module in the Sylow normalizer is the component orbit of
the original central-involution seed, with its ambient embedding unchanged. -/
theorem normalizerModule_eq_original_seed_span (d : CaseIComponentData T M Mc V)
    (hZ : centralInvolutions T ≤ d.normalizerSylow d.L) :
    (d.normalizerModule d.L).map (d.L ⊔ d.normalizerSylow d.L : Subgroup G).subtype =
      conjugateSpanBy (centralInvolutions T) d.L := by
  rw [normalizerModule,normalClosure_subgroupOf_eq_conjugateSpanBy _ _
    (hZ.trans le_sup_right),map_subgroupOf_eq_of_le
      (conjugateSpanBy_le_self (hZ.trans le_sup_right))]
  exact conjugateSpanBy_sup_of_normalizes_seed _ _ _
    ((inf_le_left.trans d.S_le_T).trans
      ((le_centralizer_iff.mp (centralInvolutions_le_centralizer_sylow T)).trans
        (Subgroup.centralizer_le_normalizer _))) inf_le_right

/-- The source radical and Sylow normalizer produce the same actual seed
orbit, even though the radical need not be Sylow in its component join. -/
theorem original_seed_orbit_eq_normalizerModule (d : CaseIComponentData T M Mc V)
    (hi : Input KnownSimple.IsKnownSimple d.G1 d.Q1 d.MZ d.L)
    (hQS : d.Q1 ≤ d.S) (hZQ : centralInvolutions T ≤ d.Q1) :
    (normalClosure ((centralInvolutions T).subgroupOf (d.L ⊔ d.Q1) :
      Set (d.L ⊔ d.Q1 : Subgroup G))).map (d.L ⊔ d.Q1 : Subgroup G).subtype =
        (d.normalizerModule d.L).map (d.L ⊔ d.normalizerSylow d.L : Subgroup G).subtype := by
  rw [d.normalizerModule_eq_original_seed_span
    (le_inf (hZQ.trans hQS) (hZQ.trans hi.normalizes)),
    normalClosure_subgroupOf_eq_conjugateSpanBy _ _ (hZQ.trans le_sup_right),
    map_subgroupOf_eq_of_le (conjugateSpanBy_le_self (hZQ.trans le_sup_right))]
  exact conjugateSpanBy_sup_of_normalizes_seed _ _ _
    ((hQS.trans d.S_le_T).trans
      ((le_centralizer_iff.mp (centralInvolutions_le_centralizer_sylow T)).trans
        (Subgroup.centralizer_le_normalizer _))) hi.normalizes

/-- The original FF module and full star module have the same moved part
on the actual cubic source, once the original seed's placement and movement
are supplied. Neither underlying module is replaced by the other. -/
theorem normalizerModule_moved_eq_starV (d : CaseIComponentData T M Mc V)
    (hi : Input KnownSimple.IsKnownSimple d.G1 d.Q1 d.MZ d.L)
    (hms : Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS.SmallMSPair
      KnownSimple.IsKnownSimple d.L d.Q1)
    (t : (d.L ⧸ centralPreimage (pCore 2 d.L)) ≃* alternatingGroup (Fin 6))
    (hz : Nat.card (center (d.L ⧸ pCore 2 d.L)) = 3)
    (hQS : d.Q1 ≤ d.S) (hZQ : centralInvolutions T ≤ d.Q1)
    (hZstar : centralInvolutions T ≤
      (starV d.L d.Q1).map (d.L ⊔ d.Q1 : Subgroup G).subtype)
    (hmove : ⁅centralInvolutions T,d.L⁆ ≠ ⊥) :
    ⁅(d.normalizerModule d.L).map
      (d.L ⊔ d.normalizerSylow d.L : Subgroup G).subtype,d.L⁆ =
        ⁅(starV d.L d.Q1).map (d.L ⊔ d.Q1 : Subgroup G).subtype,d.L⁆ := by
  have he := smallMS_cubic_seed_normalClosure_moved_eq_map hms t hz
    (centralInvolutions T) hZstar hmove
  rwa [d.original_seed_orbit_eq_normalizerModule hi hQS hZQ] at he

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

namespace CFSG.Quasithin.Chapter15.Section01
open ChapterC ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
variable {G : Type*} [Group G] [Finite G]

/-- The original Nine central seed generates the full initial moved part
of the cubic star module through its literal FF normal closure. -/
theorem PreparedChosenModule.nine_original_FF_moved_eq_starV
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V) (hfull : V = localModule T M)
    (h9 : letI := h.elementary
      SourceCases.Nine (imageRepresentation M V h.normalized)
        (((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict))
    (hstrict : ((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
      (actionHom M V h.normalized).rangeRestrict <
        ((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict)
    (d : CaseIComponentData T M Mc V) (hr : d.row = .four)
    (g : d.ExchangedPlaneGeometry) (s : d.PreExclusionSource h.normalized 3)
    (hi : Input KnownSimple.IsKnownSimple d.G1 d.Q1 d.MZ d.L)
    (hms : SmallMSPair KnownSimple.IsKnownSimple d.L d.Q1)
    (t : (d.L ⧸ centralPreimage (pCore 2 d.L)) ≃* alternatingGroup (Fin 6))
    (hz : Nat.card (center (d.L ⧸ pCore 2 d.L)) = 3) :
    ⁅(d.normalizerModule d.L).map
      (d.L ⊔ d.normalizerSylow d.L : Subgroup G).subtype,d.L⁆ =
        ⁅(starV d.L d.Q1).map (d.L ⊔ d.Q1 : Subgroup G).subtype,d.L⁆ := by
  obtain ⟨_,_,hgen,_,hEQ⟩ := h.nine_marked_core_geometry
    hG T hempty hM hmany hJ hu hne hfull h9 hstrict d hr g
  obtain ⟨hEV,_,_,_,hm⟩ := h.nine_marked_star_geometry
    hG T hempty hM hmany hJ hu hne hfull h9 hstrict d hr g hi
  have hZE : centralInvolutions T ≤ thompsonFixed T V := le_sup_right.trans_eq hgen
  have hZQ : centralInvolutions T ≤ d.Q1 := fun z hz =>
    ((mem_omegaOneCenterAmbient_iff _ _).mp (hEQ (hZE hz))).1
  exact d.normalizerModule_moved_eq_starV hi hms t hz
    (d.catalogue_radical_le_sylow s.centralizer_sylow hu) hZQ (hZE.trans hEV)
    (by simpa only [commutator_comm] using hm)

end CFSG.Quasithin.Chapter15.Section01
