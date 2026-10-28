module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.ComponentModules.PairMarkedBaumann
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.ComponentModules.PairSeedNonzero
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.ComponentModules.PairContradiction
/-!
The marked natural product supplies every action, seed-coordinate and Baumann premise of the original paired Borel contradiction. This is the final application of the B.5 natural-model witnesses to 13.6.14; the witnesses are produced by the component-model branch.

Source: Aschbacher--Smith 13.6.14, printed pp.929--930.
-/
public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
open A5Module ComponentReduction InitialSieve
open ComponentElimination.SourceContainment.LinearThree.CentralAction.ModuleAlternatives
open ChapterB ChapterB.SourceInduction ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ : Subgroup G}

theorem pair_marked_contradiction_original_source
    (d : FlagSource T L V V₁ V₂) (V₃ : Subgroup G)
    (earlier : EarlierLocal T L (normalizer (L : Set G)) V V₂ V₃ (markedZ d.flag.module))
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hcounter : IsA5Counterexample G) (hfusion : ControlsFusionOfZ d.flag.module)
    (K : Subgroup G)
    [IsElementaryAbelian 2 (WK K L T (markedZ d.flag.module) (markedV d.flag.module))]
    (hK : K ∈ Yz L T (markedZ d.flag.module) (markedV d.flag.module))
    (hn : ¬ Tv T (markedV d.flag.module) ≤ normalizer (K : Set G))
    (hL : Tv T (markedV d.flag.module) ≤ normalizer (Lv L (markedV d.flag.module) : Set G))
    (hz : Tv T (markedV d.flag.module) ≤ centralizer ({markedZ d.flag.module} : Set G))
    (hLv : plusImage K L T (markedZ d.flag.module) (markedV d.flag.module) hL hz
      (Lv L (markedV d.flag.module)) ≤
        plusImage K L T (markedZ d.flag.module) (markedV d.flag.module) hL hz
          (Kminus K T (markedV d.flag.module)))
    (a : SourceTwoFactorCase ((wkRepresentation K L T (markedZ d.flag.module)
      (markedV d.flag.module) hL hz).comp (offenderSubgroup
        (wkRepresentation K L T (markedZ d.flag.module) (markedV d.flag.module) hL hz)).subtype))
    (F : BinaryField) (hF : 4 ≤ Nat.card F.Carrier) (c : a.MarkedProduct (linearNatural F 2))
    (hI : offenderSubgroup (wkRepresentation K L T (markedZ d.flag.module)
      (markedV d.flag.module) hL hz) =
      plusImage K L T (markedZ d.flag.module) (markedV d.flag.module) hL hz
        (Kminus K T (markedV d.flag.module)))
    (t : G) (ht : t ∈ Tv T (markedV d.flag.module))
    (hex : let := offenderSubgroup_normal (wkRepresentation K L T (markedZ d.flag.module)
        (markedV d.flag.module) hL hz)
      let tA : plusActor K L T (markedV d.flag.module) :=
        ⟨t,(show Tv T (markedV d.flag.module) ≤ plusActor K L T (markedV d.flag.module)
          from le_sup_right) ht⟩
      a.first.map (MulAut.conjNormal (plusMk K L T (markedZ d.flag.module)
        (markedV d.flag.module) hL hz tA)).toMonoidHom = a.second ∧
      a.second.map (MulAut.conjNormal (plusMk K L T (markedZ d.flag.module)
        (markedV d.flag.module) hL hz tA)).toMonoidHom = a.first) : False := by
  let z := markedZ d.flag.module
  let v := markedV d.flag.module
  let α := wkRepresentation K L T z v hL hz
  let I := offenderSubgroup α
  let C := plusImage K L T z v hL hz (Kminus K T v)
  let e := (MulEquiv.subgroupCongr hI.symm).trans c.action.groupEquiv
  obtain ⟨lc⟩ := localConfiguration_of_earlier_source d (normalizer (L : Set G)) V₃
    earlier hcounter hfusion
  have hs : Chapter1.IsSylowIn 2 (Tv T v) (Gv v) :=
    ⟨lc.reductions.centralizerSylow,lc.reductions.sylow_image⟩
  have hzT : z ∈ Tv T v := ((Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp
    (markedZ_mem_Tv_omega d)).1
  have hzW : z ∈ WK K L T z v := (le_conjugateSpanBy _ _) (mem_zpowers z)
  have he : ∀ (g : C) w, c.quotientMap (α g w) =
      SL2NaturalOffenders.naturalPair (F := F.Carrier) (e g) (c.quotientMap w) :=
    fun g w => c.quotientMap_action ((MulEquiv.subgroupCongr hI.symm) g) w
  obtain ⟨hz₁,hz₂⟩ := pair_seed_projections_ne_zero_source K L T z v hL hz hLv
    F.Carrier e c.quotientMap c.quotientMap_surjective he hzW
  have hB := pair_marked_baumann_image_source K L T z v hL hz hzT hK hLv hs a F c hI t ht hex
  exact pair_contradiction_original_source d V₃ earlier hG hcounter hfusion K hK hn
    hL hz hLv F.Carrier hF e c.quotientMap he hzW hz₁ hz₂ hB

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
