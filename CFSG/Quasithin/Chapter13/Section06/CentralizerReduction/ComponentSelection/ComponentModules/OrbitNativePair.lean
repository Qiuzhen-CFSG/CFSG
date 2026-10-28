module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.ComponentModules.OrbitSharedNatural
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.LinearPairGeneration
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.ComponentModules.OrbitSymmetricExclusion
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.ComponentModules.PlusPlacement
/-!
# The native paired natural model in the original 13.6.14 setup

The actual source plus placement puts L_v⁺ in the component orbit. Its cubic
Sylow three-order excludes the linear-three comparison and the symmetric-five
paired module. The surviving binary natural pair has field order at least
four. Its original components coincide with the native B.5 factors, so the
offender actor is exactly K₋⁺ and K⁺ has the same chosen SL₂ field model.

The final theorem retains the literal fixed quotient of the original WK
action, both marked factor inclusions and the original T_v element exchanging
them. Every classification, model and placement premise is discharged from
the full original marked setup. These witnesses feed the paired Baumann
consumer without a minimal-parabolic assumption.

Source: Aschbacher–Smith 13.6.14, printed pp.929–930, applying A.3.8, B.5.6
and source 1.2.2.
-/
public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
open ComponentElimination.SourceContainment.LinearThree.CentralAction.ModuleAlternatives
open ChapterB ChapterB.SourceInduction ChapterB.QuasisimpleSource
universe u
variable {G : Type u} [Group G] [Finite G]
/-- The native natural pair is the original component pair over the same field. -/
theorem orbit_linear_pair_identification_source
    (K L T : Subgroup G) (z v : G)
    [IsElementaryAbelian 2 (WK K L T z v)]
    (hlocal : IsSQTK KnownSimple.IsKnownSimple (Gv v))
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hSylow : Chapter1.IsSylowIn 2 (Tv T v) (Gv v)) (hzT : z ∈ Tv T v)
    (hK : K ∈ Yz L T z v) (hn : ¬ Tv T v ≤ normalizer (K : Set G))
    (d : SourceTwoFactorCase ((wkRepresentation K L T z v hL hz).comp
      (offenderSubgroup (wkRepresentation K L T z v hL hz)).subtype))
    (F : BinaryField) (c : d.MarkedProduct (linearNatural F 2)) :
    4 ≤ Nat.card F.Carrier ∧
      offenderSubgroup (wkRepresentation K L T z v hL hz) = plusImage K L T z v hL hz (Kminus K T v) ∧
      Nonempty (plusImage K L T z v hL hz K ≃* SL(2,F.Carrier)) := by
  let ρ := wkRepresentation K L T z v hL hz
  let I := offenderSubgroup ρ
  let := offenderSubgroup_normal ρ
  obtain ⟨t, ht, htN, hp, _, _⟩ :=
    exists_plus_pair_coordinates_source K L T z v hlocal hL hz hSylow hK hn
  let A := plusImage K L T z v hL hz K
  let B := plusImage K L T z v hL hz (K.conjBy t)
  let tA : plusActor K L T v := ⟨t,(show Tv T v ≤ plusActor K L T v from le_sup_right) ht⟩
  have hAB : B = A.conjBy (plusMk K L T z v hL hz tA) :=
    plusImage_conjBy_source K L T K z v hL hz (K_le_plusActor K L T v) tA
  have hA : IsComponent (Gplus K L T z v hL hz) A :=
    ⟨plusImage_K_subnormal K L T z v hL hz hK,
      plusImage_K_quasisimple_source K L T z v hL hz hK hSylow⟩
  have hB : IsComponent (Gplus K L T z v hL hz) B :=
    hAB.symm ▸ hA.map_conj (plusMk K L T z v hL hz tA)
  have hOI := orbit_plus_le_offenders_source K L T z v hL hz hzT hSylow hK
  have hAI : A ≤ I := (map_mono (comap_mono (le_conjugateSpanBy K (Tv T v)))).trans hOI
  have hBI : B ≤ I := (map_mono (comap_mono (le_sup_right.trans hp.ge))).trans hOI
  have hne : A.subgroupOf I ≠ B.subgroupOf I := by
    intro he
    have hh := congrArg (map I.subtype) he
    rw [map_subgroupOf_eq_of_le hAI,map_subgroupOf_eq_of_le hBI] at hh
    exact plusImage_pair_ne_source K L T z v hlocal hL hz hK hn t ht htN hh
  have hF := c.linear_field_large F (hA.subgroupOf hAI)
  obtain ⟨hgen,⟨eA⟩,_⟩ := c.linear_components F (hA.subgroupOf hAI) (hB.subgroupOf hBI) hne
  have hi : A ⊔ B = I := by
    have hh := congrArg (map I.subtype) hgen
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hAI,map_subgroupOf_eq_of_le hBI,
      ← MonoidHom.range_eq_map,range_subtype] at hh
    exact hh
  have hKt : K.conjBy t ≤ plusActor K L T v :=
    le_sup_right.trans (hp.ge.trans (le_sup_left.trans le_sup_left))
  have heq : plusImage K L T z v hL hz (Kminus K T v) = A ⊔ B := by
    rw [hp,plusImage,subgroupOf_sup (K_le_plusActor K L T v) hKt,Subgroup.map_sup]
    rfl
  exact ⟨hF,hi.symm.trans heq.symm,⟨(subgroupOfEquivOfLe hAI).symm.trans eA⟩⟩

open A5Module ComponentReduction InitialSieve
variable {T : Sylow 2 G} {L V V₁ V₂ : Subgroup G}

/-- The full original setup supplies the literal binary natural pair and exchange. -/
theorem orbit_native_pair_original_source
    (d : FlagSource T L V V₁ V₂) (V₃ : Subgroup G)
    (earlier : EarlierLocal T L (normalizer (L : Set G)) V V₂ V₃ (markedZ d.flag.module))
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hm : SymmetricSix.ModuleData d.flag.module)
    (hcounter : IsA5Counterexample G) (hfusion : ControlsFusionOfZ d.flag.module)
    (K : Subgroup G)
    (hK : K ∈ Yz L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module))
    (hn : ¬ Tv (T : Subgroup G) (markedV d.flag.module) ≤ normalizer (K : Set G))
    (hL : Tv (T : Subgroup G) (markedV d.flag.module) ≤
      normalizer (Lv L (markedV d.flag.module) : Set G))
    (hz : Tv (T : Subgroup G) (markedV d.flag.module) ≤
      centralizer ({markedZ d.flag.module} : Set G))
    :
    let := (WK_mem_reducedFamily_original_source d V₃ earlier hG hm hcounter hfusion K hK.1.1).2.1
    let ρ := wkRepresentation K L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module) hL hz
    let := offenderSubgroup_normal ρ
    ∃ a : SourceTwoFactorCase (ρ.comp (offenderSubgroup ρ).subtype),
      ∃ F : BinaryField, 4 ≤ Nat.card F.Carrier ∧
      Nonempty (plusImage K L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module) hL hz K ≃* SL(2,F.Carrier)) ∧
      ∃ _c : a.MarkedProduct (linearNatural F 2),
        offenderSubgroup ρ = plusImage K L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module) hL hz
          (Kminus K (T : Subgroup G) (markedV d.flag.module)) ∧
        ∃ t : G, ∃ ht : t ∈ Tv (T : Subgroup G) (markedV d.flag.module),
          let tA : plusActor K L (T : Subgroup G) (markedV d.flag.module) :=
            ⟨t,(show Tv (T : Subgroup G) (markedV d.flag.module) ≤
              plusActor K L (T : Subgroup G) (markedV d.flag.module) from le_sup_right) ht⟩
          a.first.map (MulAut.conjNormal (plusMk K L (T : Subgroup G) (markedZ d.flag.module)
            (markedV d.flag.module) hL hz tA)).toMonoidHom = a.second ∧
          a.second.map (MulAut.conjNormal (plusMk K L (T : Subgroup G) (markedZ d.flag.module)
            (markedV d.flag.module) hL hz tA)).toMonoidHom = a.first := by
  let := (WK_mem_reducedFamily_original_source d V₃ earlier hG hm hcounter hfusion K hK.1.1).2.1
  have hLvplus := plusLv_le_Kminus_original_source d V₃ earlier hG hm hcounter hfusion K hK hn hL hz
  have ha := orbit_shared_natural_of_plus_placement_original_source
    d V₃ earlier hG hm hcounter hfusion K hK hn hL hz hLvplus
  dsimp only at ha
  obtain ⟨a,t,ht,hfirst,hsecond,hcase⟩ := ha
  obtain ⟨lc⟩ := localConfiguration_of_earlier_source d (normalizer (L : Set G)) V₃
    earlier hcounter hfusion
  have hSylow : Chapter1.IsSylowIn 2 (Tv (T : Subgroup G) (markedV d.flag.module))
      (Gv (markedV d.flag.module)) := ⟨lc.reductions.centralizerSylow,lc.reductions.sylow_image⟩
  have hzT := ((Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp (markedZ_mem_Tv_omega d)).1
  rcases hcase with hlin | hsym
  · obtain ⟨F,⟨c⟩⟩ := hlin
    obtain ⟨hF,hI,he⟩ := orbit_linear_pair_identification_source K L (T : Subgroup G) _ _
      (hG.involution_centralizer_sqtk (marked_orders d.flag.module).2) hL hz hSylow hzT hK hn a F c
    exact ⟨a,F,hF,he,c,hI,t,ht,hfirst,hsecond⟩
  · obtain ⟨c⟩ := hsym
    exact (orbit_symmetric_pair_excluded_source K L (T : Subgroup G) _ _ hL hz hSylow hzT hK
      hLvplus (plusLv_sylow_three_card_original_source d V₃ earlier hcounter hfusion K hL hz)
      a c t ht ⟨hfirst,hsecond⟩).elim

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
