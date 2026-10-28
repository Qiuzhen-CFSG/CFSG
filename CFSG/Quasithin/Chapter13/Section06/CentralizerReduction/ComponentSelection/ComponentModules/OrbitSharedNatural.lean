module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.ComponentModules.OrbitComponentModels
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.PairFromComponents
/-!
# A common natural model on the original orbit quotient

The original moving element exchanges the two component images inside the
offender actor. Native B.5 factor alignment therefore exchanges the actual
source factors, and transport through the same element gives either a
common binary SL₂ natural model or the paired S₅ natural model. The exact
fixed quotient, intertwiners, original factor inclusions, and moving Sylow
element are retained. The original-source wrapper constructs the component
and native classification data; only source plus placement remains explicit.

Source: Aschbacher–Smith 13.6.14, printed p.929, applying B.5.6(3).
-/
public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
open ComponentElimination.SourceContainment.LinearThree.CentralAction.ModuleAlternatives
open ChapterB ChapterB.SourceInduction ChapterB.QuasisimpleSource
universe u
variable {G : Type u} [Group G] [Finite G]

theorem orbit_shared_natural_source
    (K L T : Subgroup G) (z v : G)
    [IsElementaryAbelian 2 (WK K L T z v)]
    (hlocal : IsSQTK KnownSimple.IsKnownSimple (Gv v))
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hSylow : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (hzT : z ∈ Tv T v)
    (hK : K ∈ Yz L T z v) (hn : ¬ Tv T v ≤ normalizer (K : Set G))
    (E : BinaryField) (eF : plusImage K L T z v hL hz K ≃* SL(2,E.Carrier))
    (d : SourceTwoFactorCase ((wkRepresentation K L T z v hL hz).comp
      (offenderSubgroup (wkRepresentation K L T z v hL hz)).subtype)) :
    let := offenderSubgroup_normal (wkRepresentation K L T z v hL hz)
    ∃ t : G, ∃ ht : t ∈ Tv T v,
      let tA : plusActor K L T v := ⟨t,(show Tv T v ≤ plusActor K L T v from le_sup_right) ht⟩
      d.first.map (MulAut.conjNormal (plusMk K L T z v hL hz tA)).toMonoidHom = d.second ∧
      d.second.map (MulAut.conjNormal (plusMk K L T z v hL hz tA)).toMonoidHom = d.first ∧
      ((∃ F : BinaryField, Nonempty (d.MarkedProduct (linearNatural F 2))) ∨
        Nonempty (d.MarkedProduct (BinaryPermutation.naturalRepresentation (Fin 5)))) := by
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
  have hmove : (A.subgroupOf I).map (MulAut.conjNormal (plusMk K L T z v hL hz tA)).toMonoidHom = B.subgroupOf I := by
    apply map_injective I.subtype_injective
    rw [map_map]
    have hc : I.subtype.comp (MulAut.conjNormal (plusMk K L T z v hL hz tA)).toMonoidHom =
        (MulAut.conj (plusMk K L T z v hL hz tA)).toMonoidHom.comp I.subtype := by
      ext x
      rfl
    rw [hc,← map_map,map_subgroupOf_eq_of_le hAI,map_subgroupOf_eq_of_le hBI]
    exact hAB.symm
  have hcore : pCore 2 I = ⊥ := by
    have hle : (pCore 2 I).map I.subtype ≤ pCore 2 (Gplus K L T z v hL hz) :=
      le_sSup ⟨inferInstance,pCore_isPGroup.map I.subtype⟩
    rw [plus_twoCore_eq_bot K L T z v hK.1.1 hL hz hSylow] at hle
    apply (eq_bot_iff_forall _).mpr
    intro x hx
    exact Subtype.ext (hle (mem_map_of_mem I.subtype hx))
  let eA : (A.subgroupOf I) ≃* SL(2,E.Carrier) := (subgroupOfEquivOfLe hAI).trans eF
  let eAB : A ≃* B := ((MulAut.conj (plusMk K L T z v hL hz tA)).subgroupMap A).trans
    (MulEquiv.subgroupCongr hAB.symm)
  let eB : (B.subgroupOf I) ≃* SL(2,E.Carrier) :=
    (subgroupOfEquivOfLe hBI).trans (eAB.symm.trans eF)
  have hex := d.exchange_of_moving_component hcore (hA.subgroupOf hAI) (hB.subgroupOf hBI)
    hne (MulAut.conjNormal (plusMk K L T z v hL hz tA)) hmove
  exact ⟨t,ht,hex.1,hex.2,source_pair_natural_of_binary_components ρ I d hcore
    (hA.subgroupOf hAI) (hB.subgroupOf hBI) hne E eA eB _ hmove⟩

open A5Module ComponentReduction InitialSieve
variable {T : Sylow 2 G} {L V V₁ V₂ : Subgroup G}

theorem orbit_shared_natural_of_plus_placement_original_source
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
    (hLvplus : plusImage K L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module) hL hz
        (Lv L (markedV d.flag.module)) ≤
      plusImage K L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module) hL hz
        (Kminus K (T : Subgroup G) (markedV d.flag.module))) :
    let := (WK_mem_reducedFamily_original_source d V₃ earlier hG hm hcounter hfusion K hK.1.1).2.1
    let ρ := wkRepresentation K L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module) hL hz
    let := offenderSubgroup_normal ρ
    ∃ a : SourceTwoFactorCase (ρ.comp (offenderSubgroup ρ).subtype),
      ∃ t : G, ∃ ht : t ∈ Tv (T : Subgroup G) (markedV d.flag.module),
        let tA : plusActor K L (T : Subgroup G) (markedV d.flag.module) :=
          ⟨t,(show Tv (T : Subgroup G) (markedV d.flag.module) ≤
            plusActor K L (T : Subgroup G) (markedV d.flag.module) from le_sup_right) ht⟩
        a.first.map (MulAut.conjNormal (plusMk K L (T : Subgroup G) (markedZ d.flag.module)
          (markedV d.flag.module) hL hz tA)).toMonoidHom = a.second ∧
        a.second.map (MulAut.conjNormal (plusMk K L (T : Subgroup G) (markedZ d.flag.module)
          (markedV d.flag.module) hL hz tA)).toMonoidHom = a.first ∧
        ((∃ F : BinaryField, Nonempty (a.MarkedProduct (linearNatural F 2))) ∨
          Nonempty (a.MarkedProduct (BinaryPermutation.naturalRepresentation (Fin 5)))) := by
  let := (WK_mem_reducedFamily_original_source d V₃ earlier hG hm hcounter hfusion K hK.1.1).2.1
  obtain ⟨E,_,_,⟨eF⟩⟩ := noninvariant_component_linearTwo_of_plus_placement_original_source
    d V₃ earlier hG hm hcounter hfusion K hK hn hL hz hLvplus
  obtain ⟨a⟩ := orbit_twoFactor_of_plus_placement_original_source
    d V₃ earlier hG hm hcounter hfusion K hK hn hL hz hLvplus
  obtain ⟨c⟩ := localConfiguration_of_earlier_source d (normalizer (L : Set G)) V₃
    earlier hcounter hfusion
  refine ⟨a,?_⟩
  exact orbit_shared_natural_source K L (T : Subgroup G) _ _
    (hG.involution_centralizer_sqtk (marked_orders d.flag.module).2) hL hz
    ⟨c.reductions.centralizerSylow,c.reductions.sylow_image⟩
    ((Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp (markedZ_mem_Tv_omega d)).1
    hK hn E eF a

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
