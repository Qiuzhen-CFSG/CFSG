module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.ComponentModules.OrbitAlternatives
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.ComponentModules.PairedGeneration
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.ComponentModules.OrbitPlusLinearThree
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.BinaryComponentRows
/-!
# All components of the plus actor are binary rank one

The actual exchanged component images form a centerless pair. Plus placement
makes the full actor their Sylow extension, so source reducedness kills the
pair centralizer. Any further component would centralize both factors,
contradicting nontriviality. Consequently every actual component has the same
binary SL₂ model as K⁺. This supplies the model input for the native B.5
hyperplane and linear-three factor exclusions.

Source: Aschbacher–Smith 13.6.14, printed p.929, with ordinary component
calculus A.1. The only earlier-source placement is the literal plus inequality.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
universe u
variable {G : Type u} [Group G] [Finite G]

private theorem centerless_of_simple_perfect {D : Type*} [Group D]
    [IsSimpleGroup D] [Group.IsPerfect D] : center D = ⊥ := by
  rcases (inferInstance : (center D).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · exact (Group.IsPerfect.not_isMulCommutative D (center_eq_top_iff.mp h)).elim

private theorem centerless_of_equiv {D E : Type*} [Group D] [Group E]
    (e : D ≃* E) (h : center E = ⊥) : center D = ⊥ := by
  apply (eq_bot_iff_forall _).mpr
  intro x hx
  have he : e x = 1 := h.le ((centerCongr e ⟨x,hx⟩).property)
  exact e.map_eq_one_iff.mp he

private theorem component_eq_left_or_right {D : Type*} [Group D]
    {A B C : Subgroup D} (hA : IsComponent D A) (hB : IsComponent D B)
    (hC : IsComponent D C) (hc : centralizer ((A ⊔ B : Subgroup D) : Set D) = ⊥) :
    C = A ∨ C = B := by
  by_cases hCA : C = A
  · exact Or.inl hCA
  by_cases hCB : C = B
  · exact Or.inr hCB
  have hCC : C ≤ centralizer ((A ⊔ B : Subgroup D) : Set D) := by
    apply le_centralizer_iff.mp
    exact sup_le
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (hC.commutator_eq_bot_of_ne hA hCA)))
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (hC.commutator_eq_bot_of_ne hB hCB)))
  have hbot : C = ⊥ := bot_unique (hc ▸ hCC)
  let := hC.2
  let : IsSimpleGroup (C ⧸ center C) := IsQuasisimple.simple
  let : Nontrivial C := (QuotientGroup.mk'_surjective (center C)).nontrivial
  exact ((Subgroup.nontrivial_iff_ne_bot C).mp inferInstance hbot).elim

open scoped MatrixGroups

/-- Every ordinary component of the original plus actor has the same SL₂ model. -/
theorem orbit_plus_all_components_binary_source
    (K L T : Subgroup G) (z v : G)
    (hlocal : IsSQTK KnownSimple.IsKnownSimple (Gv v))
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hSylow : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (hK : K ∈ Yz L T z v) (hn : ¬ Tv T v ≤ normalizer (K : Set G))
    (hLvplus : plusImage K L T z v hL hz (Lv L v) ≤
      plusImage K L T z v hL hz (Kminus K T v))
    (F : ChapterB.QuasisimpleSource.BinaryField)
    (eF : plusImage K L T z v hL hz K ≃* SL(2,F.Carrier))
    (C : Subgroup (Gplus K L T z v hL hz))
    (hC : IsComponent (Gplus K L T z v hL hz) C) :
    Nonempty (C ≃* SL(2,F.Carrier)) := by
  obtain ⟨t,ht,htN,hp,hd,e,he⟩ :=
    exists_plus_pair_coordinates_source K L T z v hlocal hL hz hSylow hK hn
  let A := plusImage K L T z v hL hz K
  let B := plusImage K L T z v hL hz (K.conjBy t)
  let H := plusImage K L T z v hL hz (Kminus K T v)
  let tA : plusActor K L T v := ⟨t,(show Tv T v ≤ plusActor K L T v from le_sup_right) ht⟩
  have hAB : B = A.conjBy (plusMk K L T z v hL hz tA) :=
    plusImage_conjBy_source K L T K z v hL hz (K_le_plusActor K L T v) tA
  let eAB : A ≃* B := ((MulAut.conj (plusMk K L T z v hL hz tA)).subgroupMap A).trans
    (MulEquiv.subgroupCongr hAB.symm)
  have hA : IsComponent (Gplus K L T z v hL hz) A :=
    ⟨plusImage_K_subnormal K L T z v hL hz hK,
      plusImage_K_quasisimple_source K L T z v hL hz hK hSylow⟩
  have hB : IsComponent (Gplus K L T z v hL hz) B :=
    hAB.symm ▸ hA.map_conj (plusMk K L T z v hL hz tA)
  let := hA.2
  let : IsSimpleGroup (K ⧸ pCore 2 K) :=
    noninvariant_component_core_simple_source K L T z v hlocal hK hn
  let : IsSimpleGroup A :=
    (componentCoreEquivPlus K L T z v hlocal hL hz hSylow hK hn).symm.isSimpleGroup
  have hZA : center A = ⊥ := centerless_of_simple_perfect
  have hZB : center B = ⊥ := centerless_of_equiv eAB.symm hZA
  have hZH : center H = ⊥ := centerless_of_equiv e.symm (by
    rw [Subgroup.center_prod,hZA,hZB,bot_prod_bot])
  have hCH := paired_plus_centralizer_eq_bot_source K L T z v hL hz hK hLvplus hSylow hZH
  have hKt : K.conjBy t ≤ plusActor K L T v :=
    (le_sup_right.trans hp.ge).trans
      (show Kminus K T v ≤ plusActor K L T v from le_sup_left.trans le_sup_left)
  have heq : A ⊔ B = H := by
    change A ⊔ B = plusImage K L T z v hL hz (Kminus K T v)
    rw [hp,plusImage,subgroupOf_sup (K_le_plusActor K L T v) hKt,Subgroup.map_sup]
    rfl
  rcases component_eq_left_or_right hA hB hC (by rw [heq]; exact hCH) with hc | hc
  · exact ⟨(MulEquiv.subgroupCongr hc).trans eF⟩
  · exact ⟨(MulEquiv.subgroupCongr hc).trans (eAB.symm.trans eF)⟩

open Representation Representation.BinaryOffender
open scoped IsMulCommutative
open ComponentElimination.SourceContainment.LinearThree.CentralAction.ModuleAlternatives

/-- Every component in the literal normal offender actor has the same
binary rank-one model. -/
theorem orbit_offender_components_binary_source
    (K L T : Subgroup G) (z v : G)
    [IsElementaryAbelian 2 (WK K L T z v)]
    (hlocal : IsSQTK KnownSimple.IsKnownSimple (Gv v))
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hSylow : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (hK : K ∈ Yz L T z v) (hn : ¬ Tv T v ≤ normalizer (K : Set G))
    (hLvplus : plusImage K L T z v hL hz (Lv L v) ≤
      plusImage K L T z v hL hz (Kminus K T v))
    (F : ChapterB.QuasisimpleSource.BinaryField)
    (eF : plusImage K L T z v hL hz K ≃* SL(2,F.Carrier))
    (C : Subgroup (offenderSubgroup (wkRepresentation K L T z v hL hz)))
    (hC : IsComponent (offenderSubgroup (wkRepresentation K L T z v hL hz)) C) :
    Nonempty (C ≃* SL(2,F.Carrier)) := by
  let ρ := wkRepresentation K L T z v hL hz
  let I := offenderSubgroup ρ
  let := offenderSubgroup_normal ρ
  let := hC.2
  have hc : IsComponent (Gplus K L T z v hL hz) (C.map I.subtype) :=
    ⟨hC.1.trans' (inferInstance : I.Normal).isSubnormal,
      IsQuasisimple.of_mulEquiv (C.equivMapOfInjective I.subtype I.subtype_injective)⟩
  obtain ⟨e⟩ := orbit_plus_all_components_binary_source K L T z v hlocal hL hz hSylow
    hK hn hLvplus F eF _ hc
  exact ⟨(C.equivMapOfInjective I.subtype I.subtype_injective).trans e⟩

/-- The original corrected classifier now supplies its actual two-factor
module row; the hyperplane row is discharged using the component models. -/
theorem orbit_twoFactor_source
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (K L T : Subgroup G) (z v : G) (hv : orderOf v = 2)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hSylow : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (hzOmega : z ∈ Stellmacher.omegaOneCenterAmbient (Tv T v))
    (hf : generalizedFitting (Gv v) = pCore 2 (Gv v))
    (hK : K ∈ Yz L T z v) (hn : ¬ Tv T v ≤ normalizer (K : Set G))
    (hLvplus : plusImage K L T z v hL hz (Lv L v) ≤
      plusImage K L T z v hL hz (Kminus K T v))
    (F : ChapterB.QuasisimpleSource.BinaryField)
    (eF : plusImage K L T z v hL hz K ≃* SL(2,F.Carrier)) :
    let := wk_elementary K L T z v hK.1.1 hSylow hzOmega hf
    let ρ := wkRepresentation K L T z v hL hz
    Nonempty (ChapterB.SourceInduction.SourceTwoFactorCase (ρ.comp (offenderSubgroup ρ).subtype)) := by
  let := wk_elementary K L T z v hK.1.1 hSylow hzOmega hf
  rcases orbit_product_alternatives_source hG K L T z v hv hL hz hSylow hzOmega hf hK hn with h | ⟨c⟩
  · exact h
  obtain ⟨c⟩ := c
  exact (ChapterB.SourceInduction.HyperplaneCase.not_of_binary_components c (fun C hC => ⟨F,
    orbit_offender_components_binary_source K L T z v
      (hG.involution_centralizer_sqtk hv) hL hz hSylow hK hn hLvplus F eF C hC⟩)).elim

open A5Module ComponentReduction InitialSieve
variable {T : Sylow 2 G} {L V V₁ V₂ : Subgroup G}

/-- The original source setup yields an actual native two-factor module
row once the source plus containment is supplied. -/
theorem orbit_twoFactor_of_plus_placement_original_source
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
    Nonempty (ChapterB.SourceInduction.SourceTwoFactorCase (ρ.comp (offenderSubgroup ρ).subtype)) := by
  let := (WK_mem_reducedFamily_original_source d V₃ earlier hG hm hcounter hfusion K hK.1.1).2.1
  obtain ⟨F,_,_,⟨eF⟩⟩ := noninvariant_component_linearTwo_of_plus_placement_original_source
    d V₃ earlier hG hm hcounter hfusion K hK hn hL hz hLvplus
  obtain ⟨c⟩ := localConfiguration_of_earlier_source d (normalizer (L : Set G)) V₃
    earlier hcounter hfusion
  exact orbit_twoFactor_source hG K L (T : Subgroup G) _ _ (marked_orders d.flag.module).2
    hL hz ⟨c.reductions.centralizerSylow,c.reductions.sylow_image⟩ (markedZ_mem_Tv_omega d)
    (generalizedFitting_eq_pCore_of_earlier_source d V₃ earlier hG hm hcounter hfusion)
    hK hn hLvplus F eF

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
