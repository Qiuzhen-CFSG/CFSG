module
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.Components.IntrinsicSource
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.Components.OrdinaryNormalizers
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.ParabolicGeneration

/-!
# Geometry of the selected unitary point component

Solvability of the literal centralizing residual makes every C-component
of the point normalizer move the original span. The omega-center criterion
then gives faithful-local membership. Original 13.3.2 promotes the component
to a maximal member, and relative component normality plus local uniqueness
give the exact normalizer and escape conclusions of reduction (e).

Source: Aschbacher--Smith 13.3.14(e), printed p.892. The source application
in SourceComponentGeometry supplies reduction (a), solvability and the
original local uniqueness inputs. Component existence remains the separate
preceding reductions (c)--(d).
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open Noncentrality Noncentrality.SupercriticalSource
open Chapter1 Chapter1.Section02.Adequate
open ChapterE Atlas.G2.Natural.BinaryPointFlag
variable {G : Type*} [Group G] [Finite G]

/-- Solvability of the literal centralizing residual forces every point
C-component to move U. No normality in the full ambient group is used. -/
theorem unitary_component_moves_span (H U : Subgroup G)
    (hs : Group.IsSolvable (centralizingResidual U))
    (K : Subgroup H) (hK : K.IsCComponent) : ⁅U,K.map H.subtype⁆ ≠ ⊥ := by
  let B := K.map H.subtype
  have hB : Group.IsPerfect B := by
    let := hK.perfect
    exact Group.IsPerfect.map H.subtype
  have hpB : IsPPerfect 2 B := by
    let := hB
    intro N hn hp
    let := hn
    let := hp.isNilpotent
    exact top_unique (le_of_isPerfect_of_solvable_quotient ⊤ N)
  intro hz
  have hle := twoPerfect_le_centralizingResidual hpB
    (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hz))
  let := hs
  let : Group.IsSolvable B := Group.isSolvable_of_isSolvable_injective
    (f := inclusion hle) (inclusion_injective hle)
  exact hK.not_isSolvable (Group.isSolvable_of_isSolvable_injective
    (f := (K.equivMapOfInjective H.subtype H.subtype_injective).toMonoidHom)
    (K.equivMapOfInjective H.subtype H.subtype_injective).injective)

/-- Reduction (a) and solvability make the actual point component faithful. -/
theorem unitary_component_faithful
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (H U : Subgroup G) (hTH : (T : Subgroup G) ≤ H) (hH : IsTwoLocal H)
    (ha : U ≤ Stellmacher.omegaOneCenterAmbient (H.pCoreIn 2))
    (hs : Group.IsSolvable (centralizingResidual U))
    (K : Subgroup H) (hK : K.IsCComponent) :
    K.map H.subtype ∈ MainForward.faithfulLocalComponents T := by
  have hm := unitary_component_moves_span H U hs K hK
  have hHe := Chapter1.twoLocal_mem_He_of_sylow_le T (hG.evenCharacteristic T) hH hTH
  have hω : (Stellmacher.omegaOneCenterAmbient (pCore 2 H)).map H.subtype =
      Stellmacher.omegaOneCenterAmbient (H.pCoreIn 2) :=
    (Stellmacher.omegaOneCenterAmbient_map_injective H.subtype H.subtype_injective _).symm
  have hUH : U ≤ H := ha.trans (hω ▸ map_subtype_le _)
  have hUi : U.subgroupOf H ≤ Stellmacher.omegaOneCenterAmbient (pCore 2 H) := by
    intro u hu
    have hh := ha hu
    rw [←hω] at hh
    obtain ⟨v,hv,he⟩ := hh
    exact (H.subtype_injective he) ▸ hv
  have hmi : ⁅U.subgroupOf H,K⁆ ≠ ⊥ := by
    intro he
    have hh := congrArg (fun A : Subgroup H => A.map H.subtype) he
    rw [map_commutator,map_subgroupOf_eq_of_le hUH,Subgroup.map_bot] at hh
    exact hm hh
  exact (mem_faithfulLocalComponents_iff T _).mpr
    (source_component_faithful_local T H hTH (Chapter1.mem_H_of_isTwoLocal hH)
      hHe K _ hK hUi hmi)

/-- A faithful point C-component is normal in that point normalizer. -/
theorem unitary_component_normal
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (H : Subgroup G) (hTH : (T : Subgroup G) ≤ H) (hH : IsTwoLocal H)
    (h1332 : Source1332OneTwo T) (K : Subgroup H) (hK : K.IsCComponent)
    (hf : K.map H.subtype ∈ MainForward.faithfulLocalComponents T) : K.Normal := by
  rcases Chapter1.Section02.component_normal_or_index_two_source
    (hG.twoLocal_sqtk hH) hK with hn | hi
  · exact hn
  have hTN : (T : Subgroup G).subgroupOf H ≤ normalizer (K : Set H) := by
    have he : (K.map H.subtype).subgroupOf H = K :=
      comap_map_eq_self_of_injective H.subtype_injective K
    rw [←he, ←subgroupOf_normalizer_eq (map_subtype_le K)]
    exact comap_mono (h1332 _ hf).1
  have hd := index_dvd_of_le hTN
  change (normalizer (K : Set H)).index ∣ ((T : Subgroup G).subgroupOf H).index at hd
  rw [hi] at hd
  exact ((T.subtype hTH).not_dvd_index hd).elim

/-- The faithful component has the exact maximal-normalizer and escape
conclusions in original reduction (e). -/
theorem unitary_component_normalizer_conclusions
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (L H : Subgroup G) (hTH : (T : Subgroup G) ≤ H) (hH : IsTwoLocal H)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hM : IsMaximalTwoLocal (normalizer (L : Set G)))
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → L ⊔ (T : Subgroup G) ≤ N →
      N = normalizer (L : Set G))
    (hescape : ¬ H ≤ normalizer (L : Set G))
    (h1332 : Source1332OneTwo T) (K : Subgroup H) (hK : K.IsCComponent)
    (hf : K.map H.subtype ∈ MainForward.faithfulLocalComponents T) :
    K.map H.subtype ∈ LStar G T ∧
      H ≤ normalizer (K.map H.subtype : Set G) ∧
      IsMaximalTwoLocal (normalizer (K.map H.subtype : Set G)) ∧
      (∀ N : Subgroup G, IsMaximalTwoLocal N →
        K.map H.subtype ⊔ (T : Subgroup G) ≤ N →
          N = normalizer (K.map H.subtype : Set G)) ∧
      ¬ L ≤ normalizer (K.map H.subtype : Set G) ∧
      ¬ K.map H.subtype ≤ normalizer (L : Set G) := by
  let B := K.map H.subtype
  have hB := source1332_faithful_maximal hG T h1332 hf
  have hTB := (h1332 B hf).1
  have hBn : (B.subgroupOf H).Normal := by
    have hn := unitary_component_normal hG T H hTH hH h1332 K hK hf
    change ((K.map H.subtype).comap H.subtype).Normal
    rwa [comap_map_eq_self_of_injective H.subtype_injective]
  have hHN : H ≤ normalizer (B : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (map_subtype_le K)).mp hBn
  have hBuni := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X)) hG T hB
  have horb : componentOrbit B (T : Subgroup G) = B :=
    le_antisymm (iSup_conjugates_le_of_le_normalizer B _ B le_rfl hTB) (le_componentOrbit B _)
  have hmax : IsMaximalTwoLocal (normalizer (B : Set G)) := horb ▸ hBuni.normalizer_maximal
  have huniq : ∀ N : Subgroup G, IsMaximalTwoLocal N → B ⊔ (T : Subgroup G) ≤ N →
      N = normalizer (B : Set G) := by
    intro N hN hBN
    have hh := hBuni.normalizer_unique N hN hBN
    change N = normalizer (componentOrbit B (T : Subgroup G) : Set G) at hh
    rwa [horb] at hh
  have hLn : ¬ L ≤ normalizer (B : Set G) := by
    intro hLN
    exact hescape (hHN.trans_eq (hu _ hmax (sup_le hLN hTB)))
  have hBM : ¬ B ≤ normalizer (L : Set G) := by
    intro hBM
    exact hescape (hHN.trans_eq (huniq _ hM (sup_le hBM hTL)).symm)
  exact ⟨hB,hHN,hmax,huniq,hLn,hBM⟩

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion
