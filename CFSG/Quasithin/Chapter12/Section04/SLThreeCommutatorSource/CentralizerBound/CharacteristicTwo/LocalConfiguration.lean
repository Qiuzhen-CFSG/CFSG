module
public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.CentralizerBound.CharacteristicTwo.BlockSelection
public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.CentralizerBound.CharacteristicTwo.Geometry
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Contracts

/-!
# The local C.5.1–2 configuration for the selected L₃ block

Set Q = C_T(V) and H = JQ for the literal residual block J in C_G(U).
Characteristic two descends to H because H contains the original Sylow Q.
The uniqueness theorem for LT supplies the common-normal obstruction;
no characteristic-two or SQTK assertion about the ambient join is assumed.

Source: Aschbacher–Smith E.6.14, printed p.251, applied in 12.4.8, p.815.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.CentralizerBound.CharacteristicTwo
open ChapterE.Section06 ChapterE.Section06.InvariantSubspaces
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V U : Subgroup G}

/-- Construct all local hypotheses for the original block and the original LT. -/
theorem local_configuration (c : Configuration T L V U)
    (hc : HasCharacteristicTwo (centralizer (U : Set G)))
    (J : Subgroup G) (hJ : SingleBlock T (normalizer (V : Set G)) V U J)
    (hmax : localNormalizer (L ⊔ (T : Subgroup G)) J ⋖ L ⊔ (T : Subgroup G)) :
    LocalIndex.Configuration KnownSimple.IsKnownSimple (L ⊔ (T : Subgroup G))
      (J ⊔ sylowCentralizer (T : Subgroup G) V) (sylowCentralizer (T : Subgroup G) V) J := by
  let A := L ⊔ (T : Subgroup G)
  let Q := sylowCentralizer (T : Subgroup G) V
  let H := J ⊔ Q
  let M := normalizer (V : Set G)
  have hE := source_hypothesisE61 c.hypothesis c.structural c.extension c.fixed_nontrivial
  have hU := (escaping_subspaces c.hypothesis c.structural c.extension
    c.fixed_nontrivial c.normalizer_action c.le_module c.corank c.escape).2.2.2.1
  have hs := c.structural G T L c.hypothesis
  have hAQ : A ≤ normalizer (Q : Set G) :=
    join_normalizes_sylow_centralizer c.extension hs.1 (hs.2.2 V c.chosen).1
  have hJM : ¬ J ≤ M := by
    intro hj
    apply c.escape
    rw [hJ.generated]
    exact sup_le inf_le_right hj
  have hJN : normalizer (U : Set G) ≤ normalizer (J : Set G) := by
    rw [hJ.residual_three]
    exact (normalizer_le_normalizer_centralizer U).trans
      (normalizer_le_normalizer_characteristic_image (centralizer (U : Set G))
        (primeToResidual 3 (centralizer (U : Set G))))
  have hSyl := c.sylow_centralizers.1
  have hQH : Q ≤ centralizer (U : Set G) := (Chapter1.isSylowIn_iff.mp hSyl).2.1
  have hHC : H ≤ centralizer (U : Set G) := sup_le hJ.le_centralizer hQH
  have hQ2 : IsPGroup 2 Q := (Chapter1.isSylowIn_iff.mp hSyl).1
  have hQN : Q ≤ normalizer (J : Set G) :=
    hQH.trans ((Subgroup.centralizer_le_normalizer _).trans hJN)
  have hres : (pResidual 2 H).map H.subtype = J :=
    embedded_pResidual_join_pGroup J Q hJ.type.chi.short.twoPerfect hQ2 hQN
  have hHSyl : Chapter1.IsSylowIn 2 Q H := hSyl.restrict le_sup_right hHC
  have hHchar : HasCharacteristicTwo H := by
    obtain ⟨P,hP⟩ := hSyl
    have hPH : (P : Subgroup (centralizer (U : Set G))) ≤ H.subgroupOf (centralizer (U : Set G)) := by
      intro x hx
      have hxP : (x : G) ∈ (P : Subgroup (centralizer (U : Set G))).map
          (centralizer (U : Set G)).subtype := mem_map_of_mem _ hx
      rw [hP] at hxP
      have hxQ : (x : G) ∈ Q := hxP
      exact (show Q ≤ H from le_sup_right) hxQ
    exact (show HasCharacteristicTwo (H.subgroupOf (centralizer (U : Set G))) from
      centralizer_pCore_le_of_sylow_le P _ hPH hc).of_equiv (subgroupOfEquivOfLe hHC)
  have hHsq := hE.obstructionIntermediate_sqtk hU hHC
  have hSQTKQ := hE.simpleQTKE.twoLocal_sqtk
    (show IsTwoLocal (normalizer (Q : Set G)) from ⟨Q,hE.sylowCentralizer_ne_bot,hQ2,rfl⟩)
  have hAsq : IsSQTK KnownSimple.IsKnownSimple A :=
    ⟨hSQTKQ.stronglyQuasithin.of_injective (inclusion hAQ) (inclusion_injective hAQ),
      hSQTKQ.isKGroup.of_injective (inclusion hAQ) (inclusion_injective hAQ)⟩
  have hu := Chapter1.Section02.nonsolvable_uniqueness_knownSimple
    c.hypothesis.simpleQTKE T c.hypothesis.maximal_faithful.1
  have hOrbit : componentOrbit L (T : Subgroup G) = L := by
    apply le_antisymm _ (le_componentOrbit L _)
    exact iSup_conjugates_le_of_le_normalizer L (T : Subgroup G) L le_rfl hs.1
  obtain ⟨_,_,_,_,hMV,_,_⟩ := fixed_involution_setup_of_card_two
    c.hypothesis c.chosen c.structural (c.extension.fixed_card_eq_two c.fixed_nontrivial)
  have huniq : ∀ N : Subgroup G, IsMaximalTwoLocal N → A ≤ N → N = M := by
    intro N hN hAN
    have he : N = normalizer (L : Set G) := by
      simpa only [hOrbit] using hu.normalizer_unique N hN hAN
    exact he.trans hMV
  have hno := Chapter3.no_common_normal_of_unique_maximal hQ2 huniq
    (show ¬ H ≤ M from fun hh => hJM (le_sup_left.trans hh))
  exact ⟨hAsq,hHsq,hHchar,hHSyl,hJ.unique_maximal,
    inf_le_left.trans le_sup_right,hAQ,hno,hres,hJ.type,hmax⟩

end CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.CentralizerBound.CharacteristicTwo
