module

public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.G2Source.CharacteristicTwoBlocks
public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.G2Source.HyperplaneNormalizers
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.CommonNormalKnownSimple
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.MovedAlternating

/-!
# The local index contradiction for the escaping binary G₂ hyperplane

For the single residual block J, put Q = C_T(V) and H = JQ. The original
chosen-module centralizer identity makes Q normal in LT. The source uniqueness
theorem supplies the common-normal obstruction, and characteristic two descends
from C_G(U) to H through the actual Sylow Q. The moved alternating C.5.7 theorem
then gives index two for a maximal block normalizer in LT.

Its normalizer either equals the maximal hyperplane normalizer, contradicting
index 36 or 28, or equals LT. In the latter case C_V(J) is T-invariant, so the
proved E.6.13 forces J into N_G(V), contradicting the original escape.

Source: Aschbacher--Smith, E.6.14, printed p.251, applied to 12.4.8, p.815.
-/

public section
open Subgroup Theory.GroupTheory Module
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section04.SmallFusion.G2Source
open Chapter12.Section02 ChapterB.QuasisimpleSource Atlas.G2.Natural
open ChapterE ChapterE.Section06 ChapterE.Section06.InvariantSubspaces
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V U : Subgroup G}

/-- The local C.5 configuration uses the literal selected block and LT. -/
theorem cover_characteristicTwo_local_configuration
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (e : ActionEquiv D.quotientAction (OrthogonalCover.action (ZMod 2)))
    (hne : fixedSubgroup L V ≠ ⊥)
    (hUV : U ≤ V) (hcor : subgroupCorank V U = 1)
    (hescape : ¬ centralizer (U : Set G) ≤ normalizer (V : Set G))
    (hc : HasCharacteristicTwo (centralizer (U : Set G)))
    (J : Subgroup G) (hJ : SingleBlock T (normalizer (V : Set G)) V U J)
    (hmax : localNormalizer (L ⊔ (T : Subgroup G)) J ⋖ L ⊔ (T : Subgroup G)) :
    LocalIndex.Configuration KnownSimple.IsKnownSimple (L ⊔ (T : Subgroup G))
      (J ⊔ sylowCentralizer (T : Subgroup G) V) (sylowCentralizer (T : Subgroup G) V) J := by
  let A := L ⊔ (T : Subgroup G)
  let Q := sylowCentralizer (T : Subgroup G) V
  let H := J ⊔ Q
  let M := normalizer (V : Set G)
  have hE := cover_source_hypothesisE61 h D structural e hne
  have hU := (escaping_cover_subspaces h D structural e hne hUV hcor hescape).2.2.2.1
  have hs := structural L h
  have hTV := (hs.2.2 V D).1
  have hVOrbit : componentOrbit V (T : Subgroup G) = V :=
    le_antisymm (iSup_conjugates_le_of_le_normalizer V T V le_rfl hTV)
      (le_componentOrbit V T)
  have hQ : Q = A.pCoreIn 2 := by
    change (T : Subgroup G) ⊓ centralizer (V : Set G) = _
    simpa only [hVOrbit] using D.orbit_centralizer h.toHypothesis1221
  have hAQ : A ≤ normalizer (Q : Set G) := by
    rw [hQ]
    exact A.le_normalizer.trans (normalizer_le_normalizer_characteristic_image A (pCore 2 A))
  have hJM : ¬ J ≤ M := by
    intro hj
    apply hescape
    rw [hJ.generated]
    exact sup_le inf_le_right hj
  have hJN : normalizer (U : Set G) ≤ normalizer (J : Set G) := by
    rw [hJ.residual_three]
    exact (normalizer_le_normalizer_centralizer U).trans
      (normalizer_le_normalizer_characteristic_image (centralizer (U : Set G))
        (primeToResidual 3 (centralizer (U : Set G))))
  have hSyl := hE.sylow_obstruction hU
  have hQH : Q ≤ centralizer (U : Set G) := (Chapter1.isSylowIn_iff.mp hSyl).2.1
  have hHC : H ≤ centralizer (U : Set G) := sup_le hJ.le_centralizer hQH
  have hQ2 : IsPGroup 2 Q := (Chapter1.isSylowIn_iff.mp hSyl).1
  have hQN : Q ≤ normalizer (J : Set G) :=
    hQH.trans ((Subgroup.centralizer_le_normalizer _).trans hJN)
  have hres : (pResidual 2 H).map H.subtype = J :=
    embedded_pResidual_join_pGroup J Q hJ.type.chi.short.twoPerfect hQ2 hQN
  have hHSyl : Chapter1.IsSylowIn 2 Q H :=
    Chapter1.IsSylowIn.restrict hSyl le_sup_right hHC
  have hHchar : HasCharacteristicTwo H := by
    obtain ⟨P,hP⟩ := hSyl
    have hPH : (P : Subgroup (centralizer (U : Set G))) ≤
        H.subgroupOf (centralizer (U : Set G)) := by
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
    h.simpleQTKE T h.maximal_faithful.1
  have hOrbit : componentOrbit L (T : Subgroup G) = L := by
    apply le_antisymm _ (le_componentOrbit L _)
    exact iSup_conjugates_le_of_le_normalizer L (T : Subgroup G) L le_rfl hs.1
  obtain ⟨_,_,_,_,hMV,_,_⟩ := exists_fixed_involution_setup h D structural e hne
  have huniq : ∀ N : Subgroup G, IsMaximalTwoLocal N → A ≤ N → N = M := by
    intro N hN hAN
    have he : N = normalizer (L : Set G) := by
      simpa only [hOrbit] using hu.normalizer_unique N hN hAN
    exact he.trans hMV
  have hno := Chapter3.no_common_normal_of_unique_maximal hQ2 huniq
    (show ¬ H ≤ M from fun hh => hJM (le_sup_left.trans hh))
  exact ⟨hAsq,hHsq,hHchar,hHSyl,hJ.unique_maximal,
    inf_le_left.trans le_sup_right,hAQ,hno,hres,hJ.type,hmax⟩

/-- The complete local E.6.14 argument on the original G₂ hyperplane.
Only its actual cubic-action witness is supplied separately. -/
theorem cover_not_characteristicTwo_of_faithful_three
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (e : ActionEquiv D.quotientAction (OrthogonalCover.action (ZMod 2)))
    (hne : fixedSubgroup L V ≠ ⊥)
    (hUV : U ≤ V) (hcor : subgroupCorank V U = 1)
    (hescape : ¬ centralizer (U : Set G) ≤ normalizer (V : Set G))
    (ha : HasFaithfulThreeAction U) :
    ¬ HasCharacteristicTwo (centralizer (U : Set G)) := by
  intro hc
  let A := L ⊔ (T : Subgroup G)
  let M := normalizer (V : Set G)
  have hE := cover_source_hypothesisE61 h D structural e hne
  have hU := (escaping_cover_subspaces h D structural e hne hUV hcor hescape).2.2.2.1
  obtain ⟨J,hJ,hAlt,hm⟩ := cover_characteristicTwo_blockSelection_moved
    h D structural e hne hUV hcor hescape hc ha
  obtain ⟨hmax,hi⟩ := cover_hyperplane_normalizer h D structural e hne hUV hcor hescape
  have hJM : ¬ J ≤ M := by
    intro hj
    apply hescape
    rw [hJ.generated]
    exact sup_le inf_le_right hj
  have hn : normalizer (U : Set G) ≤ normalizer (J : Set G) := by
    rw [hJ.residual_three]
    exact (normalizer_le_normalizer_centralizer U).trans
      (normalizer_le_normalizer_characteristic_image (centralizer (U : Set G))
        (primeToResidual 3 (centralizer (U : Set G))))
  have hbetween : localNormalizer A U ≤ localNormalizer A J := inf_le_inf_left A hn
  rcases hmax.eq_or_eq hbetween inf_le_left with he | he
  · have hmaxJ : localNormalizer A J ⋖ A := he.symm ▸ hmax
    have hcJ := cover_characteristicTwo_local_configuration
      h D structural e hne hUV hcor hescape hc J hJ hmaxJ
    have hindex := LocalIndex.index_of_moved_alternating hcJ hm hAlt
    have htwo : (localNormalizer A U).relIndex A = 2 := he ▸ hindex
    rcases hi with hi | hi
    · exact (by decide : (2 : ℕ) ≠ 36) (htwo.symm.trans hi)
    · exact (by decide : (2 : ℕ) ≠ 28) (htwo.symm.trans hi)
  · let W := V ⊓ centralizer (J : Set G)
    have hUW : U ≤ W := le_inf hUV (le_centralizer_iff.mp hJ.le_centralizer)
    have hWne : W ≠ ⊥ := fun hb => hU.2.1 (le_bot_iff.mp (hb ▸ hUW))
    have hAJ : A ≤ normalizer (J : Set G) := he.ge.trans inf_le_right
    have hTW : (T : Subgroup G) ≤ normalizer (W : Set G) :=
      (le_inf hE.sylow_le_normalizer
        (((show (T : Subgroup G) ≤ A from le_sup_right).trans hAJ).trans
          (normalizer_le_normalizer_centralizer J))).trans
        inf_normalizer_le_normalizer_inf
    have hWnormal : (W.subgroupOf (T : Subgroup G)).Normal :=
      (normal_subgroupOf_iff_le_normalizer
        ((show W ≤ V from inf_le_left).trans hE.le_sylow)).mpr hTW
    have hC := centralizer_le_of_normal_in_sylow_knownSimple hE hWne inf_le_left
      (oddCentralizerCondition_mono hUW hU.2.2.2) hWnormal
    exact hJM ((le_centralizer_iff.mpr
      (show W ≤ centralizer (J : Set G) from inf_le_right)).trans hC)

end CFSG.Quasithin.Chapter12.Section04.SmallFusion.G2Source
