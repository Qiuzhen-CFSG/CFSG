module
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.InitialSource.MixedGeometry.Realized
public import CFSG.Quasithin.Chapter15.Section04.LocalIdentification.Earlier115
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.PostSylowInputs

/-!
# Actual common inputs for the mixed source branches

The original moved module contains [Z,Y] and makes it elementary. Normalization
by T and noncentrality of Z then force Z to meet that commutator nontrivially.
On the constructed mixed centralizer, the proved original 1.1.5 and 15.4.17
supply one common Sylow, all marked local hypotheses, odd-core elimination
and the fitting implication. No commutator-intersection or earlier-theorem
certificate is assumed.

Source: Aschbacher--Smith, 15.4.18, fourth paragraph, p.1162.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section04.InitialSource
open FamilySource FamilySource.ModuleStructure LocalSetup
open LocalSetup.TwoFactors LocalSetup.TwoFactors.MixedLocal LocalSetup.TwoFactors.SourceFactors
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The actual original module bounds the central-omega commutator. -/
theorem source_member_central_commutator {κ : GroupClass} {T : Sylow 2 G}
    {M X : Subgroup G} {s : ℕ} (h : Input κ T M X s) :
    omegaOneCenterAmbient (T : Subgroup G) ⊓
      ⁅omegaOneCenterAmbient (T : Subgroup G),X⁆ ≠ ⊥ := by
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  let D := ⁅Z,X⁆
  let W := movedModule (T : Subgroup G) M X
  let : IsElementaryAbelian 2 W := h.moved_elementary
  have hZV : Z ≤ localV (T : Subgroup G) M := by
    intro z hz
    have hzM := h.sylow_le ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1
    exact mem_map.mpr ⟨⟨z,hzM⟩,subset_normalClosure hz,rfl⟩
  have hDW : D ≤ W := commutator_mono hZV le_rfl
  let : IsElementaryAbelian 2 D := IsElementaryAbelian.of_le hDW
  have hWT : W ≤ (T : Subgroup G) := h.moved_le.trans
    (localV_le_sylow T M h.sylow_le
      (h.ambient.evenCharacteristic T M h.maximal h.sylow_le))
  have hTZ : (T : Subgroup G) ≤ normalizer (Z : Set G) := by
    apply le_trans _ (Subgroup.centralizer_le_normalizer _)
    intro t ht z hz
    exact (((mem_omegaOneCenterAmbient_iff _ _).mp hz).2.2 t ht).symm
  have hTD : (T : Subgroup G) ≤ normalizer (D : Set G) :=
    commutator_factors_normalized hTZ (YFamily.invariant h.member)
  have hne : D ≠ ⊥ := by
    intro he
    have hXT : X ≤ (T : Subgroup G) :=
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp he)).trans_eq h.center_centralizer
    have hp : IsPGroup 2 X := T.isPGroup'.of_injective (inclusion hXT) (inclusion_injective hXT)
    exact member_core_ne_top _ h.member (top_unique (le_sSup ⟨inferInstance,
      hp.of_equiv (Subgroup.topEquiv : (⊤ : Subgroup X) ≃* X).symm⟩))
  intro he
  exact hne (eq_bot_of_normalized_of_disjoint_centralOmega T.isPGroup' (hDW.trans hWT) hTD he)

/-- One actual Sylow and every original 1.1.5 input are constructed on the
mixed group; the odd core is trivial and the source fitting implication holds. -/
theorem source_mixed_prebranch {κ : GroupClass} {T : Sylow 2 G}
    {M₁ M₂ Y X : Subgroup G} {L : Bool → Subgroup G}
    (hY : Input κ T M₁ Y 1)
    (c : Configuration κ T Y X M₂ L) :
    ∃ P : Sylow 2 (generated T Y L),
      (P : Subgroup (generated T Y L)).map (generated T Y L).subtype = stabilizer T L ∧
      (∀ z ∈ omegaOneCenterAmbient (T : Subgroup G), z ≠ 1 →
        ∃ M : Subgroup G, Chapter1.Lemma115Hypotheses (generated T Y L) P M z) ∧
      pPrimeCore 2 (generated T Y L) = ⊥ ∧
      (omegaOneCenterAmbient (T : Subgroup G) ⊓ (generated T Y L).pCoreIn 2 ≠ ⊥ →
        generalizedFitting (generated T Y L) = pCore 2 (generated T Y L)) := by
  let E₀ := commonFixed T Y L
  let I := generated T Y L
  let U := stabilizer T L
  let : IsElementaryAbelian 2 (MixedLocal.omega T) := omegaOneCenterAmbient_elementaryAbelian _
  let : IsElementaryAbelian 2 E₀ := IsElementaryAbelian.of_le
    (show E₀ ≤ MixedLocal.omega T from inf_le_left.trans inf_le_left)
  have hE₀T : E₀ ≤ (T : Subgroup G) := c.common_le_stabilizer.trans inf_le_left
  have hUI : U ≤ I := le_sup_right.trans le_sup_left
  obtain ⟨S,hS⟩ := c.centralizer_sylow
  obtain ⟨P,hP⟩ := c.generated_sylow
  refine ⟨P,hP,?_,?_,?_⟩
  · intro z hz hz1
    have hzorder : orderOf z = 2 := orderOf_eq_prime_iff.mpr
      ⟨((mem_omegaOneCenterAmbient_iff _ _).mp hz).2.1,hz1⟩
    obtain ⟨M,hCM,hM⟩ := Finite.exists_le_maximal
      (isTwoLocal_involution_centralizer hzorder)
    obtain ⟨Q,hQ,hlocal⟩ := local115_from_promoted_centralizer hY.ambient.toIsQTKE T
      c.common_ne_bot hE₀T S hS (show U ≤ T from inf_le_left) hUI
      c.generated_centralizes hz hz1 hM hCM
    have hQP : Q = P := by
      apply Sylow.ext
      apply map_injective I.subtype_injective
      exact hQ.trans hP.symm
    exact ⟨M,hQP ▸ hlocal⟩
  · exact Prebranch.oddCore_eq_bot_of_promoted_centralizer hY.ambient
      SourceRecognition.Source.earlier115OneTwo T c.common_ne_bot hE₀T S hS
      (show U ≤ T from inf_le_left) hUI c.generated_centralizes
      (show Y ≤ I from le_sup_left.trans le_sup_left) (source_member_central_commutator hY)
  · exact Prebranch.generalizedFitting_implication_of_promoted_centralizer hY.ambient
      (fun h T B H I hB hBT hBH hCH hHN S hS hTI hIH hZ =>
        source_lemma_15_4_17_two h T hB hBT hBH hCH hHN S hS hTI hIH hZ)
      T c.common_ne_bot hE₀T S hS (show U ≤ T from inf_le_left) hUI c.generated_centralizes

end CFSG.Quasithin.Chapter15.Section04.InitialSource
