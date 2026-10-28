module
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.KernelSylow
public import CFSG.Quasithin.Chapter13.Section02.A5Local.EvenThompson
public import Theory.GroupTheory.PCoreImage

/-!
# Thompson normalizers for the original invariant even Sylow subgroup

Let R≤T contain T∩L and be T-invariant. The original Sylow intersection
makes R Sylow in LR. If its actual five-point action is even, the offender
calculation forces J(R) to centralize V. That centralizer is O₂(LR), so
J(R)=J(O₂(LR)) is normalized by LT. Nontriviality and the original unique
maximal overgroup of LT give N_G(J(R))≤N_G(L).

The even-action input is the separate source step for R=O₂(XT), using
[L,X]=L; it is retained at this boundary until that step is constructed.
Source: Aschbacher–Smith 13.2.9 and 13.2.4(1), printed pp. 879–881.
-/
public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section05.A5Source.Context
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}
  (d : Context T L V V₁ V₂ V₃)
include d

/-- The actual even action gives the Thompson identity and original normalizer bound. -/
theorem thompson_normalizer_of_invariant_even_sylow (R : Subgroup G)
    (hSR : (T : Subgroup G) ⊓ L ≤ R) (hRT : R ≤ (T : Subgroup G))
    (hnR : (T : Subgroup G) ≤ normalizer (R : Set G))
    (heven : (R.subgroupOf (L ⊔ (T : Subgroup G))).map d.localActor ≤ alternatingGroup (Fin 5)) :
    elementaryAbelianMaxJ R = elementaryAbelianMaxJ ((L ⊔ R).pCoreIn 2) ∧
      normalizer (elementaryAbelianMaxJ R : Set G) ≤ normalizer (L : Set G) := by
  let Y := L ⊔ R
  let K := L ⊔ (T : Subgroup G)
  let Q := Y.pCoreIn 2
  have hYK : Y ≤ K := sup_le le_sup_left (hRT.trans le_sup_right)
  have hnY : K ≤ normalizer (Y : Set G) := by
    apply sup_le
    · exact (show L ≤ Y from le_sup_left).trans Y.le_normalizer
    · exact (le_inf d.normalizes_L hnR).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hnQ : K ≤ normalizer (Q : Set G) :=
    hnY.trans (normalizer_le_normalizer_characteristic_image Y (pCore 2 Y))
  have hQK : Q ≤ K.pCoreIn 2 := pCoreIn_mono_of_normalizes hYK hnY
  obtain ⟨P,hP⟩ := Section02.A5Outside.source_component_sylow d
  obtain ⟨S,hS⟩ := (T.isPGroup'.to_le hRT).exists_sylow_sup_of_coprime_index L R
    (hRT.trans d.normalizes_L) (P : Subgroup L) P.not_dvd_index (hP ▸ hSR)
  have hQR : Q ≤ R := (pCoreIn_le_sylow Y S).trans_eq hS
  have hVR : V ≤ R := (le_inf d.chosen.le_sylow d.chosen.le_component).trans hSR
  have hc : R ⊓ centralizer (V : Set G) = Q := by
    apply le_antisymm
    · have hC : R ⊓ centralizer (V : Set G) = Y ⊓ K.pCoreIn 2 := by
        apply le_antisymm
        · exact le_inf (inf_le_left.trans le_sup_right)
            ((inf_le_inf_right _ hRT).trans_eq (d.sylow_centralizer d.normalizes_L))
        · intro x hx
          have hQY : Y ⊓ K.pCoreIn 2 ≤ Q := le_pCoreIn_of_normalizes
            ((isPGroup_pCoreIn 2 K).to_le inf_le_right) inf_le_left
            ((le_inf Y.le_normalizer ((hYK.trans K.le_normalizer).trans
              (normalizer_le_normalizer_characteristic_image K (pCore 2 K)))).trans inf_normalizer_le_normalizer_inf)
          exact ⟨hQR (hQY hx),d.chosen.core_centralizes hx.2⟩
      rw [hC]
      exact le_pCoreIn_of_normalizes ((isPGroup_pCoreIn 2 K).to_le inf_le_right) inf_le_left
        ((le_inf Y.le_normalizer ((hYK.trans K.le_normalizer).trans
          (normalizer_le_normalizer_characteristic_image K (pCore 2 K)))).trans inf_normalizer_le_normalizer_inf)
    · exact le_inf hQR (hQK.trans d.chosen.core_centralizes)
  have hJ : elementaryAbelianMaxJ R ≤ Q := by
    rw [←hc]
    exact le_inf (sSup_le fun _ hA => hA.1)
      (d.thompson_centralizes_of_even_action R hVR (hRT.trans le_sup_right) heven)
  have he : elementaryAbelianMaxJ R = elementaryAbelianMaxJ Q :=
    (elementaryAbelianMaxJ_eq_of_intermediate R Q hJ hQR).symm
  refine ⟨he,?_⟩
  rw [he]
  have hQV : V ≤ Q := by
    rw [←hc]
    let := d.elementary
    exact le_inf hVR (le_centralizer_iff_isMulCommutative.mpr inferInstance)
  have hQne : Q ≠ ⊥ := fun hb => d.chosen.ne_bot (bot_unique (hQV.trans_eq hb))
  exact normalizer_le_of_unique_maximalTwoLocal d.unique_maximal_overgroup
    ((isPGroup_pCoreIn 2 Y).to_le (sSup_le fun _ hA => hA.1))
    (elementaryAbelianMaxJ_ne_bot_of_finite_pGroup Q (isPGroup_pCoreIn 2 Y) hQne)
    (hnQ.trans (normalizer_le_normalizer_elementaryAbelianMaxJ Q))

end CFSG.Quasithin.Chapter13.Section05.A5Source.Context

namespace CFSG.Quasithin.Chapter13.Section02.A5Outside
variable {G : Type*} [Group G] [Finite G]
/-- All R-construction premises are discharged on the literal kernel residual;
only the preceding inner-action step is retained. -/
theorem source_kernel_thompson_normalizer_of_even_action
    {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}
    (d : Section05.A5Source.Context T L V V₁ V₂ V₃)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H)
    (hne : centralizer ((omegaOrbit T H).subgroupOf H : Set H) ≠ pCore 2 H) :
    let C := centralizer ((omegaOrbit T H).subgroupOf H : Set H)
    let X := ((pResidual 2 C).map C.subtype).map H.subtype
    let R := (X ⊔ (T : Subgroup G)).pCoreIn 2
    (R.subgroupOf (L ⊔ (T : Subgroup G))).map d.localActor ≤ alternatingGroup (Fin 5) →
      elementaryAbelianMaxJ R = elementaryAbelianMaxJ ((L ⊔ R).pCoreIn 2) ∧
      normalizer (elementaryAbelianMaxJ R : Set G) ≤ normalizer (L : Set G) := by
  dsimp only
  intro heven
  obtain ⟨hSR,hRT,hnR,_⟩ := source_residual_kernel_sylow_configuration d hH hB hZ hs hne
  exact d.thompson_normalizer_of_invariant_even_sylow _ hSR hRT hnR heven
end CFSG.Quasithin.Chapter13.Section02.A5Outside
