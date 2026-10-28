module
public import CFSG.Quasithin.Chapter14.Section06.SourceCentrality
public import CFSG.Quasithin.ChapterA.Section01.Fitting.Characteristic
public import Theory.GroupTheory.GeneralizedFitting.CoreCentralQuotient
public import Theory.GroupTheory.PCoreSurjective

/-!
# The actual omega-core quotient in original 14.6.9

Original 14.6.1(5) centralizes the omega-center of the local two-core with
the whole generalized-Fitting preimage. Characteristic two of the local
Sylow overgroup then descends through that omega-center. We identify the
quotient core with the literal image of the original core, and place the
omega-center of the original Sylow image inside its omega-center.

This supplies step (j) of the paired-A₅ branch, without a quotient-action
or characteristic-two premise on the quotient.
Source: Aschbacher--Smith, 14.6.9(j), printed p.1027, using 14.6.1(5).
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter14.Section06
open Chapter15.Section03
variable {G : Type*} [Group G] [Finite G]

local instance omegaCore_normal {X : Type*} [Group X] :
    (omegaOneCenterAmbient (pCore 2 X)).Normal := by
  let : (omega₁ (center (pCore 2 X)) (p := 2)).Characteristic := omega₁_characteristic _
  unfold omegaOneCenterAmbient
  infer_instance

/-- The original local hypotheses give the characteristic-two quotient,
its actual core image, and the Sylow omega-center inclusion used in (j). -/
theorem source_omegaCore_quotient_characteristicTwo
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {H : Subgroup G} (hH : H ∈ Chapter1.HOver G (T : Set G))
    (hHZ : H ≤ centralizer (centralInvolutions T : Set G)) :
    let Z1 := omegaOneCenterAmbient (pCore 2 H)
    let q := QuotientGroup.mk' Z1
    generalizedFitting (H ⧸ Z1) = pCore 2 (H ⧸ Z1) ∧
      pCore 2 (H ⧸ Z1) = (pCore 2 H).map q ∧
      omegaOneCenterAmbient (((T.subtype hH.2 : Sylow 2 H) : Subgroup H).map q) ≤
        omegaOneCenterAmbient ((pCore 2 H).map q) := by
  dsimp only
  let Z1 := omegaOneCenterAmbient (pCore 2 H)
  let q := QuotientGroup.mk' Z1
  have hZQ : Z1 ≤ pCore 2 H := fun z hz =>
    ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1
  have hc : centralizer (pCore 2 H : Set H) ≤ pCore 2 H :=
    Chapter1.mem_He_iff.mp (Chapter1.lemma_1_1_4_6 T (hG.evenCharacteristic T) hH)
  have hfit := generalizedFitting_quotient_eq_pCore_of_preimage_centralizes 2 hc Z1 hZQ
    (generalizedFittingPreimage_centralizes_omegaCore hG T hempty hH hHZ)
  have himage : pCore 2 (H ⧸ Z1) = (pCore 2 H).map q := by
    have hk : IsPGroup 2 q.ker := by
      rw [QuotientGroup.ker_mk']
      exact pCore_isPGroup.to_le hZQ
    rw [← q.comap_pCore_of_ker_isPGroup (QuotientGroup.mk'_surjective Z1) hk,
      map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective Z1)]
  refine ⟨hfit,himage,?_⟩
  let S := (T.subtype hH.2).mapSurjective (QuotientGroup.mk'_surjective Z1)
  have hchar := (ChapterA.generalizedFitting_eq_pCore_iff 2).mp hfit
  rw [← himage]
  intro z hz
  obtain ⟨_,hzpow,hzcent⟩ := (mem_omegaOneCenterAmbient_iff _ _).mp hz
  have hzQ : z ∈ pCore 2 (H ⧸ Z1) := hchar (fun x hx =>
    hzcent x (pCore_isPGroup.le_sylow_of_normal S hx))
  exact (mem_omegaOneCenterAmbient_iff _ _).mpr
    ⟨hzQ,hzpow,fun x hx => hzcent x (pCore_isPGroup.le_sylow_of_normal S hx)⟩
end CFSG.Quasithin.Chapter14.Section06
