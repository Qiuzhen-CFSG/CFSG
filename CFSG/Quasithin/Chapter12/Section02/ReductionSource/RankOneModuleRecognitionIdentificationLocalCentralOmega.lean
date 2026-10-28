module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationLocalCentralOmega
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionIdentificationLocalInitial
public import Theory.GroupTheory.ReducedNormal.SylowCenter

/-!
# Central omega on the whole reduced Chapter 12 layer

Even characteristic makes LT a group of characteristic two. B.2.14 then
places Ω₁(Z(T)) in R₂(LT). Transporting this statement along the literal
inclusion LT → G and applying the natural-layer averaging argument gives
Ω₁(Z(T)) ≤ Z_S for the actual whole reduced layer.

The order-two assertion and remaining common analysis are still owned by
qt-d-1222-recognition-local-analysis. Final identification is owned by
qt-d-1222-rankone-recognition-identification.
Source: Aschbacher--Smith, B.2.14 and the opening of §6.2, printed p.680,
applied to the whole layer in 12.2.2(3d).
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
open Chapter6.Source Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G} {n : ℕ}
/-- B.2.14 places the central omega subgroup in the whole reduced subgroup. -/
theorem source_local_centralOmega_le_wholeReduced
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n) :
    centralOmega (T : Subgroup G) ≤ wholeReduced T L := by
  let H := L ⊔ (T : Subgroup G)
  have hTH : (T : Subgroup G) ≤ H := le_sup_right
  have hchar : centralizer (pCore 2 H : Set H) ≤ pCore 2 H :=
    Chapter1.mem_He_iff.mp (Chapter1.lemma_1_1_4_6 T (h611.simpleQTKE.evenCharacteristic T)
      ⟨h611.local_mem.1.prop.2.2, hTH⟩)
  have hh := map_mono (f := H.subtype) (sylow_omegaCenter_le_reduced (T.subtype hTH) hchar)
  change (Stellmacher.omegaOneCenterAmbient
    ((T.subtype hTH : Sylow 2 H) : Subgroup H)).map H.subtype ≤ wholeReduced T L at hh
  rw [← Stellmacher.omegaOneCenterAmbient_map_injective H.subtype H.subtype_injective,
    Sylow.coe_subtype, map_subgroupOf_eq_of_le hTH] at hh
  have he : centralOmega (T : Subgroup G) =
      Stellmacher.omegaOneCenterAmbient (T : Subgroup G) := by
    rw [centralOmega, ← map_center_subtype_eq_inf_centralizer,
      ← omegaCenterIn_eq_omegaOneAmbient]
    rfl
  exact he.symm ▸ hh
/-- The original central omega subgroup lies in the distinguished plane. -/
theorem source_local_centralOmega_le_ZS
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Conclusion6127 (T : Subgroup G) L
      (normalizer (L : Set G)) (wholeReduced T L) n) :
    centralOmega (T : Subgroup G) ≤ ZS (T : Subgroup G) L (wholeReduced T L) :=
  local_centralOmega_le_ZS_of_le_reduced h611 hnatural
    (source_local_centralOmega_le_wholeReduced h611)

end CFSG.Quasithin.Chapter12.Section02.RankOneModule
