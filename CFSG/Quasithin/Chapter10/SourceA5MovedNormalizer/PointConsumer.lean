module
public import CFSG.Quasithin.Chapter10.SourceA5MovedNormalizer.Completion
public import CFSG.Quasithin.Chapter10.SourceA5PointCentralizerCompletion
/-!
# Applying the proved moved-factor normalizer bound to source point centralizers

The source 10.2.6 theorem removes the earlier normalizer premises from the
actual common-centralizer and exceptional-orbit contradictions of 10.2.9.
The remaining inspection interface retains its independent point-centralizer
geometry; the literal original quotient, vectors and subgroup maps are used.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
include D
/-- The common-centralizer alternative is impossible with the actual source
normalizer premise discharged. -/
theorem source_a5_point_common_centralizer_impossible_of_cross
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G))
    (I : Subgroup G) (hout : ¬ I ≤ D.maximalLocal)
    (hc : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (I : Set G)) : False :=
  source_a5_point_component_common_centralizer_impossible D ht
    (source_a5_moved_normalizer_le D e ht htn hcross) I hout hc

/-- The exceptional full-moved-orbit alternative is impossible with its
source normalizer bound discharged. -/
theorem source_a5_point_full_moved_orbit_impossible_of_cross
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G))
    (I : Subgroup G) (hout : ¬ I ≤ D.maximalLocal) (Z : Subgroup G)
    (he : conjugateSpanBy Z I = ⁅D.fullModule,L⁆) : False :=
  source_a5_point_component_full_moved_orbit_impossible D
    (source_a5_moved_normalizer_le D e ht htn hcross) I hout Z he

/-- The actual nonfixed partner point-centralizer endpoint, requiring only
its remaining independent inspection and local geometry. -/
theorem source_a5_partner_point_centralizer_le_of_cross_inspection
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G))
    {v : G} (hv : v ∈ (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom) (hvne : v ≠ 1)
    (hv0 : v ∉ centralizer (localOrbit T L : Set G))
    (hs : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({v} : Set G))
      (centralizer ({v} : Set G)))
    (hinspect : SourceA5PointComponentInspection D e t v) :
    centralizer ({v} : Set G) ≤ D.maximalLocal := by
  have hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G) := fun h => htn (h ht)
  have hsep : L.map (MulAut.conj t).toMonoidHom ≤
      centralizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (source_a5_moved_normalizer_opposite_cross D ht htn hcross))
  exact source_a5_partner_point_centralizer_le_of_inspection D e hn ht htn hsep hcross
    (source_a5_component_normalizer_le D e hn)
    (source_a5_moved_normalizer_le D e ht htn hcross) hv hvne hv0 hs hinspect

/-- Full original moved-vector centralizer control with both source 10.2.6
normalizer bounds discharged. The remaining hypotheses are precisely the
independent fixed-vector, Sylow-promotion and point-component inspections. -/
theorem source_a5_moved_point_centralizers_of_cross_inspection
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G))
    (hfixed : ∀ v ∈ (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom, v ≠ 1 →
      v ∈ centralizer (localOrbit T L : Set G) → centralizer ({v} : Set G) ≤ D.maximalLocal)
    (hpromote : ∀ v ∈ (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom, v ≠ 1 →
      v ∉ centralizer (localOrbit T L : Set G) →
      Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({v} : Set G))
        (D.maximalLocal ⊓ centralizer ({v} : Set G)) →
      Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({v} : Set G))
        (centralizer ({v} : Set G)))
    (hinspect : ∀ v ∈ (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom, v ≠ 1 →
      v ∉ centralizer (localOrbit T L : Set G) →
      Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({v} : Set G))
        (centralizer ({v} : Set G)) → SourceA5PointComponentInspection D e t v) :
    ∀ v ∈ ⁅D.fullModule,L⁆, v ≠ 1 → centralizer ({v} : Set G) ≤ D.maximalLocal := by
  have hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G) := fun h => htn (h ht)
  have hsep : L.map (MulAut.conj t).toMonoidHom ≤
      centralizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (source_a5_moved_normalizer_opposite_cross D ht htn hcross))
  exact source_a5_moved_point_centralizers_of_inspection D e hn ht htn hsep hcross
    (source_a5_component_normalizer_le D e hn)
    (source_a5_moved_normalizer_le D e ht htn hcross) hfixed hpromote hinspect
end CFSG.Quasithin.Chapter10
