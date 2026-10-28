module
public import CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalMaximality
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.OrbitSetup
public import CFSG.Quasithin.Chapter10.SourceA5LayerElementComponent

/-!
# The original prescribed element-centralizer component under 13.3.1

The original Fundamental Setup supplies Sylow promotion and 1.2.4 for a
vector distinguishing the original component pair. The moved-layer version
discharges this distinction using the actual alternating-five block obtained
from the escaping Baumann normalizer. No local Sylow or replacement-component
hypothesis is supplied.
Source: Aschbacher–Smith 10.2.1 and 13.3.2(2), printed pp.743 and 884–885.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalMaximality
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The literal original vector has the required Sylow centralizer and
an actual normal containing component in its full ambient centralizer. -/
theorem conjugate_layer_element_component
    (h : Chapter14.Section03.FaithfulSource.Hypothesis1331 T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤
      normalizer (localOrbit T L : Set G))
    {t v : G} (ht : t ∈ (T : Subgroup G))
    (hv : v ∈ (ChapterC.blockU (L.map (MulAut.conj t).toMonoidHom)).map
      (L.map (MulAut.conj t).toMonoidHom).subtype)
    (hvT : v ∈ (T : Subgroup G)) (hv1 : v ≠ 1)
    (hvL : v ∈ centralizer (L : Set G))
    (hCT : (T : Subgroup G) ⊓ centralizer ({v} : Set G) =
      (T : Subgroup G) ⊓ normalizer (L : Set G)) :
    Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ normalizer (L : Set G))
      (centralizer ({v} : Set G)) ∧
    ∃ I : Subgroup G, L ≤ I ∧ I ≤ centralizer ({v} : Set G) ∧
      (I.subgroupOf (centralizer ({v} : Set G))).IsCComponent ∧
      centralizer ({v} : Set G) ≤ normalizer (I : Set G) := by
  obtain ⟨D⟩ := (hypothesis1221 h e).exists_original_fundamentalSetup
  exact Chapter10.source_a5_conjugate_layer_element_component D e hn hout ht hv hvT hv1 hvL hCT

end CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalMaximality
