module
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.InitialSource.DoubleCenter
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Family.SourceConstruction.Normalizers
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Preliminaries.RatioSource.CommonNormal

/-!
# The source normalizer conclusions for actual double modules

Relative normality and characteristic two identify the whole ambient
normalizer of a source member with its maximal local overgroup. The actual
Baumann Sylow supplement, now constructed from the source module, then
supplies every local premise of the full earlier common-normal theorem
3.1.1. This proves the source 15.4.16 normalizer containment without an
assumed Sylow or module-decomposition certificate.

Source: Aschbacher--Smith, 15.4.12(2) and 15.4.16, pp.1161--1162.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.SourceWitnesses
open FamilySource FamilySource.ModuleStructure
variable {G : Type*} [Group G] [Finite G]
variable {κ : GroupClass} {T : Sylow 2 G} {M X : Subgroup G} {s : ℕ}

/-- The normalizer of the actual member is determined by its original input. -/
theorem source_member_normalizer (h : Input κ T M X s) :
    normalizer (X : Set G) = M :=
  member_normalizer_of_image_normal T h.maximal h.sylow_le
    (h.ambient.evenCharacteristic T M h.maximal h.sylow_le) h.member h.member_le
    (h.normal.map (quotientMap M) (QuotientGroup.mk'_surjective _))

/-- Source 15.4.16 for the actual double module. Only complete universal
3.1.1 and the preceding uniqueness conclusion remain as earlier inputs. -/
theorem source_double_baumann_normalizer (h311 : RatioSource.Earlier311 (G := G))
    (h : Input KnownSimple.IsKnownSimple T M X 2)
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N → X ⊔ (T : Subgroup G) ≤ N → N = M) :
    normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ M := by
  apply lemma_15_4_16 h.ambient ?_ T h.maximal h.sylow_le h.member_le
    ((normal_subgroupOf_iff_le_normalizer h.member_le).mp h.normal)
    (YFamily.perfect h.member) (member_core_ne_top _ h.member)
    (member_quotient_irreducible T h.member h.quotient_elementary)
    (by simpa only [ChapterB.thompsonJ_zero] using h.member.2)
    (source_thompsonGeometry h).sylow hunique
  intro hG S R M₀ H hM₀ hH hu hRne hRS hs hn
  obtain ⟨N, hNR, hNne, hN⟩ := h311 S hG M₀ H R hM₀ hH hu hRne hRS hs
    (Chapter3.normalIn_iff_le_normalizer.mp hn).2
  exact ⟨N, hNne, hNR, by simpa only [Chapter3.generated_eq_sup] using hN⟩

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.SourceWitnesses
