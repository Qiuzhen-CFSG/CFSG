module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.Catalogue.Preparation
public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.C27.MSRestriction
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.OriginalMS

/-!
# MS conditions on the original component-radical product

The actual S is Sylow in I and lies in NI = M intersect I. Since
R = O2(NI), NI supplies an odd-index core witness. Restriction to XR
preserves the literal core, and characteristic-normalizer control gives
MS3 with normality relative to XR. The final constructor requires only
the full SL3 core-quotient model; it assumes no MS conditions.

Core-quotient recognition and the C.1.34 module alternatives remain
separate obligations. This module does not assert MSDescription or
completion of original 15.2.23.

Source: Aschbacher--Smith C.1.31, p.135; C.2.7, pp.145--147; original
15.2.23, pp.1116--1117; refs/quasithin.pdf.
-/

public section
namespace CFSG.Quasithin.Chapter15.Section02.ComponentCatalogue
open Subgroup Theory.GroupTheory Stellmacher
open Section01 PlaneUniquenessPreceding
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterC.C27Source
open scoped MatrixGroups
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS I X : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)
include d

/-- The original NI and its Sylow subgroup supply MS2(a) on XR. -/
theorem normalized_component_ms_oddIndex
    (hI : PlaneEscapes Mc ZS I)
    (hcore : (M ⊓ I).pCoreIn 2 = M.pCoreIn 2)
    (s : Normalized H M I X) :
    MSOddIndex X ((M ⊓ I).pCoreIn 2) := by
  let R := (M ⊓ I).pCoreIn 2
  let J := X ⊔ R
  let h := normalized_component_input (hsource := hsource) hI hcore s
  obtain ⟨P,hP⟩ := d.sylow_in_escape hI
  have hPN : (P : Subgroup I) ≤ (M ⊓ I).subgroupOf I := by
    intro x hx
    have hxS : (x : G) ∈ planeSylow T ZS := hP ▸ mem_map_of_mem I.subtype hx
    exact ⟨hsource.maximal.1.2 hxS.1,x.property⟩
  obtain ⟨Q,hQ,ho,hR⟩ := msOddIndexRadical_join_from_source h
    (msOddIndexRadical_of_first_core h (M ⊓ I) inf_le_right le_rfl P hPN rfl)
  refine ⟨Q.map J.subtype,?_,?_,?_⟩
  · apply lt_of_le_of_ne (map_subtype_le _)
    intro he
    apply hQ.ne
    apply map_injective J.subtype_injective
    rw [he,←MonoidHom.range_eq_map,range_subtype]
  · have he : (Q.map J.subtype).subgroupOf J = Q :=
      Q.comap_map_eq_self_of_injective J.subtype_injective
    rwa [he]
  · rw [←map_pCoreIn_of_injective 2 Q J.subtype J.subtype_injective]
    change Q.pCoreIn 2 = R.subgroupOf J at hR
    rw [hR,map_subgroupOf_eq_of_le (show R ≤ J from le_sup_right)]

/-- Assemble all MS-pair conditions once the full core quotient is identified.
The star-group model alone is not this premise. -/
theorem normalized_component_msPair_of_core_model
    (hI : PlaneEscapes Mc ZS I)
    (hcore : (M ⊓ I).pCoreIn 2 = M.pCoreIn 2)
    (s : Normalized H M I X)
    (n : ℕ) (F : Type) [Field F] [Finite F]
    (hn : 1 ≤ n) (hF : Nat.card F = 2^n)
    (e : (X ⧸ pCore 2 X) ≃* SL(3,F)) :
    LinearThreeMSPair KnownSimple.IsKnownSimple X ((M ⊓ I).pCoreIn 2) n F := by
  let h := normalized_component_input (hsource := hsource) hI hcore s
  exact {
    positive := hn
    field_card := hF
    model := ⟨e⟩
    sqtk := (source_join_input h).setup.sqtk
    fitting := source_join_fitting h
    component := (source_join_input h).component
    radical := Or.inl (normalized_component_ms_oddIndex d hI hcore s)
    characteristic := source_ms_characteristic h }

end CFSG.Quasithin.Chapter15.Section02.ComponentCatalogue
