module
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.Components.OrdinaryThompsonSource

/-!
# Ordinary component entry from the escaping point normalizer

The uniqueness of the maximal local subgroups containing LT and KT makes
G₁ ≰ M sufficient for the normalizer exclusions in 13.3.14(e). The Sylow
omega-center centralizer then lies in N(K), while M supplies a distinct
maximal local subgroup. The source Thompson theorem gives [K,J(T)]=K and
hence the literal reduced offender entry on KL₁T.

These statements accept the actual point-normalizer escape, so they also
apply before abelianness of the full V-span has been decided. The final
source application of 12.2.13 is in `SourceEntry`.

Source: Aschbacher--Smith, 13.3.14(e--g), printed pp.892--893.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.Noncentrality
open SupercriticalSource Chapter1
open Section08.SourceCompletion
open Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V P E U M H : Subgroup G}
  (d : NaturalSetup T L V P E U M H)
include d

/-- Reduction (e) from the original escape, without a full-span hypothesis. -/
theorem ordinary_component_normalizer_conclusions_of_escape
    (h1221 : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hescape : ¬ H ≤ M)
    (h1332 : Source1332OneTwo T) (K : Subgroup H) (hK : K.IsCComponent)
    (hf : K.map H.subtype ∈ MainForward.faithfulLocalComponents T) :
    K.map H.subtype ∈ LStar G T ∧
      H ≤ normalizer (K.map H.subtype : Set G) ∧
      IsMaximalTwoLocal (normalizer (K.map H.subtype : Set G)) ∧
      (∀ N : Subgroup G, IsMaximalTwoLocal N →
        K.map H.subtype ⊔ (T : Subgroup G) ≤ N →
          N = normalizer (K.map H.subtype : Set G)) ∧
      ¬ L ≤ normalizer (K.map H.subtype : Set G) ∧ ¬ K.map H.subtype ≤ M := by
  let B := K.map H.subtype
  have hB := source1332_faithful_maximal d.counterexample.qtke T h1332 hf
  have hTB := (h1332 B hf).1
  have hBn : (B.subgroupOf H).Normal := by
    have hn := ordinary_component_normal d h1332 K hK hf
    change ((K.map H.subtype).comap H.subtype).Normal
    rwa [comap_map_eq_self_of_injective H.subtype_injective]
  have hHN : H ≤ normalizer (B : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (map_subtype_le K)).mp hBn
  have hBuni := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    d.counterexample.qtke T hB
  have horb : componentOrbit B (T : Subgroup G) = B :=
    le_antisymm (iSup_conjugates_le_of_le_normalizer B _ B le_rfl hTB)
      (le_componentOrbit B _)
  have hmax : IsMaximalTwoLocal (normalizer (B : Set G)) :=
    horb ▸ hBuni.normalizer_maximal
  have huniq : ∀ N : Subgroup G, IsMaximalTwoLocal N → B ⊔ (T : Subgroup G) ≤ N →
      N = normalizer (B : Set G) := by
    intro N hN hBN
    have hu := hBuni.normalizer_unique N hN hBN
    change N = normalizer (componentOrbit B (T : Subgroup G) : Set G) at hu
    rwa [horb] at hu
  have hLuni := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    h1221.simpleQTKE T h1221.maximal_faithful.1
  have hLorb : componentOrbit L (T : Subgroup G) = L :=
    le_antisymm (iSup_conjugates_le_of_le_normalizer L _ L le_rfl d.normalizes_L)
      (le_componentOrbit L _)
  have hMmax : IsMaximalTwoLocal M := by
    rw [d.local_normalizer, ←hLorb]
    exact hLuni.normalizer_maximal
  have hLn : ¬ L ≤ normalizer (B : Set G) := by
    intro hLN
    have he := hLuni.normalizer_unique _ hmax (sup_le hLN hTB)
    rw [hLorb, ←d.local_normalizer] at he
    exact hescape (hHN.trans_eq he)
  have hBM : ¬ B ≤ M := by
    intro hBM
    have hTM : (T : Subgroup G) ≤ M := d.local_normalizer ▸ d.normalizes_L
    exact hescape (hHN.trans_eq (huniq M hMmax (sup_le hBM hTM)).symm)
  exact ⟨hB,hHN,hmax,huniq,hLn,hBM⟩

/-- The actual selected component is Thompson generated under source escape. -/
theorem ordinary_selected_thompson_generation_of_escape
    (h1221 : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hescape : ¬ H ≤ M)
    (h1332 : SupercriticalSource.Source1332OneTwo T)
    (K : Subgroup H) (hK : K.IsCComponent)
    (hqK : IsQuasisimple (K ⧸ pCore 2 K))
    (hf : K.map H.subtype ∈ MainForward.faithfulLocalComponents T) :
    ⁅K.map H.subtype,elementaryAbelianMaxJ (T : Subgroup G)⁆ = K.map H.subtype := by
  let B := K.map H.subtype
  obtain ⟨hB,hHN,hmax,huniq,hLn,hBM⟩ :=
    ordinary_component_normalizer_conclusions_of_escape d h1221 hescape h1332 K hK hf
  have hTB : (T : Subgroup G) ≤ normalizer (B : Set G) := (h1332 B hf).1
  have hfB := ((Chapter1.Section02.Adequate.mem_faithfulLocalComponents_iff T B).mp hf).2
  let := hqK
  let eK : K ≃* B := K.equivMapOfInjective H.subtype H.subtype_injective
  have hqB : IsQuasisimple (B ⧸ pCore 2 B) := IsQuasisimple.of_mulEquiv
    (QuotientGroup.congr _ _ eK (pCore_map_iso 2 eK))
  have hLuni := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    h1221.simpleQTKE T h1221.maximal_faithful.1
  have hLorb : componentOrbit L (T : Subgroup G) = L :=
    le_antisymm (iSup_conjugates_le_of_le_normalizer L _ L le_rfl d.normalizes_L)
      (le_componentOrbit L _)
  have hMmax : IsMaximalTwoLocal M := by
    rw [d.local_normalizer, ←hLorb]
    exact hLuni.normalizer_maximal
  have hTM : (T : Subgroup G) ≤ M := d.local_normalizer ▸ d.normalizes_L
  have hout : Chapter3.HasMaximalOutside T (normalizer (B : Set G)) :=
    Chapter3.hasMaximalOutside_of_two_distinct hmax hMmax hTB hTM
      (by intro he; exact hBM (he.symm ▸ B.le_normalizer))
  have hc : centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) ≤
      normalizer (B : Set G) := by
    apply le_trans (centralizer_le (ordinary_line_le_sylow_omega d))
    apply le_trans (Subgroup.centralizer_le_normalizer _)
    rw [←d.first_normalizer]
    exact hHN
  exact Chapter3.Section02.source_component_thompson_generation
    d.counterexample.qtke T B hB hfB hqB hTB hout hc

/-- Full B.5 entry for the ordinary selected component, with Thompson generation
discharged from its actual source normalizer data. -/
theorem ordinary_selected_offender_entry_of_escape
    (h1221 : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hescape : ¬ H ≤ M)
    (h1332 : SupercriticalSource.Source1332OneTwo T)
    (K : Subgroup H) (hK : K.IsCComponent)
    (hqK : IsQuasisimple (K ⧸ pCore 2 K))
    (hf : K.map H.subtype ∈ MainForward.faithfulLocalComponents T) :
    let B := K.map H.subtype
    let J := Diagonal.localGroup B (sourceOne L T P) T
    let W := reducedTwoSubgroup J
    letI := (isPReduced_reducedPSubgroup (p := 2) (G := J)).elementary
    let C := centralizer (W : Set J)
    let q := QuotientGroup.mk' C
    let ρ := NormalElementaryQuotient.representation W q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
    let N := offenderSubgroup ρ
    (B.subgroupOf J).map q ≤ N ∧
      IsComponent N (((B.subgroupOf J).map q).subgroupOf N) ∧
      ChapterB.SourceInduction.NontrivialAdequateAlternative (ρ.comp N.subtype) :=
  ordinary_selected_offender_entry d h1332 K hK hqK hf
    (ordinary_selected_thompson_generation_of_escape d h1221 hescape h1332 K hK hqK hf)

end CFSG.Quasithin.Chapter13.Section03.Noncentrality
