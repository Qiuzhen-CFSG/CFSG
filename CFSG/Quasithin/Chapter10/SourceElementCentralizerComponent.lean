module
public import CFSG.Quasithin.Chapter10.SourceA5ElementComponent
public import CFSG.Quasithin.Chapter10.SourceElementCentralizerSetup
public import Theory.GroupTheory.CComponent.FixedOrbitClosure

/-!
# The enlarged component in an escaping element centralizer

For an arbitrary nonidentity vector in the original Sylow group, a Sylow
centralizer normalizing L gives the unique normal C-component containing L.
The vector itself supplies the nontrivial two-core required by original
1.2.4. Component minimality shows that L normally generates this component.
The original normalizer bound from 10.2.6 then forces an escaping centralizer
to contain a strictly larger component which also escapes M.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Proposition 10.2.9(1), printed p.750.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
include D

omit D [Finite G] in
private theorem centralizer_core_ne_bot {v : G}
    (hvT : v ∈ (T : Subgroup G)) (hv1 : v ≠ 1)
    {X : Subgroup G} (hvX : v ∈ X) (hX : X ≤ centralizer ({v} : Set G)) :
    X.pCoreIn 2 ≠ ⊥ := by
  have hp : IsPGroup 2 (zpowers v) := T.isPGroup'.to_le (zpowers_le.mpr hvT)
  have hn : X ≤ normalizer (zpowers v : Set G) := by
    apply le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    rw [zpowers_eq_closure,centralizer_closure]
    exact hX
  have hle := le_pCoreIn_of_normalizes hp (zpowers_le.mpr hvX) hn
  intro he
  exact hv1 (mem_bot.mp (he ▸ hle (mem_zpowers v)))

/-- The actual Sylow centralizer produces a normal containing component. -/
theorem source_element_containing_component_of_sylow
    {v : G} (hvT : v ∈ (T : Subgroup G)) (hv1 : v ≠ 1)
    (hvL : v ∈ centralizer (L : Set G))
    (hs : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({v} : Set G))
      (centralizer ({v} : Set G)))
    (hn : (T : Subgroup G) ⊓ centralizer ({v} : Set G) ≤ normalizer (L : Set G)) :
    ∃ I : Subgroup G, L ≤ I ∧ I ≤ centralizer ({v} : Set G) ∧
      (I.subgroupOf (centralizer ({v} : Set G))).IsCComponent ∧
      centralizer ({v} : Set G) ≤ normalizer (I : Set G) := by
  let X := centralizer ({v} : Set G)
  let R := (T : Subgroup G) ⊓ X
  have hvX : v ∈ X := mem_centralizer_singleton_iff.mpr rfl
  have hLX : L ≤ X := fun l hl => mem_centralizer_singleton_iff.mpr (hvL l hl)
  have hRX : R ≤ X := inf_le_right
  have hvR : v ∈ R := ⟨hvT,hvX⟩
  have hcoreX := centralizer_core_ne_bot hvT hv1 hvX le_rfl
  have hlocal : L ∈ Chapter1.L G R := by
    refine ⟨D.maximal.1.1.subgroupOf_of_le le_sup_left
      (sup_le le_sup_left (inf_le_left.trans le_sup_right)),?_,?_⟩
    · exact hs.restrict le_sup_right (sup_le hLX hRX)
    · exact centralizer_core_ne_bot hvT hv1 (mem_sup_right hvR) (sup_le hLX hRX)
  obtain ⟨P,hP⟩ := hs
  have hP' : (P : Subgroup X) = R.subgroupOf X := by
    apply Subgroup.map_injective X.subtype_injective
    rw [hP,map_subgroupOf_eq_of_le hRX]
  have hlocalX : L.subgroupOf X ∈ Chapter1.L X (P : Subgroup X) := by
    rw [hP']
    exact (Chapter1.mem_LIn_iff_subgroupOf hRX hLX).mp ⟨hLX,hlocal⟩
  have hPL : (P : Subgroup X) ≤ normalizer (L.subgroupOf X : Set X) := by
    rw [hP',←subgroupOf_normalizer_eq hLX]
    exact comap_mono hn
  obtain ⟨K,⟨hK,hLK,hKn⟩,_⟩ :=
    Chapter1.Section02.lemma_1_2_4_containment_normality_source
      (Chapter1.Section02.uniqueness_local_quotient_sqtk D.simpleQTKE hcoreX) P hlocalX hPL
  let I := K.map X.subtype
  have hIX : I ≤ X := map_subtype_le K
  have he : I.subgroupOf X = K := comap_map_eq_self_of_injective X.subtype_injective K
  refine ⟨I,?_,hIX,he.symm ▸ hK,?_⟩
  · rw [←map_subgroupOf_eq_of_le hLX]
    exact map_mono hLK
  · exact (normal_subgroupOf_iff_le_normalizer hIX).mp (he.symm ▸ hKn)

/-- The original component normally generates every containing C-component. -/
theorem source_containing_component_normal_generation
    {I X : Subgroup G} (hLI : L ≤ I) (hIX : I ≤ X)
    (hI : (I.subgroupOf X).IsCComponent) : componentOrbit L I = I := by
  let W := componentOrbit L I
  have hWI : W ≤ I := iSup_conjugates_le_of_le_normalizer L I I hLI I.le_normalizer
  have hLperfect : Group.IsPerfect L := by
    let := D.maximal.1.1.perfect
    exact Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe
      (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left)).toMonoidHom)
      (subgroupOfEquivOfLe le_sup_left).surjective
  let := hLperfect
  let : Group.IsPerfect W := isPerfect_iSup_conjugates L I
  let : Group.IsPerfect (W.subgroupOf I) := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hWI).symm.toMonoidHom) (subgroupOfEquivOfLe hWI).symm.surjective
  have hn : (W.subgroupOf I).Normal :=
    normal_subgroupOf_of_le_normalizer (le_normalizer_componentOrbit L I)
  have hLne : L ≠ ⊥ := by
    intro he
    exact D.maximal.1.1.ne_bot (by simp only [he,bot_subgroupOf])
  have hWne : W.subgroupOf I ≠ ⊥ := by
    intro he
    have he' := congrArg (Subgroup.map I.subtype) he
    rw [map_subgroupOf_eq_of_le hWI,Subgroup.map_bot] at he'
    exact hLne (le_bot_iff.mp ((le_componentOrbit L I).trans he'.le))
  have hII := hI.subgroupOf_of_le (show I ≤ I from le_rfl) hIX
  have hmin := hII.minimal (W.subgroupOf I) (by rw [subgroupOf_self]; exact le_top)
    hWne inferInstance hn.isSubnormal
  have hm := map_mono (f := I.subtype) hmin
  rw [map_subgroupOf_eq_of_le (show I ≤ I from le_rfl),map_subgroupOf_eq_of_le hWI] at hm
  exact le_antisymm hWI hm

/-- The original 10.2.6 normalizer bound makes the containing component escape M. -/
theorem source_element_containing_component_escape
    (hNL : normalizer (L : Set G) ≤ D.maximalLocal)
    {v : G} (hescape : ¬ centralizer ({v} : Set G) ≤ D.maximalLocal)
    {I : Subgroup G} (hLI : L ≤ I) (hIX : I ≤ centralizer ({v} : Set G))
    (hI : (I.subgroupOf (centralizer ({v} : Set G))).IsCComponent)
    (hIn : centralizer ({v} : Set G) ≤ normalizer (I : Set G)) :
    L < I ∧ ¬ I ≤ D.maximalLocal := by
  have hne : L ≠ I := fun he => hescape (hIn.trans (he ▸ hNL))
  refine ⟨lt_of_le_of_ne hLI hne,?_⟩
  intro hIM
  have hLC := D.component_in_maximalLocal.subgroupOf_of_le hLI hIM
  have hIC := hI.subgroupOf_of_le (show I ≤ I from le_rfl) hIX
  have he : L.subgroupOf I = I.subgroupOf I := hLC.eq_of_le hIC (comap_mono hLI)
  have hm := congrArg (Subgroup.map I.subtype) he
  rw [map_subgroupOf_eq_of_le hLI,map_subgroupOf_eq_of_le (show I ≤ I from le_rfl)] at hm
  exact hne hm

/-- Actual consumer of the Sylow preparation and original 10.2.6: the
escaping centralizer has a strictly larger, normally generated component. -/
theorem source_escaping_element_component
    (hNL : normalizer (L : Set G) ≤ D.maximalLocal)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {v : G} (hvT : v ∈ (T : Subgroup G)) (hv1 : v ≠ 1)
    (hvL : v ∈ centralizer (L : Set G))
    (hv0 : v ∉ centralizer (localOrbit T L : Set G))
    (hs : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({v} : Set G))
      (centralizer ({v} : Set G)))
    (hescape : ¬ centralizer ({v} : Set G) ≤ D.maximalLocal) :
    ∃ I : Subgroup G, L < I ∧ I ≤ centralizer ({v} : Set G) ∧
      (I.subgroupOf (centralizer ({v} : Set G))).IsCComponent ∧
      centralizer ({v} : Set G) ≤ normalizer (I : Set G) ∧
      ¬ I ≤ D.maximalLocal ∧ componentOrbit L I = I := by
  have hstab : (T : Subgroup G) ⊓ centralizer ({v} : Set G) ≤ normalizer (L : Set G) :=
    (inf_le_inf (le_normalizer_componentOrbit L T) le_rfl).trans
      (source_nonnormal_element_centralizer_stabilizes D hn hvL hv0)
  obtain ⟨I,hLI,hIX,hI,hIn⟩ :=
    source_element_containing_component_of_sylow D hvT hv1 hvL hs hstab
  obtain ⟨hlt,hout⟩ := source_element_containing_component_escape D hNL hescape hLI hIX hI hIn
  exact ⟨I,hlt,hIX,hI,hIn,hout,source_containing_component_normal_generation D hLI hIX hI⟩


/-- The two proved Sylow-normalizer branches feed the actual enlarged-component
construction with only local Sylow placement left as the source choice of v. -/
theorem source_escaping_element_component_of_local_sylow
    (hNL : normalizer (L : Set G) ≤ D.maximalLocal)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {v : G} (hv : v ∈ D.fullModule) (hv1 : v ≠ 1)
    (hvL : v ∈ centralizer (L : Set G))
    (hv0 : v ∉ centralizer (localOrbit T L : Set G))
    (hbranch :
      elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.fullModule : Set G) ∨
      (normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal ∧
        ChapterB.baumann (T : Subgroup G) ≤ centralizer ({v} : Set G)))
    (hs : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({v} : Set G))
      (D.maximalLocal ⊓ centralizer ({v} : Set G)))
    (hescape : ¬ centralizer ({v} : Set G) ≤ D.maximalLocal) :
    ∃ I : Subgroup G, L < I ∧ I ≤ centralizer ({v} : Set G) ∧
      (I.subgroupOf (centralizer ({v} : Set G))).IsCComponent ∧
      centralizer ({v} : Set G) ≤ normalizer (I : Set G) ∧
      ¬ I ≤ D.maximalLocal ∧ componentOrbit L I = I := by
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    D.simpleQTKE T D.maximal
  apply source_escaping_element_component D hNL hn (D.fullModule_le_sylow hu hv)
    hv1 hvL hv0 _ hescape
  rcases hbranch with hJ | ⟨h1021,hB⟩
  · exact source_element_sylow_of_thompson_centralizes D hJ hv hs
  · exact source_element_sylow_of_baumann_centralizes D h1021 hB hs

end CFSG.Quasithin.Chapter10
