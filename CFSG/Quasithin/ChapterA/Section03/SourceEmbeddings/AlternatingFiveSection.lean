module

public import Theory.SpecificGroups.Alternating.SevenFiveSection
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingFive
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Quotients

/-!
# The marked alternating-seven image of a local A₅ section

Transport the original local C-component through a surjection with solvable
kernel and with a two-group kernel on the local component. An A₅ two-core quotient becomes an actual A₅ in A₇, and the image
of the original full Sylow normalizes it. The seven-letter placement theorem
then identifies this same image as the pointwise stabilizer of two letters.
Its cubic elements are single three-cycles.

The exact restricted kernel is retained: it is the original two-core.
`alternatingGroup.SevenFiveSection.imageFiveEquiv_apply` identifies the image
marking with the original quotient marking on every element.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 10.2.9,
printed pp.751–752, the alternating-seven reduced-action row; the local
placement uses A.3.12 and C.5.13. The rank-two rows do not have trivial
smaller two-core and are not covered by this argument.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings

private theorem image_local {G : Type*} [Group G] [Finite G]
    (f : G →* alternatingGroup (Fin 7)) (hf : Function.Surjective f)
    (hks : Group.IsSolvable f.ker) (S : Sylow 2 G) (L : Subgroup G)
    (hL : L ∈ localCComponents S) :
    L.map f ∈ localCComponents (S.mapSurjective hf) := by
  let : Group.IsSolvable f.ker := hks
  have h := Chapter1.Section02.localCComponents_map_of_solvable_ker hL f
  simpa only [Sylow.coe_mapSurjective] using h

/-- The actual image is normalized by the image of the original full Sylow. -/
theorem alternatingSeven_five_section_image_normalized {G : Type*} [Group G] [Finite G]
    (f : G →* alternatingGroup (Fin 7)) (hf : Function.Surjective f)
    (hks : Group.IsSolvable f.ker) (S : Sylow 2 G) (L : Subgroup G)
    (hL : L ∈ localCComponents S) (hk : IsPGroup 2 (f.subgroupMap L).ker)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) :
    (S : Subgroup G).map f ≤ normalizer (L.map f : Set (alternatingGroup (Fin 7))) := by
  exact alternatingSeven_local_five_normalized _
    (alternatingGroup.SevenFiveSection.imageFiveEquiv f L hk e) (S.mapSurjective hf)
    (image_local f hf hks S L hL)

/-- The actual local image has trivial two-core and is the five-letter A₅. -/
theorem alternatingSeven_five_section_image {G : Type*} [Group G] [Finite G]
    (f : G →* alternatingGroup (Fin 7)) (hf : Function.Surjective f)
    (hks : Group.IsSolvable f.ker) (S : Sylow 2 G) (L : Subgroup G)
    (hL : L ∈ localCComponents S) (hk : IsPGroup 2 (f.subgroupMap L).ker)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) :
    pCore 2 (L.map f) = ⊥ ∧ (f.subgroupMap L).ker = pCore 2 L ∧
    ∃ i j : Fin 7, i ≠ j ∧
      L.map f = fixingSubgroup (alternatingGroup (Fin 7)) ({i,j} : Set (Fin 7)) := by
  obtain ⟨hcore,hker⟩ := alternatingGroup.SevenFiveSection.image_twoCore_eq_bot_and_ker_eq f L hk e
  refine ⟨hcore,hker,?_⟩
  let d := alternatingGroup.SevenFiveSection.imageFiveEquiv f L hk e
  exact Theory.SpecificGroups.Alternating.SevenFivePlacement.exists_fixed_pair _ d
    (S.mapSurjective hf) (alternatingSeven_five_section_image_normalized f hf hks S L hL hk e)

/-- Every cubic in the actual local image is a single three-cycle in A₇. -/
theorem alternatingSeven_five_section_image_threeCycle {G : Type*} [Group G] [Finite G]
    (f : G →* alternatingGroup (Fin 7)) (hf : Function.Surjective f)
    (hks : Group.IsSolvable f.ker) (S : Sylow 2 G) (L : Subgroup G)
    (hL : L ∈ localCComponents S) (hk : IsPGroup 2 (f.subgroupMap L).ker)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (a : L.map f) (ha : orderOf a = 3) : a.val.val.IsThreeCycle := by
  let d := alternatingGroup.SevenFiveSection.imageFiveEquiv f L hk e
  exact Theory.SpecificGroups.Alternating.SevenFivePlacement.isThreeCycle_of_order_three _ d
    (S.mapSurjective hf) (alternatingSeven_five_section_image_normalized f hf hks S L hL hk e) a ha

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings
