module
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Local
public import CFSG.Quasithin.Chapter1.Section01Inheritance
public import CFSG.Quasithin.Chapter1.Section01Overgroups

/-!
# The original Chapter 1.1 inputs for E.6

Characteristic two passes to centralizers by 1.1.3(2). The original
condition (E) at T gives the center-intersection normalizer criterion
1.1.4(3) and the Sylow-overgroup criterion 1.1.4(6). Their source theorems
therefore supply every field of EarlierLocalFacts from Hypothesis E.6.1.
The intrinsic center of T is explicitly mapped to T ∩ C_G(T).

Source: Aschbacher–Smith, 1.1.3–4, printed pp.500–501, and E.6.6.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06
variable {G : Type*} [Group G] [Finite G]
variable {K : GroupClass} {T : Sylow 2 G} {M V : Subgroup G}

/-- Supply all original local inheritance facts used by E.6.6 and E.6.9. -/
theorem source_earlierLocalFacts (h : HypothesisE61 K T M V) : EarlierLocalFacts T := by
  refine ⟨?_,?_,?_⟩
  · intro A B hB hAB hp
    exact Chapter1.mem_He_iff.mp (pCoreIn_selfCentralizing_centralizer
      (Chapter1.mem_He_iff.mpr hB) hp hAB)
  · intro A hp hne hint
    have hz : (center (T : Subgroup G)).map (T : Subgroup G).subtype =
        (T : Subgroup G) ⊓ centralizer (T : Set G) := by
      ext x
      constructor
      · rintro ⟨y,hy,rfl⟩
        exact ⟨y.property,mem_centralizer_iff.mpr (fun z hz =>
          congrArg Subtype.val (mem_center_iff.mp hy ⟨z,hz⟩))⟩
      · intro hx
        exact ⟨⟨x,hx.1⟩,mem_center_iff.mpr (fun y =>
          Subtype.ext (mem_centralizer_iff.mp hx.2 y y.property)),rfl⟩
    exact Chapter1.mem_He_iff.mp
      (Chapter1.lemma_1_1_4_3 T (h.simpleQTKE.evenCharacteristic T) hne hp
        (by rw [hz];exact hint)).2.2
  · intro B hcore hTB
    exact Chapter1.mem_He_iff.mp
      (Chapter1.lemma_1_1_4_6 T (h.simpleQTKE.evenCharacteristic T) ⟨hcore,hTB⟩)
end CFSG.Quasithin.ChapterE.Section06
