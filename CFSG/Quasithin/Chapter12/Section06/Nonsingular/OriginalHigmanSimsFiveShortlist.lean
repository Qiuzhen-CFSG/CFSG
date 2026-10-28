module
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingFiveShortlist

/-!
# The full-Sylow local A5 comparison for the original HS configuration

Restrict the actual Sylow to the actual ordinary component before invoking
A.3.14. Equality retains the literal A5 identification; a proper inclusion
retains the complete proven shortlist. No overcomponent classification
callback or faithful-module assumption is added.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section06.OriginalHigmanSimsFiveShortlist
open ChapterA.Section03 ChapterA.Section03.SourceEmbeddings
variable {G : Type*} [Group G] [Finite G]

/-- A component containing an actual full-Sylow-normalized local A5 is A5
itself or belongs to the genuine proper-container shortlist. -/
theorem five_or_shortlist
    (hG : IsSQTK KnownSimple.IsKnownSimple G) (hO : pCore 2 G = ⊥)
    (T : Sylow 2 G) {B K : Subgroup G}
    (hB : B ∈ localCComponents T) (hK : IsComponent G K) (hBK : B ≤ K)
    (hTB : (T : Subgroup G) ≤ normalizer (B : Set G))
    (eB : B ≃* alternatingGroup (Fin 5)) :
    Nonempty (K ≃* alternatingGroup (Fin 5)) ∨ AlternatingFive.Shortlist K := by
  classical
  let := hK.2
  obtain ⟨S,_,hl,hn⟩ := exists_local_sylow_normalizing T hB hK.1 hBK hTB
  let e : B.subgroupOf K ≃* alternatingGroup (Fin 5) :=
    (subgroupOfEquivOfLe hBK).trans eB
  by_cases heq : B.subgroupOf K = ⊤
  · exact .inl ⟨(topEquiv (G := K)).symm.trans
      ((MulEquiv.subgroupCongr heq.symm).trans e)⟩
  · right
    rcases quasisimple_containing_component_models_knownSimple hG hO hK.isCComponent with
      ⟨_,hm⟩ | ⟨_,hm⟩
    · exact AlternatingFive.shortlist_of_theoremC S hl hn e heq hm
    · exact .inr (.inl (AlternatingFive.seven_of_threeCover S hl hn e heq hm))

end CFSG.Quasithin.Chapter12.Section06.OriginalHigmanSimsFiveShortlist
