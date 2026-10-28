module
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.Source.KnownSimple
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.ComponentReduction.SourceSwapped.Detection
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.NonnormalOuterSource.FourModels.Swapped

/-!
# Complete intrinsic three-complement embedding from the original local input

The source detection theorem constructs the actual component orbit or proves
normality. If the Sylow group fixes the component, the orbit is the component
itself and the complete invariant-three sieve applies. Otherwise the checked
swapped theorem gives its literal two-factor model. The full known-simple
Theorems A and C discharge every earlier classification input. The adequate
conclusion retains the Held alternative required by the intrinsic hypotheses.

Source: Aschbacher–Smith, Proposition 1.3.4, printed pp.509–511, with the
Held correction recorded in docs/quasithin-proof-basis.md.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.XiEmbedding
universe u

/-- The complete p=3 intrinsic theorem has only its original local, SQTK and
Sylow hypotheses, including the actual detected component and complement. -/
theorem LocalInput.adequate_three_knownSimple
    {G : Type u} [Group G] [Finite G] {T X P H : Subgroup G}
    (h : LocalInput 3 T X P H) (hH : IsSQTK KnownSimple.IsKnownSimple H)
    (hT : IsSylowIn 2 T H) : AdequateConclusion 3 T X P H := by
  let hA := fun (Y : Type u) [Group Y] [Finite Y] =>
    ChapterA.Section02.theoremA_knownSimple (G := Y)
  let hC := fun (Y : Type u) [Group Y] [Finite Y] =>
    ChapterA.Section02.theoremC_knownSimple (G := Y)
  rcases h.normal_or_detected_containment hA hC hH hT with
    hn | ⟨L,hL,hn,hcomm,hP,hX⟩
  · exact Or.inl hn
  · refine Or.inr ⟨L,hL.mem,hL.quasisimple,hX,?_⟩
    by_cases hi : T ≤ normalizer L
    · have horbit : componentOrbit L T = L :=
        le_antisymm (iSup_conjugates_le_of_le_normalizer L T L le_rfl hi)
          (le_componentOrbit L T)
      rw [horbit] at hn hcomm hP
      exact InvariantThree.Source.alternatives_knownSimple h hH hT hL.mem.1 hn
        hL.quasisimple hP hcomm
    · let hs : SwappedSylowInput KnownSimple.IsKnownSimple 3 T X P H L :=
        { toLocalInput := h
          sqtk := hH
          component := hL.mem
          quasisimple := hL.quasisimple
          orbit_normal := hn
          complement_le_orbit := hP
          orbit_commutator := hcomm
          noncentral := hL.noncentral_component_core
          not_invariant := hi
          sylow_two := hT }
      obtain ⟨he,hf,hm⟩ := SwappedSylow.embedding_of_theoremsAC hA hC hs
      exact Or.inl ⟨he,Or.inl ⟨hf,hm⟩⟩

end CFSG.Quasithin.Chapter1.XiEmbedding
