module

public import Theory.Mathieu.M24.LocalGeometry.EvenCatalogue.NormalizerOvergroups.TrioTranslations

/-!
# Explicit large elementary candidates in the native M24 Sylow group

The two six-generator candidates are the existing sextet and trio groups.
Their certified word lists have 64 distinct elements, and a point image
separates the two groups. Four further five-generator groups are specified
in the same Sylow enumeration for the large-elementary fusion calculation.
No exhaustiveness or normality of arbitrary elementary subgroups is asserted.

Source: Aschbacher–Smith H.14.1(1,5), printed pp.396–397.
-/

@[expose] public section
namespace Sporadic.Mathieu.M24ChapterHStabilizers.ElementaryFusion
open M24LocalGeometry
open SylowNormalizer.OrderEnumeration

/-- The four additional rows needed for the rank-five Sylow calculation. -/
def smallGeneratorIndex : Fin 4 → Fin 5 → Fin 1024 :=
  ![![5,57,80,129,641], ![7,48,98,256,642],
    ![14,16,38,384,512], ![14,27,76,386,518]]

noncomputable def smallGenerator (i : Fin 4) (j : Fin 5) : M24 :=
  (element (smallGeneratorIndex i j)).val

noncomputable def smallCandidate (i : Fin 4) : Subgroup M24 :=
  Subgroup.closure (Set.range (smallGenerator i))

theorem smallGenerator_mem (i : Fin 4) (j : Fin 5) :
    smallGenerator i j ∈ smallCandidate i := Subgroup.subset_closure ⟨j, rfl⟩

theorem smallCandidate_le_sylow (i : Fin 4) :
    smallCandidate i ≤ SylowNormalizer.candidate := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨j, rfl⟩
  exact (element (smallGeneratorIndex i j)).property

/-- Both six-generator candidates have exactly 64 native elements. -/
theorem candidate_card (k : Fin 2) : Nat.card (EvenCandidates.elementary k) = 64 := by
  let r : Fin 22 := if k = 0 then 20 else 21
  have hr := EvenCatalogue.NormalizerOvergroupsProof.last_ambient k
  let f : Fin 64 → EvenCatalogue.ambient r := fun j =>
    ⟨EvenCatalogue.NormalizerOvergroupsProof.rowElement r j,
      EvenCatalogue.NormalizerOvergroupsProof.rowElement_mem r j⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      have h := (EvenCatalogue.NormalizerOvergroupsProof.rowElement_eq_iff r a b).mp
        (congrArg (fun g : EvenCatalogue.ambient r => g.val) hab)
      have hi : ∀ k : Fin 2, Function.Injective
          (EvenCatalogue.NormalizerOvergroupsProof.rowCode (if k = 0 then 20 else 21)) := by
        decide +kernel
      exact hi k h
    · intro a
      obtain ⟨j, hj⟩ := (EvenCatalogue.NormalizerOvergroupsProof.mem_ambient_iff r a.val).mp
        a.property
      exact ⟨j, Subtype.ext hj⟩
  rw [← hr]
  exact (Nat.card_congr (Equiv.ofBijective f hf).symm).trans (Nat.card_fin 64)

/-- The trio generator moving point 0 to point 3 is outside the sextet candidate. -/
theorem candidates_distinct : EvenCandidates.elementary 0 ≠ EvenCandidates.elementary 1 := by
  intro h
  have hm := h ▸ EvenCandidates.generator_mem 0 2
  rw [← EvenCatalogue.NormalizerOvergroupsProof.last_ambient 1] at hm
  obtain ⟨j, hj⟩ :=
    (EvenCatalogue.NormalizerOvergroupsProof.mem_ambient_iff 21 _).mp hm
  have hp := congrArg (fun g : M24 => g.val 0) hj
  rw [EvenCatalogue.NormalizerOvergroupsProof.rowElement_apply,
    EvenCandidates.generator_apply] at hp
  have hn : ∀ j : Fin 64,
      EvenCatalogue.NormalizerOvergroupsProof.point
        (EvenCatalogue.NormalizerOvergroupsProof.rowCode 21 j) 0 ≠
          EvenCandidates.generatorPoint 0 2 0 := by decide +kernel
  exact hn j hp

end Sporadic.Mathieu.M24ChapterHStabilizers.ElementaryFusion
