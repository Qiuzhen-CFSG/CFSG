module

public import Theory.SpecificGroups.Tits.Atlas1600ParrottCertificate
public import Theory.SpecificGroups.Tits.GeneratedImage

/-!
# A surjective Parrott presentation map onto the Atlas model

The concrete permutation certificates give an assignment of Parrott's ten
original generators to the degree-1600 Atlas group. All 37 defining relators
vanish. The two Atlas generators are words in the assigned elements, so the
universal homomorphism is surjective.

The presentation and conventions are Parrott (1972), p. 683, transcribed in
`refs/original/n-group-global/parrott-tits-presentation.md`. This establishes
a concrete quotient; it does not assert faithfulness of the presented group.
-/

namespace Tits

/-- A generating realization of all ten Parrott generators in the Atlas model. -/
public def atlas1600ParrottAssignment (i : ParrottGenerator) : Atlas1600Group :=
  ⟨Atlas1600ParrottData.permutation i, Atlas1600ParrottData.permutation_mem i⟩

/-- The permutation underlying an assigned Parrott generator. This equation
supports concrete certificates without exposing the assignment's body. -/
@[simp] public theorem atlas1600ParrottAssignment_val (i : ParrottGenerator) :
    (atlas1600ParrottAssignment i).val = Atlas1600ParrottData.permutation i := by rfl

/-- The concrete assignment satisfies every original defining relation. -/
public theorem atlas1600ParrottAssignment_relations :
    SatisfiesParrottRelations atlas1600ParrottAssignment := by
  have hlift : atlas1600Subgroup.subtype.comp (FreeGroup.lift atlas1600ParrottAssignment) =
      FreeGroup.lift Atlas1600ParrottData.permutation := by
    ext i
    rfl
  intro i
  apply Subtype.ext
  change (atlas1600Subgroup.subtype.comp (FreeGroup.lift atlas1600ParrottAssignment))
    (parrottRelator i) = 1
  rw [hlift]
  exact Atlas1600ParrottData.relations i

/-- The induced map from Parrott's presentation is onto the Atlas group. -/
public theorem atlas1600ParrottLift_surjective :
    Function.Surjective
      (parrottLift atlas1600ParrottAssignment atlas1600ParrottAssignment_relations) := by
  let φ := parrottLift atlas1600ParrottAssignment atlas1600ParrottAssignment_relations
  let ψ := atlas1600Subgroup.subtype.comp φ
  have hgen (i : ParrottGenerator) : Atlas1600ParrottData.permutation i ∈ ψ.range := by
    refine ⟨parrottGenerator i, ?_⟩
    exact congrArg (fun x : Atlas1600Group => x.val)
      (parrottLift_generator atlas1600ParrottAssignment atlas1600ParrottAssignment_relations i)
  have ha : atlas1600A ∈ ψ.range := by
    rw [Atlas1600ParrottData.atlasA_word]
    exact hgen .r1
  have hb : atlas1600B ∈ ψ.range := by
    rw [Atlas1600ParrottData.atlasB_word]
    with_reducible repeat first
      | apply Subgroup.mul_mem
      | apply Subgroup.inv_mem
      | exact hgen _
  have hsub : atlas1600Subgroup ≤ ψ.range := by
    apply (Subgroup.closure_le ψ.range).mpr
    intro x hx
    rcases hx with rfl | hx
    · exact ha
    · obtain rfl := Set.mem_singleton_iff.mp hx
      exact hb
  intro x
  obtain ⟨y, hy⟩ := hsub x.property
  exact ⟨y, Subtype.ext hy⟩

/-- The assigned generators generate the entire Atlas model. -/
public theorem atlas1600ParrottAssignment_generates :
    Subgroup.closure (Set.range atlas1600ParrottAssignment) = ⊤ :=
  (parrottLift_surjective_iff _ atlas1600ParrottAssignment_relations).mp
    atlas1600ParrottLift_surjective

end Tits
