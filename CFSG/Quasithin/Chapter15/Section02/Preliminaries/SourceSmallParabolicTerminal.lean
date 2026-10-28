module

public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.SmallMixedRecognition
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenCriticalPair.ResidualTerminalReduction

/-!
# Excluding the original marked cubic action

The mixed A5/S3 size theorem supplies the global H-star wreath quotients in
the marked cubic row. The source constructs an actual offender residual input,
and the terminal equal-plane argument then excludes that row without assuming
any residual identity. Thus the small chosen action is marked five or Omega.
The mixed-size theorem and SmallSourcePrior retain their independent producers;
the marked-five and Omega terminal arguments are not asserted here.

Source: Aschbacher--Smith, 15.2.1--8 and 15.2.14--15,
printed pp.1104--1112, with the terminal argument on pp.1119--1120.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02
open Section01 Section03 ChapterD ChapterD.UniqueFactor ChosenGeometry ChapterD.CyclicSource
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- The marked cubic source branch is excluded using the mixed size input,
with no residual-identity or plane-uniqueness callback. -/
theorem source_chosen_contradiction_of_marked_cubic_and_mixed_size
    (hsize : ∀ (K A S : Subgroup G), ChapterF.Source.HypothesisF11 ![K,A] S →
      IsQuasithin (ChapterF.Source.generated ![K,A] S) →
      Chapter1.IsSylowIn 2 S (ChapterF.Source.generated ![K,A] S) →
      Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5)) →
      Nonempty ((A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3)) →
      ChapterF.Source.borel A S ≤ normalizer (S : Set G) → Nat.card S ≤ 256)
    (h : ChosenSmallSource T M Mc V) (hprior : SmallSourcePrior T M V)
    (hd : letI := h.prepared.elementary
      ∃ l : LocalGeneration ((imageRepresentation M V h.prepared.normalized).comp
        (Jhat (imageRepresentation M V h.prepared.normalized)).subtype),
        ChapterD.CyclicSource.DihedralMarking l 3 2) : False := by
  have hquotient : ∀ P ∈ Chapter3.HStar (T : Subgroup G) M,
      Nonempty ((P ⧸ pCore 2 P) ≃* Wreath) :=
    fun P hP => h.HStar_wreath_of_marked_cubic_of_mixed_size hsize hprior hd hP
  obtain ⟨P,hP,_,he⟩ := h.exists_wreath_local hquotient
  obtain ⟨C,d⟩ := h.exists_residualInput_of_preceding h.action_alternatives hP he
    (h.maximal_overgroups_of_marked_cubic hd)
  exact source_chosen_contradiction_of_marked_cubic_residual_input h d hquotient hd


/-- After the cubic exclusion, only the marked-five and Omega small actions remain. -/
theorem source_chosen_marked_five_or_omega_of_mixed_size
    (hsize : ∀ (K A S : Subgroup G), ChapterF.Source.HypothesisF11 ![K,A] S →
      IsQuasithin (ChapterF.Source.generated ![K,A] S) →
      Chapter1.IsSylowIn 2 S (ChapterF.Source.generated ![K,A] S) →
      Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5)) →
      Nonempty ((A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3)) →
      ChapterF.Source.borel A S ≤ normalizer (S : Set G) → Nat.card S ≤ 256)
    (h : ChosenSmallSource T M Mc V) (hprior : SmallSourcePrior T M V) :
    letI := h.prepared.elementary
    (∃ l : LocalGeneration ((imageRepresentation M V h.prepared.normalized).comp
      (Jhat (imageRepresentation M V h.prepared.normalized)).subtype),
      DihedralMarking l 5 2) ∨
      SourceCases.Omega (imageRepresentation M V h.prepared.normalized) := by
  let := h.prepared.elementary
  rcases h.small with ⟨l,p,m,hpm,hd⟩ | ho
  · have hm : m = 2 := h.marking_dimension l p m hd
    subst m
    rcases (primeDimensionOptions_iff p 2).mp hpm with ⟨rfl,_⟩ | ⟨rfl,_⟩
    · exact (source_chosen_contradiction_of_marked_cubic_and_mixed_size
        hsize h hprior ⟨l,hd⟩).elim
    · exact Or.inl ⟨l,hd⟩
  · exact Or.inr ho

end CFSG.Quasithin.Chapter15.Section02
