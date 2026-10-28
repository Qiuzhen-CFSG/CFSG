module

public import Theory.SpecificGroups.ONan.Presentation.Marking
public import Theory.SpecificGroups.ONan.OddCoverLifting

/-!
# The concrete four-involution marking in odd central covers

The unique square-one lifts of the four marked matrix involutions generate
any perfect odd-primary central cover occurring in the source application.
Their word evaluation projects to the same marked evaluation on the actual
matrix model. In particular the two original matrix generators are recovered
by the explicit words in `Marking`.

This discharges the generating-family input of the involution-lifting route
in Soicher, *Presentations of Some Finite Groups* (1985), I.6, for the literal
central quotient in Aschbacher--Smith A.2.19. It supplies neither a complete
presentation nor a compatible homomorphism from the derived linear cover.
The relator-kernel and central-relator calculations remain necessary.
-/

namespace ONan.Presentation

/-- Any lift of the marking intertwines free-word evaluation with the source's
literal central-quotient map. -/
public theorem lift_evaluation_comp
    {G : Type*} [Group G] (e : G ⧸ Subgroup.center G ≃* Model)
    (a : Fin 4 → G)
    (ha : ∀ i, e (QuotientGroup.mk' (Subgroup.center G) (a i)) = involutionGenerator i) :
    (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center G))).comp
      (FreeGroup.lift a) = involutionEvaluation := by
  apply FreeGroup.ext_hom
  intro i
  change e (QuotientGroup.mk' (Subgroup.center G)
    (FreeGroup.lift a (FreeGroup.of i))) = FreeGroup.lift involutionGenerator (FreeGroup.of i)
  simpa only [FreeGroup.lift_apply_of] using ha i

/-- The marking retains explicit correspondence with both original generators
under the source central quotient. -/
public theorem lift_original_words
    {G : Type*} [Group G] (e : G ⧸ Subgroup.center G ≃* Model)
    (a : Fin 4 → G)
    (ha : ∀ i, e (QuotientGroup.mk' (Subgroup.center G) (a i)) = involutionGenerator i) :
    e (QuotientGroup.mk' (Subgroup.center G) (FreeGroup.lift a originalAWord)) = generatorA ∧
    e (QuotientGroup.mk' (Subgroup.center G) (FreeGroup.lift a originalBWord)) = generatorB := by
  have h := lift_evaluation_comp e a ha
  exact ⟨(DFunLike.congr_fun h originalAWord).trans originalAWord_evaluation,
    (DFunLike.congr_fun h originalBWord).trans originalBWord_evaluation⟩

/-- In the source's perfect odd-primary central cover, the actual four marked
involutions have unique square-one lifts. These generate the cover and preserve
all pairwise Coxeter relations. Completeness of a presentation is not assumed. -/
public theorem existsUnique_generating_involution_lift
    {G : Type*} [Group G] [Finite G] [Group.IsPerfect G]
    {p : ℕ} (hp : p.Prime) (hpodd : p ≠ 2)
    (hP : IsPGroup p (Subgroup.center G))
    (e : G ⧸ Subgroup.center G ≃* Model) :
    ∃! a : Fin 4 → G,
      (∀ i, e (QuotientGroup.mk' (Subgroup.center G) (a i)) = involutionGenerator i ∧
        a i ^ 2 = 1) ∧
      Subgroup.closure (Set.range a) = ⊤ ∧
      (∀ i j n, (involutionGenerator i * involutionGenerator j) ^ n = 1 →
        (a i * a j) ^ n = 1) := by
  obtain ⟨a, ⟨ha, hcox⟩, huniq⟩ :=
    Cover.existsUnique_involution_lift_family hp hpodd hP e
      involutionGenerator involutionGenerator_pow_two
  refine ⟨a, ⟨ha, ?_, hcox⟩, ?_⟩
  · let q := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center G))
    have hcomp : q.comp (FreeGroup.lift a) = involutionEvaluation :=
      lift_evaluation_comp e a (fun i => (ha i).1)
    have hker : q.ker = Subgroup.center G := by
      ext x
      change e (QuotientGroup.mk' (Subgroup.center G) x) = 1 ↔ x ∈ Subgroup.center G
      rw [e.map_eq_one_iff]
      exact QuotientGroup.eq_one_iff x
    apply FreeGroup.lift_surjective_iff_closure_range_eq_top.mp
    apply PerfectCentralCovering.surjective_of_comp_surjective_of_ker_le_center_of_isPerfect
      q (FreeGroup.lift a) _ hker.le
    rw [hcomp]
    exact involutionEvaluation_surjective
  · intro b hb
    exact huniq b ⟨hb.1, hb.2.2⟩

end ONan.Presentation
