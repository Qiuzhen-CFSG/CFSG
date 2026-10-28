module

public import CFSG.Quasithin.MainForward.SourceReduction
public import CFSG.Quasithin.ClassificationModels
public import CFSG.Quasithin.Chapter14.Section08
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Overgroup.SourceAt

/-!
# Forward reduction for the quasithin Main Theorem

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, Main Theorem 0.1.2 (p. 4) and its forward proof
(p. 1166; PDF p. 1183).

The current reduction uses the complete actual output lists for Theorem 2.1.1
and Theorem E as explicit branch-theorem hypotheses. Their inclusions in the
available main list are proved by the catalogue API. If neither closes the
input, the proof constructs a member of the actual `L_f(G,T)` for Theorem D,
with the uniform A₅-quotient choice used in Hypothesis 13.3.1(4) and a proper
SQTK local overgroup. Even order and nonemptiness of `M(T)` are proved upstream.

This is a conditional reduction, not Theorem 0.1.2. Final assembly still
requires the source proofs of 2.1.1, D/14.8.2, and E/15.4.25, the complete
output list (including the general Ree family), and the full known-simple
K-catalogue. In particular the partial output predicate below does not
silently discard the Ree case: every nonempty-family case is retained as
input for Theorem D.
-/

@[expose] public section

namespace CFSG.Quasithin.MainForward

open Theory.GroupTheory ClassificationModels

universe u
variable {G : Type u} [Group G] [Finite G] {K : GroupClass.{u}}

/-- The p. 1166 reduction after supplying the two source results for the
unique-overgroup and empty-family branches. The remaining branch is exactly
the nonempty-family input of Theorem D. -/
theorem forward_to_theoremD (h : IsSimpleQTKE K G)
    (h211 : ∀ T : Sylow 2 G,
      (∃! M : Subgroup G, IsMaximalTwoLocal M ∧ (T : Subgroup G) ≤ M) →
        IsTheorem211Model G)
    (hE : ∀ T : Sylow 2 G,
      1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      faithfulLocalComponents T = ∅ → IsTheoremEModel G) :
    IsQTKEModelWithoutReeF4 G ∨
      ∃ T : Sylow 2 G,
        1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard ∧
        (faithfulLocalComponents T).Nonempty := by
  classical
  let T : Sylow 2 G := Classical.choice inferInstance
  rcases source_cases h T with hone | ⟨hmany, hempty⟩ | ⟨hmany, hnonempty⟩
  · exact Or.inl ((h211 T
      ((maximalTwoLocalOvergroups_ncard_eq_one_iff _).mp hone)).toQTKEModelWithoutReeF4)
  · exact Or.inl ((hE T hmany hempty).toQTKEModelWithoutReeF4)
  · exact Or.inr ⟨T, hmany, hnonempty⟩

/-- A remaining Theorem D input supplies the precise quotient choice used
on pp. 1078–1079, together with a proper SQTK generated local subgroup.
The quotient and the A₅ identification are actual groups and equivalences. -/
theorem exists_theoremD_local_setup (h : IsSimpleQTKE K G)
    (T : Sylow 2 G) (hne : (faithfulLocalComponents T).Nonempty) :
    ∃ L ∈ faithfulLocalComponents T,
      (Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) →
        ∀ J ∈ faithfulLocalComponents T,
          Nonempty ((J ⧸ pCore 2 J) ≃* alternatingGroup (Fin 5))) ∧
      ∃ M ∈ maximalTwoLocalOvergroups (T : Subgroup G),
        L ⊔ (T : Subgroup G) ≤ M ∧
        (L ⊔ (T : Subgroup G) : Subgroup G) ≠ ⊤ ∧
        IsSQTK K (L ⊔ (T : Subgroup G) : Subgroup G) := by
  obtain ⟨L, hL, huniform⟩ :=
    Chapter14.Section08.exists_local_with_uniform_A5_quotient _ hne
  exact ⟨L, hL, huniform, localComponents_local_setup h T hL.1⟩

end CFSG.Quasithin.MainForward
