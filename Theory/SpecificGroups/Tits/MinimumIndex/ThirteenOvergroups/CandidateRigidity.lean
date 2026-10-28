module

public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.Seeds
public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.CandidateRigidity.Normalizer
public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.CandidateRigidity.Generation
public import Theory.SpecificGroups.Tits.MinimumIndex.ThirteenOvergroups.CandidateRigidity.DoubleCosetCover
public import Theory.SpecificGroups.Tits.MinimumIndex.FiveOvergroups.Representatives
public import Theory.SpecificGroups.Tits.MinimumIndex.FiveOvergroups.DoubleCosetCover
public import Theory.SpecificGroups.Tits.MinimumIndex.FiveOvergroups.RepresentativeGeneration

/-!
# Assembly of candidate-derived overgroup rigidity

A double-coset factorization by a subgroup already contained in L puts the
representative in L. The checked recovery words then exclude every representative
outside the candidate when L is proper. The max4 branch uses its proved
perfectness and the independently owned max4 cover and generation certificates.

The final theorem discharges the cover and generation premises using the
checked certificates for the literal max1, max2 and max4 candidates. Together
with the normalizer-placement theorem re-exported from Normalizer, it supplies
the rigidity and normalizer inputs of the thirteen-overgroup coverage reduction.
The conditional interfaces are retained for separate use of their reductions.

Source: the primary ATLAS Tits entry and literal subgroup programs preserved
with attribution in `MinimumIndex/source/`.
-/

namespace Tits.MinimumIndexThirteen
open Subgroup CandidateRigidity

private theorem le_of_doubleCoset_cover {G : Type*} [Group G] {n : Nat}
    (D M : Subgroup G) (r : Fin n → G) (hDM : D ≤ M)
    (hcover : ∀ x : G, ∃ (a b : D) (j : Fin n), x = a.val * r j * b.val)
    (hrep : ∀ j, r j ∈ M ∨ D ⊔ closure {r j} = ⊤)
    (L : Subgroup G) (hL : L ≠ ⊤) (hDL : D ≤ L) : L ≤ M := by
  intro x hx
  obtain ⟨a, b, j, he⟩ := hcover x
  rcases hrep j with hm | ht
  · rw [he]
    exact M.mul_mem (M.mul_mem (hDM a.property) hm) (hDM b.property)
  · have hr : r j ∈ L := by
      have hh := L.mul_mem (L.mul_mem (L.inv_mem (hDL a.property)) hx)
        (L.inv_mem (hDL b.property))
      have hh' : a.val⁻¹ * x * b.val⁻¹ = r j := by simp [he, mul_assoc]
      exact hh' ▸ hh
    have htop : ⊤ ≤ L := by
      rw [← ht]
      exact sup_le hDL ((closure_le _).mpr (Set.singleton_subset_iff.mpr hr))
    exact False.elim (hL (top_unique htop))

/-- For max1 and max2, the proved recovery words reduce rigidity to the literal
six-double-coset cover by the published commutator-generated subgroup. -/
public theorem candidateDerived_rigid_firstTwo_of_cover
    (hcover : ∀ (i : Fin 2) (x : Atlas1600Group),
      ∃ (a b : core (i.castLE (by decide))) (j : Fin 6),
        x = a.val * representative i j * b.val)
    (i : Fin 2) (L : Subgroup Atlas1600Group) (hL : L ≠ ⊤)
    (hD : candidateDerived (i.castLE (by decide)) ≤ L) :
    L ≤ candidate (i.castLE (by decide)) := by
  apply le_of_doubleCoset_cover (candidateDerived (i.castLE (by decide)))
    (candidate (i.castLE (by decide))) (representative i)
    (Subgroup.commutator_le_self _) ?_ ?_ L hL hD
  · intro x
    obtain ⟨a, b, j, he⟩ := hcover i x
    exact ⟨⟨a.val, core_le_derived _ a.property⟩,
      ⟨b.val, core_le_derived _ b.property⟩, j, he⟩
  · intro j
    by_cases hj : j.val < 2
    · exact Or.inl (representative_small_mem i j hj)
    · exact Or.inr (representative_generates i j (by omega))

/-- The perfect max4 candidate has the requested rigidity once its independently
owned cover and generation certificates are supplied. -/
public theorem candidateDerived_rigid_two_of_certificates
    (hcover : ∀ x : Atlas1600Group,
      ∃ (a b : MinimumIndexCandidates.max4) (j : Fin 7),
        x = a.val * MinimumIndexFiveOvergroups.max4Rep j * b.val)
    (hgenerate : ∀ (j : Fin 7), j ≠ 0 →
      MinimumIndexCandidates.max4 ⊔ closure {MinimumIndexFiveOvergroups.max4Rep j} = ⊤)
    (L : Subgroup Atlas1600Group) (hL : L ≠ ⊤) (hD : candidateDerived 2 ≤ L) :
    L ≤ candidate 2 := by
  rw [candidateDerived_two_eq] at hD
  apply le_of_doubleCoset_cover MinimumIndexCandidates.max4 MinimumIndexCandidates.max4
    MinimumIndexFiveOvergroups.max4Rep le_rfl hcover ?_ L hL hD
  intro j
  by_cases hj : j = 0
  · subst j
    left
    rw [MinimumIndexFiveOvergroups.max4Rep_zero]
    exact Subgroup.one_mem _
  · exact Or.inr (hgenerate j hj)

/-- Conditional final rigidity assembly. All missing certificates remain
explicit; normalizer placement is already unconditional. -/
public theorem candidateDerived_rigid_of_covers
    (hcover12 : ∀ (i : Fin 2) (x : Atlas1600Group),
      ∃ (a b : core (i.castLE (by decide))) (j : Fin 6),
        x = a.val * representative i j * b.val)
    (hcover4 : ∀ x : Atlas1600Group,
      ∃ (a b : MinimumIndexCandidates.max4) (j : Fin 7),
        x = a.val * MinimumIndexFiveOvergroups.max4Rep j * b.val)
    (hgenerate4 : ∀ (j : Fin 7), j ≠ 0 →
      MinimumIndexCandidates.max4 ⊔ closure {MinimumIndexFiveOvergroups.max4Rep j} = ⊤)
    (i : Fin 3) (L : Subgroup Atlas1600Group) (hL : L ≠ ⊤)
    (hD : candidateDerived i ≤ L) : L ≤ candidate i := by
  fin_cases i
  · exact candidateDerived_rigid_firstTwo_of_cover hcover12 0 L hL hD
  · exact candidateDerived_rigid_firstTwo_of_cover hcover12 1 L hL hD
  · exact candidateDerived_rigid_two_of_certificates hcover4 hgenerate4 L hL hD

/-- A proper subgroup containing the ambient derived subgroup of one of the
three literal candidates is contained in that candidate. All cover and
generation certificates are discharged on the actual ATLAS carrier. -/
public theorem candidateDerived_rigid (i : Fin 3) (L : Subgroup Atlas1600Group)
    (hL : L ≠ ⊤) (hD : candidateDerived i ≤ L) : L ≤ candidate i := by
  exact candidateDerived_rigid_of_covers core_doubleCoset_cover
    MinimumIndexFiveOvergroups.max4_doubleCoset_cover
    MinimumIndexFiveOvergroups.max4_rep_generates i L hL hD

end Tits.MinimumIndexThirteen
