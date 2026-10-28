module
public import Theory.SpecificGroups.Held.Automorphisms.OuterInvolution.FixedStructure.OrbitCover.ActionData
/-!
# The orbit letters and their pair coordinates

Closure induction proves that the displayed 21 letters are exactly the orbit
of letter 30. Their pair labels enumerate the two-subsets of seven letters.
Source: the actual ATLAS Held action for GLS3 Table 5.3p; the generator
comparisons are checked in `ActionData`.
-/

@[expose] public section
noncomputable section
open Subgroup
namespace Held.OuterInvolution.FixedStructure
def orbitPointsSet : Set (Fin 2058) := Set.range orbitPoints

theorem orbitPointsSet_firstGenerator :
    ∀ x ∈ orbitPointsSet, firstGenerator • x ∈ orbitPointsSet := by
  rintro x ⟨i, hi⟩
  refine ⟨pointPermX i, ?_⟩
  exact (firstGenerator_smul_orbitPoints i).symm.trans
    (congrArg (fun z => firstGenerator • z) hi)

theorem orbitPointsSet_secondGenerator :
    ∀ x ∈ orbitPointsSet, secondGenerator • x ∈ orbitPointsSet := by
  rintro x ⟨i, hi⟩
  refine ⟨pointPermY i, ?_⟩
  exact (secondGenerator_smul_orbitPoints i).symm.trans
    (congrArg (fun z => secondGenerator • z) hi)

theorem orbitPointsSet_firstGenerator_inv :
    ∀ x ∈ orbitPointsSet, firstGenerator⁻¹ • x ∈ orbitPointsSet := by
  rintro x ⟨i, hi⟩
  refine ⟨pointPermX.symm i, ?_⟩
  exact (firstGenerator_inv_smul_orbitPoints i).symm.trans
    (congrArg (fun z => firstGenerator⁻¹ • z) hi)

theorem orbitPointsSet_secondGenerator_inv :
    ∀ x ∈ orbitPointsSet, secondGenerator⁻¹ • x ∈ orbitPointsSet := by
  rintro x ⟨i, hi⟩
  refine ⟨pointPermY.symm i, ?_⟩
  exact (secondGenerator_inv_smul_orbitPoints i).symm.trans
    (congrArg (fun z => secondGenerator⁻¹ • z) hi)

theorem candidate_preserves_orbitPointsSet (g : candidate) :
    ∀ x ∈ orbitPointsSet, g • x ∈ orbitPointsSet := by
  have hg : g ∈ Subgroup.closure ({firstGenerator, secondGenerator} : Set candidate) := by
    rw [closure_pair]
    exact Subgroup.mem_top _
  induction hg using Subgroup.closure_induction_left with
  | one => intro x hx; simpa using hx
  | mul_left g hg d hd ih =>
    rcases Set.mem_insert_iff.mp hg with rfl | hg
    · intro x hx
      simpa only [mul_smul] using orbitPointsSet_firstGenerator _ (ih x hx)
    · rw [Set.mem_singleton_iff] at hg
      subst g
      intro x hx
      simpa only [mul_smul] using orbitPointsSet_secondGenerator _ (ih x hx)
  | inv_mul_cancel g hg d hd ih =>
    rcases Set.mem_insert_iff.mp hg with rfl | hg
    · intro x hx
      simpa only [mul_smul] using orbitPointsSet_firstGenerator_inv _ (ih x hx)
    · rw [Set.mem_singleton_iff] at hg
      subst g
      intro x hx
      simpa only [mul_smul] using orbitPointsSet_secondGenerator_inv _ (ih x hx)

theorem orbitPointsSet_candidate :
    ∀ g : candidate, g • (30 : Fin 2058) ∈ orbitPointsSet := by
  intro g
  rw [show (30 : Fin 2058) = orbitPoints 0 by rfl]
  exact candidate_preserves_orbitPointsSet g _ ⟨0, by simp [orbitPoints]⟩

theorem orbitPoints_mem_orbit (i : Fin 21) :
    orbitPoints i ∈ PointOrbit := by
  have step {g : candidate} {i j : Fin 21}
      (hi : orbitPoints i ∈ PointOrbit)
      (h : g • orbitPoints i = orbitPoints j) : orbitPoints j ∈ PointOrbit := by
    obtain ⟨u, hu⟩ := MulAction.mem_orbit_iff.mp hi
    apply MulAction.mem_orbit_iff.mpr
    refine ⟨g * u, ?_⟩
    calc
      (g * u) • (30 : Fin 2058) = g • (u • (30 : Fin 2058)) := by rw [mul_smul]
      _ = g • orbitPoints i := congrArg (fun z => g • z) hu
      _ = orbitPoints j := h
  have h0 : orbitPoints 0 ∈ PointOrbit := by
    apply MulAction.mem_orbit_iff.mpr
    exact ⟨1, by simp [orbitPoints]⟩
  have h18 := step (j := 18) h0 (by
    rw [firstGenerator_smul_orbitPoints]
    rfl)
  have h14 := step (j := 14) h18 (by
    rw [firstGenerator_smul_orbitPoints]
    rfl)
  have h3 := step (j := 3) h14 (by
    rw [firstGenerator_smul_orbitPoints]
    rfl)
  have h10 := step (j := 10) h3 (by
    rw [firstGenerator_smul_orbitPoints]
    rfl)
  have h16 := step (j := 16) h10 (by
    rw [secondGenerator_smul_orbitPoints]
    rfl)
  have h5 := step (j := 5) h16 (by
    rw [secondGenerator_smul_orbitPoints]
    rfl)
  have h19 := step (j := 19) h5 (by
    rw [secondGenerator_smul_orbitPoints]
    rfl)
  have h12 := step (j := 12) h19 (by
    rw [secondGenerator_smul_orbitPoints]
    rfl)
  have h8 := step (j := 8) h12 (by
    rw [secondGenerator_smul_orbitPoints]
    rfl)
  have h1 := step (j := 1) h12 (by
    rw [firstGenerator_smul_orbitPoints]
    rfl)
  have h17 := step (j := 17) h16 (by
    rw [firstGenerator_smul_orbitPoints]
    rfl)
  have h15 := step (j := 15) h1 (by
    rw [secondGenerator_smul_orbitPoints]
    rfl)
  have h7 := step (j := 7) h15 (by
    rw [secondGenerator_smul_orbitPoints]
    rfl)
  have h13 := step (j := 13) h7 (by
    rw [firstGenerator_smul_orbitPoints]
    rfl)
  have h4 := step (j := 4) h13 (by
    rw [secondGenerator_smul_orbitPoints]
    rfl)
  have h11 := step (j := 11) h14 (by
    rw [secondGenerator_smul_orbitPoints]
    rfl)
  have h20 := step (j := 20) h11 (by
    rw [secondGenerator_smul_orbitPoints]
    rfl)
  have h6 := step (j := 6) h20 (by
    rw [secondGenerator_smul_orbitPoints]
    rfl)
  have h2 := step (j := 2) h6 (by
    rw [secondGenerator_smul_orbitPoints]
    rfl)
  have h9 := step (j := 9) h5 (by rw [firstGenerator_smul_orbitPoints]; rfl)
  fin_cases i <;> assumption

theorem pairPoints_surjective : Function.Surjective pairPoints :=
  ((Nat.bijective_iff_injective_and_card pairPoints).mpr ⟨pairPoints_injective, by
    rw [Nat.card_fin, Set.powersetCard.card, Nat.card_fin]
    decide⟩).2

noncomputable def pointEquiv : Fin 21 ≃ PointOrbit :=
  Equiv.ofBijective (fun i => ⟨orbitPoints i, orbitPoints_mem_orbit i⟩) (by
    refine ⟨fun i j h => orbitPoints_injective (congrArg Subtype.val h), ?_⟩
    intro x
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp x.property
    obtain ⟨j, hj⟩ := orbitPointsSet_candidate g
    refine ⟨j, ?_⟩
    apply Subtype.ext
    exact hj.trans hg)

noncomputable def pairEquiv : Fin 21 ≃ Pair7 :=
  Equiv.ofBijective pairPoints ⟨pairPoints_injective, pairPoints_surjective⟩

noncomputable def orbitPairEquiv : PointOrbit ≃ Pair7 :=
  pointEquiv.symm.trans pairEquiv

end Held.OuterInvolution.FixedStructure
