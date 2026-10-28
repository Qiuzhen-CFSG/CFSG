module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.ActionConstruction.Degree21.SmallDegrees.ArithmeticData
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.ActionConstruction.Degree21.SmallDegrees.LocalBounds
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.SignedAnalysis
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.SuzukiPairings
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.OrderExhaustion.Constraints

/-!
# Numerical constraints for the complete irreducible family

Every row comes from an actual irreducible of the arbitrary ambient group.
The complete integral expansion supplies all rows, its Gram matrix and its
five degree-zero relations. The actual involution pairings give Suzuki's
identities. Restriction and faithfulness supply the local inequalities, and
the sum of squared degrees bounds even rows outside the exceptional supports.

Source: Janko, *A characterization of the Mathieu simple groups, I* (1968),
Sections 6--7. The remaining finite arithmetic must still be proved before
this system yields the minimum and uniqueness statements on p.16.
-/

open scoped BigOperators
noncomputable section
attribute [local instance] Fintype.ofFinite
namespace Theory.GroupTheory.HeldM22A10.M22Identification.ActionConstruction.Degree21.SmallDegrees
open LocalModelDichotomy CharacterOrder
variable {G : Type*} [Group G] [Finite G]
variable {D : LocalData G} {k : TwistedModel ≃* D.centralizer}
    {I : SpecialInductionData D k}

private theorem expansion_involutionValue (E : IntegralExpansion I) (j : E.Index) :
    E.character j D.z = (columnValue (fun i => E.coefficient i j) 0 : ℂ) := by
  simpa [specialRepresentative, CaseII.into_z_zero] using E.columns j 0

/-- The literal degree and coefficient arrays satisfy the complete arithmetic
system. This uses no existence or uniqueness assumption at degree 21. -/
public def degreeSystem [IsSimpleGroup G] (L : LocalAnalysisData D k)
    (hcard : Nat.card G = 443520) (E : IntegralExpansion I) : DegreeSystem E.Index := by
  have hI := hasSuzukiPairings_of_localAnalysis D k L I
  have hu := (SignedAnalysis.unit_multiplicities_and_janko_decomposition D k L I hI).1
  refine {
    principal := E.principalIndex
    degree := fun j => (E.irreducible j).degree
    coefficient := E.coefficient
    principal_degree := ?_
    principal_coefficient := E.principal_coefficient
    positive := fun j => (E.irreducible j).degree_pos
    divides := fun j => hcard ▸ (E.irreducible j).degree_dvd_card
    unit := ?_
    restriction := ?_
    fixed_nonnegative := ?_
    faithful := ?_
    sum_squares := ?_
    gram := E.gram
    degree_zero := ?_
    suzuki := ?_ }
  · have hh : (1 : ℂ) = ((E.irreducible E.principalIndex).degree : ℂ) :=
      (congrFun E.principal_character 1).symm.trans (E.irreducible _).degree_eq
    exact_mod_cast hh.symm
  · intro i j
    have hh := hu (E.character j) (E.irreducible j) i
    rw [E.multiplicity] at hh
    exact_mod_cast hh
  · intro j
    exact OrderExhaustion.degree_congruence_mod128 D k L I (E.irreducible j)
      (fun i => E.coefficient i j) (E.columns j)
  · intro j
    exact E_fixed_nonnegative D k L (E.irreducible j) _ (expansion_involutionValue E j)
  · intro j hj
    exact involution_lt_degree D (E.irreducible j)
      (fun he => hj (E.injective (he.trans E.principal_character.symm))) _
      (expansion_involutionValue E j)
  · let e : E.Index ≃ {χ : ClassFunction G // IsIrreducibleCharacter χ} :=
      Equiv.ofBijective (fun j => ⟨E.character j, E.irreducible j⟩) (by
        constructor
        · intro i j hij
          exact E.injective (congrArg Subtype.val hij)
        · rintro ⟨χ, hχ⟩
          obtain ⟨j, hj⟩ := E.complete χ hχ
          exact ⟨j, Subtype.ext hj⟩)
    let : Fintype {χ : ClassFunction G // IsIrreducibleCharacter χ} :=
      Fintype.ofEquiv E.Index e
    calc
      ∑ j, (E.irreducible j).degree ^ 2 =
          ∑ χ : {χ : ClassFunction G // IsIrreducibleCharacter χ}, χ.property.degree ^ 2 :=
        e.sum_comp (fun χ => χ.property.degree ^ 2)
      _ = Nat.card G := Theory.Character.sum_irreducibleCharacters_degree_sq
      _ = 443520 := hcard
  · intro i
    have hh := congrFun (E.expansion i) 1
    rw [show I.induced i 1 = 0 from I.degree_zero i] at hh
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      (E.irreducible _).degree_eq] at hh
    exact_mod_cast hh.symm
  · intro i
    have hh := suzukiOrder_identity D k L I hI E.character E.irreducible
      (fun j => (E.coefficient i j : ℂ)) i (E.expansion i)
    simp_rw [expansion_involutionValue E, (E.irreducible _).degree_eq] at hh
    rw [hcard] at hh
    apply Rat.cast_injective (α := ℂ)
    push_cast
    exact hh

/-- The constructed degree system retains the actual irreducible degree. -/
@[simp] public theorem degreeSystem_degree [IsSimpleGroup G] (L : LocalAnalysisData D k)
    (hcard : Nat.card G = 443520) (E : IntegralExpansion I) (j : E.Index) :
    (degreeSystem L hcard E).degree j = (E.irreducible j).degree := by unfold degreeSystem; rfl

/-- Its coordinates are exactly the actual exceptional scalar products. -/
@[simp] public theorem degreeSystem_coefficient [IsSimpleGroup G] (L : LocalAnalysisData D k)
    (hcard : Nat.card G = 443520) (E : IntegralExpansion I) (i : Fin 5) (j : E.Index) :
    (degreeSystem L hcard E).coefficient i j = E.coefficient i j := by unfold degreeSystem; rfl

/-- The distinguished row is the principal character in the complete expansion. -/
@[simp] public theorem degreeSystem_principal [IsSimpleGroup G] (L : LocalAnalysisData D k)
    (hcard : Nat.card G = 443520) (E : IntegralExpansion I) :
    (degreeSystem L hcard E).principal = E.principalIndex := by unfold degreeSystem; rfl

end Theory.GroupTheory.HeldM22A10.M22Identification.ActionConstruction.Degree21.SmallDegrees
