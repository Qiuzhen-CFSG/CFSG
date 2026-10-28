module

public import Theory.SpecificGroups.ClassicalUnitary.A02ParabolicSections.SwappedTori.Coordinates

/-!
# Tail interchanges inside the actual unitary local subgroups

The three tail-coordinate interchanges fix the root plane in dimension at
least six, and fix the isotropic line in dimension five. Their projective
images therefore belong to the literal root normalizer and line parabolic.
Conjugation permutes the three marked torus parameters.

Source: the unitary local construction in Aschbacher--Smith A.2.18, p.40.
-/

@[expose] public noncomputable section
open BenderSuzuki.MatrixGroups Matrix
namespace Theory.SpecificGroups.ClassicalUnitary.A02ParabolicSections.SwappedTori
variable {F : Type*} [Field F] [CharP F 2]

namespace Six
open Theory.SpecificGroups.UnitaryRootNormalizer
variable (k : ℕ) (J : HermitianForm (6+k) F) (hJ : J.form = 1)

/-- The determinant-one interchange of two tail coordinates. -/
def swap (i j : Fin 3) (hij : i ≠ j) : J.specialSubgroup :=
  swapSpecial J hJ (tailSix k i) (tailSix k j) (fun h => hij (tailSix_injective k h))

theorem swap_commutes_root (i j : Fin 3) (hij : i ≠ j) :
    Commute (swap k J hJ i j hij).val (rootMatrix (F := F) k) := by
  have hd : Equiv.Perm.Disjoint (Equiv.swap (tailSix k i) (tailSix k j))
      (Equiv.swap (rootFirst k) (rootSecond k)) := by
    intro x
    by_cases h0 : x = rootFirst k
    · subst x
      exact Or.inl (six_swap_fixed k i j _ (Or.inl (by simp [rootFirst])))
    by_cases h1 : x = rootSecond k
    · subst x
      exact Or.inl (six_swap_fixed k i j _ (Or.inl (by simp [rootSecond])))
    exact Or.inr (Equiv.swap_apply_of_ne_of_ne h0 h1)
  apply Units.ext
  change (Equiv.swap (tailSix k i) (tailSix k j)).permMatrix F *
    (Equiv.swap (rootFirst k) (rootSecond k)).permMatrix F =
    (Equiv.swap (rootFirst k) (rootSecond k)).permMatrix F *
      (Equiv.swap (tailSix k i) (tailSix k j)).permMatrix F
  rw [← permMatrix_mul, ← permMatrix_mul, hd.commute.eq]

/-- The same interchange as an element of the actual projective local subgroup. -/
def localSwap (i j : Fin 3) (hij : i ≠ j) :
    Subgroup.normalizer (rootSubgroup k J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J)) :=
  ⟨project k J (swap k J hJ i j hij), by
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    have hc : Commute (project k J (swap k J hJ i j hij)) (root k J hJ) := by
      apply Subtype.ext
      exact congrArg ProjGenLinGroup.mk (swap_commutes_root k J hJ i j hij)
    rintro g ⟨m, rfl⟩
    exact (hc.zpow_right m).eq.symm⟩

variable (C : Subgroup Fˣ) (hC : ∀ u : C, J.conj (u.val : F) * (u.val : F) = 1)

/-- The actual local element interchanges the corresponding torus parameters. -/
theorem conjugate_torus (i j : Fin 3) (hij : i ≠ j) (a : Fin 3 → C) :
    localSwap k J hJ i j hij * torusNormalizer k J hJ C hC a *
        (localSwap k J hJ i j hij)⁻¹ =
      torusNormalizer k J hJ C hC (a ∘ Equiv.swap i j) := by
  apply Subtype.ext
  change project k J (swap k J hJ i j hij) *
    project k J (torusSpecial k J hJ C hC a) *
      (project k J (swap k J hJ i j hij))⁻¹ = _
  rw [← map_inv, ← map_mul, ← map_mul]
  apply congrArg (project k J)
  apply swap_diagonal J hJ _ _ _ _ _ _ _ rfl rfl
  intro x
  exact congrArg (fun u : C => (u.val : F)) (six_entries k C a i j x)
end Six

namespace Five
open Theory.SpecificGroups.UnitaryFive
variable (J : HermitianForm 5 F) (hJ : J.form = 1)

/-- The determinant-one interchange of two tail coordinates. -/
def swap (i j : Fin 3) (hij : i ≠ j) : J.specialSubgroup :=
  swapSpecial J hJ (Fin.natAdd 2 i) (Fin.natAdd 2 j)
    (fun h => hij (Fin.natAdd_injective 3 2 h))

theorem swap_stabilizes (i j : Fin 3) (hij : i ≠ j) :
    swap J hJ i j hij ∈ Theory.SpecificGroups.UnitaryFive.specialStabilizer J (Theory.SpecificGroups.UnitaryFive.line F) := by
  rw [Theory.SpecificGroups.UnitaryFive.mem_specialStabilizer_iff]
  intro v
  change ((Equiv.swap (Fin.natAdd 2 i) (Fin.natAdd 2 j)).permMatrix F *ᵥ v ∈
    Theory.SpecificGroups.UnitaryFive.line F) ↔ _
  rw [permMatrix_mulVec]
  fin_cases i <;> fin_cases j <;>
    simp [Theory.SpecificGroups.UnitaryFive.line, Equiv.swap_apply_def, and_comm, and_left_comm, and_assoc]

/-- The same interchange as an element of the actual projective local subgroup. -/
def localSwap (i j : Fin 3) (hij : i ≠ j) : lineParabolic J :=
  ⟨project J (swap J hJ i j hij), _, swap_stabilizes J hJ i j hij, rfl⟩

variable (C : Subgroup Fˣ) (hC : ∀ u : C, J.conj (u.val : F) * (u.val : F) = 1)

/-- The actual local element interchanges the corresponding torus parameters. -/
theorem conjugate_torus (i j : Fin 3) (hij : i ≠ j) (a : Fin 3 → C) :
    localSwap J hJ i j hij * torusParabolic J hJ C hC (fiveParameters C a) *
        (localSwap J hJ i j hij)⁻¹ =
      torusParabolic J hJ C hC (fiveParameters C (a ∘ Equiv.swap i j)) := by
  apply Subtype.ext
  change project J (swap J hJ i j hij) *
    project J (torusSpecial J hJ C hC (fiveParameters C a)) *
      (project J (swap J hJ i j hij))⁻¹ = _
  rw [← map_inv, ← map_mul, ← map_mul]
  apply congrArg (project J)
  apply swap_diagonal J hJ _ _ _ _ _ _ _ rfl rfl
  intro x
  exact congrArg (fun u : C => (u.val : F)) (five_entries C a i j x)
end Five

end Theory.SpecificGroups.ClassicalUnitary.A02ParabolicSections.SwappedTori
