module

public import Theory.Mathieu.M12.Properties.InvolutionClasses
public import Theory.GroupTheory.SpecificGroups.KleinFourGenerators

/-!
# Marked permutations for the M₁₂ parabolic pair

All marked permutations belong to the actual Witt-design automorphism group:
short words in its two standard generators certify membership. The marked
involutions generate the natural four. Its normalizer and the centralizer
of the distinguished involution are the two candidate parabolics.

The involutions and local choices agree with the concrete calculations in
`Stellmacher.SectionNine.NineFiveM12Data` and `NineFiveM12LocalActions`.
Source: Aschbacher–Smith, Hypothesis 14.2.1 and Lemma 14.2.21, pp.981, 988.
-/

@[expose] public section
namespace Sporadic.Mathieu.M12SmallPair
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

private def wordPerm : List Bool → Equiv.Perm (Fin 12)
  | [] => 1
  | b :: bs => (if b then m12GeneratorB else m12GeneratorA) * wordPerm bs

private theorem wordPerm_mem (bs : List Bool) : wordPerm bs ∈ M12 := by
  induction bs with
  | nil => exact M12.one_mem
  | cons b bs ih =>
    exact M12.mul_mem (by cases b <;> first | exact m12GeneratorA_mem | exact m12GeneratorB_mem) ih

def zPerm : Equiv.Perm (Fin 12) :=
  List.formPerm [1, 5] * List.formPerm [3, 4] * List.formPerm [6, 8] * List.formPerm [10, 11]

theorem zPerm_mem : zPerm ∈ M12 := by
  have h : zPerm = wordPerm [false, true, false, true, false, true, false, true, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, true, false, true, true, false, true, false, true, true] := by decide +kernel
  rw [h]
  exact wordPerm_mem _

noncomputable def z : M12 := ⟨zPerm, zPerm_mem⟩

def vPerm : Equiv.Perm (Fin 12) :=
  List.formPerm [0, 2] * List.formPerm [1, 5] * List.formPerm [6, 8] * List.formPerm [7, 9]

theorem vPerm_mem : vPerm ∈ M12 := by
  have h : vPerm = wordPerm [true, true, false, true, false, true, false, true, true, false, true, true, false, true] := by decide +kernel
  rw [h]
  exact wordPerm_mem _

noncomputable def v : M12 := ⟨vPerm, vPerm_mem⟩

def leftIPerm : Equiv.Perm (Fin 12) :=
  List.formPerm [0, 7] * List.formPerm [1, 3, 5, 4] * List.formPerm [2, 9] * List.formPerm [6, 11, 8, 10]

theorem leftIPerm_mem : leftIPerm ∈ M12 := by
  have h : leftIPerm = wordPerm [false, true, false, true, true, false, true, false, true, false, true, false, true, true, false, true, true, false, true, false, true, false, true, true, false, true] := by decide +kernel
  rw [h]
  exact wordPerm_mem _

noncomputable def leftI : M12 := ⟨leftIPerm, leftIPerm_mem⟩

def leftJPerm : Equiv.Perm (Fin 12) :=
  List.formPerm [0, 2] * List.formPerm [1, 6, 5, 8] * List.formPerm [3, 10, 4, 11] * List.formPerm [7, 9]

theorem leftJPerm_mem : leftJPerm ∈ M12 := by
  have h : leftJPerm = wordPerm [true, false, true, true, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, false, true, true, false, true, false, true, false, true, true, false, true, true, false, true, false] := by decide +kernel
  rw [h]
  exact wordPerm_mem _

noncomputable def leftJ : M12 := ⟨leftJPerm, leftJPerm_mem⟩

def rightIPerm : Equiv.Perm (Fin 12) :=
  List.formPerm [1, 4, 5, 3] * List.formPerm [6, 11, 8, 10]

theorem rightIPerm_mem : rightIPerm ∈ M12 := by
  have h : rightIPerm = wordPerm [true, true, false, true, true, false, true, false, true, false, true, true, false, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, true] := by decide +kernel
  rw [h]
  exact wordPerm_mem _

noncomputable def rightI : M12 := ⟨rightIPerm, rightIPerm_mem⟩

def rightJPerm : Equiv.Perm (Fin 12) :=
  List.formPerm [1, 8, 5, 6] * List.formPerm [3, 10, 4, 11]

theorem rightJPerm_mem : rightJPerm ∈ M12 := by
  have h : rightJPerm = wordPerm [true, false, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, true, true, false, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, false] := by decide +kernel
  rw [h]
  exact wordPerm_mem _

noncomputable def rightJ : M12 := ⟨rightJPerm, rightJPerm_mem⟩

def thirdPerm : Equiv.Perm (Fin 12) :=
  List.formPerm [0, 9] * List.formPerm [1, 8] * List.formPerm [2, 7] * List.formPerm [3, 11] * List.formPerm [4, 10] * List.formPerm [5, 6]

theorem thirdPerm_mem : thirdPerm ∈ M12 := by
  have h : thirdPerm = wordPerm [false, true, true, false, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, false, true, true] := by decide +kernel
  rw [h]
  exact wordPerm_mem _

noncomputable def third : M12 := ⟨thirdPerm, thirdPerm_mem⟩

def movingActorPerm : Equiv.Perm (Fin 12) :=
  List.formPerm [0, 4, 1] * List.formPerm [2, 3, 5] * List.formPerm [6, 9, 11] * List.formPerm [7, 10, 8]

theorem movingActorPerm_mem : movingActorPerm ∈ M12 := by
  have h : movingActorPerm = wordPerm [false, true, true, false, true, true, false, true, false, true, true, false, true, true, false, true, false, true, false, true, false, true] := by decide +kernel
  rw [h]
  exact wordPerm_mem _

noncomputable def movingActor : M12 := ⟨movingActorPerm, movingActorPerm_mem⟩

def cubicActorPerm : Equiv.Perm (Fin 12) :=
  List.formPerm [2, 9, 7] * List.formPerm [3, 8, 10] * List.formPerm [4, 6, 11]

theorem cubicActorPerm_mem : cubicActorPerm ∈ M12 := by
  have h : cubicActorPerm = wordPerm [false, true, false, true, false, true, false, true, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true] := by decide +kernel
  rw [h]
  exact wordPerm_mem _

noncomputable def cubicActor : M12 := ⟨cubicActorPerm, cubicActorPerm_mem⟩

noncomputable def distinguished : Subgroup M12 := Subgroup.zpowers z
noncomputable def natural : Subgroup M12 := Subgroup.closure ({z, v} : Set M12)
noncomputable def elementary : Subgroup M12 := Subgroup.closure ({z, v, third} : Set M12)
noncomputable def firstParabolic : Subgroup M12 := Subgroup.centralizer ({z} : Set M12)
noncomputable def secondParabolic : Subgroup M12 := Subgroup.normalizer (natural : Set M12)
noncomputable def sylowCandidate : Subgroup M12 := firstParabolic ⊓ secondParabolic

theorem parabolic_intersection : firstParabolic ⊓ secondParabolic = sylowCandidate := rfl

theorem z_order : orderOf z = 2 := by
  apply orderOf_eq_prime <;> decide +kernel

theorem v_order : orderOf v = 2 := by
  apply orderOf_eq_prime <;> decide +kernel

theorem z_v_commute : Commute z v := by
  change z * v = v * z
  decide +kernel

theorem natural_kleinFour : IsKleinFour natural := by
  apply Subgroup.isKleinFour_closure_pair_of_orderOf z v z_order v_order
  · decide +kernel
  · exact z_v_commute

theorem card_natural : Nat.card natural = 4 := natural_kleinFour.card_four

theorem mem_natural (g : M12) :
    g ∈ natural ↔ g = 1 ∨ g = z ∨ g = v ∨ g = z * v := by
  exact Subgroup.mem_closure_pair_iff z v (by decide +kernel)
    (by decide +kernel) z_v_commute g

theorem card_distinguished : Nat.card distinguished = 2 := by
  rw [distinguished, Nat.card_zpowers, z_order]

theorem z_mem_natural : z ∈ natural := Subgroup.subset_closure (by simp)
theorem v_mem_natural : v ∈ natural := Subgroup.subset_closure (by simp)

theorem distinguished_le_natural : distinguished ≤ natural :=
  Subgroup.zpowers_le.mpr z_mem_natural

theorem natural_le_elementary : natural ≤ elementary := by
  apply Subgroup.closure_mono
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
  tauto

theorem movingActor_order : orderOf movingActor = 3 := by
  apply orderOf_eq_prime <;> decide +kernel

theorem movingActor_conjugates_z : movingActor * z * movingActor⁻¹ = v := by
  decide +kernel

theorem movingActor_moves : movingActor * z * movingActor⁻¹ ≠ z := by
  decide +kernel

theorem cubicActor_order : orderOf cubicActor = 3 := by
  apply orderOf_eq_prime <;> decide +kernel

theorem cubicActor_mem : cubicActor ∈ firstParabolic := by
  rw [firstParabolic, Subgroup.mem_centralizer_singleton_iff]
  decide +kernel

end Sporadic.Mathieu.M12SmallPair
