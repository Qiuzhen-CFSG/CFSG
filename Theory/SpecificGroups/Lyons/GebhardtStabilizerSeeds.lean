module

public import Theory.SpecificGroups.Lyons.GebhardtDoubleCosetTransversalSetup
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Tactic.FinCases

/-!
# Literal conjugation seeds for the Gebhardt stabilizers

The seven conjugation relations and the commutator relation in the outer
relator list give two certified elements in each nonidentity local stabilizer.
Products and inverses of these elements remain in the indicated stabilizer.
The last outer word relation is not needed for these inclusions.

Every equality below is interpreted in the abstract 25-relator presentation.
Source: Gebhardt, Experimental Mathematics 9 (2000), 333–338, Section 3B.
-/

namespace Lyons.Gebhardt
public section

/-- A written word using only the local generators and visual separators. -/
@[expose] def IsLocalWord (s : String) : Prop :=
  ∀ c ∈ s.toList, c ∈ ['a', 'A', 'b', 'B', 'c', 'C', 'd', 'D', ' ']

theorem localWord_mem (s : String) (hs : IsLocalWord s) :
    PresentedGroup.mk relators (word s) ∈ localSubgroup := by
  unfold word
  rw [map_list_prod]
  apply localSubgroup.list_prod_mem
  intro x hx
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hx
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hw
  have hl := hs c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp only [letter, map_inv]
  · exact local_generator_mem 0 (by decide)
  · exact localSubgroup.inv_mem (local_generator_mem 0 (by decide))
  · exact local_generator_mem 1 (by decide)
  · exact localSubgroup.inv_mem (local_generator_mem 1 (by decide))
  · exact local_generator_mem 2 (by decide)
  · exact localSubgroup.inv_mem (local_generator_mem 2 (by decide))
  · exact local_generator_mem 3 (by decide)
  · exact localSubgroup.inv_mem (local_generator_mem 3 (by decide))
  · exact localSubgroup.one_mem

theorem local_conjugation_transition (x w y : String)
    (hr : equationRelator (conjugate (word x) (word w)) (word y) ∈ relators) :
    (PresentedGroup.mk relators (word w))⁻¹ * PresentedGroup.mk relators (word x) =
      PresentedGroup.mk relators (word y) * (PresentedGroup.mk relators (word w))⁻¹ := by
  have he := PresentedGroup.mk_eq_mk_of_mul_inv_mem hr
  have ht := congrArg (fun g : Presentation => g *
    (PresentedGroup.mk relators (word w))⁻¹) he
  simpa [conjugate, mul_assoc] using ht


/-- Triples `(x,w,y)` from the seven literal relations `w⁻¹*x*w = y`. -/
@[expose] def outerStabilizerWords (j : Fin 7) : String × String × String :=
  match j.val with
  | 0 => ("a", "z", "AAA")
  | 1 => ("a", "zdz", "aaa")
  | 2 => ("CDcbabb cbcbCd", "zdz", "Cbcc aCbdca CbCBB cA cDcbb cdaDCDcbAb")
  | 3 => ("a", "zdBz", "ADC bCC aB cAbb cB cACdBA")
  | 4 => ("CADCbaBaC bcaCDcdacBabac", "zdBz", "AcAAA CBBCdCa Cbb cBcACdBCDCbabdcA")
  | 5 => ("AbdcABabaCBca", "zdcdz", "CaaabCB A cDCbAB")
  | _ => ("DcbAB", "zdcdz", "acAbaCbcaCBABabDcaCBCa")

/-- Which of the four representative words occurs in a conjugation seed. -/
@[expose] def outerStabilizerCoset (j : Fin 7) : Fin 5 :=
  if j.val = 0 then 1 else if j.val < 3 then 2 else if j.val < 5 then 3 else 4

theorem outerStabilizerWords_relator (j : Fin 7) :
    equationRelator (conjugate (word (outerStabilizerWords j).1)
      (word (outerStabilizerWords j).2.1)) (word (outerStabilizerWords j).2.2) ∈
      relators := by
  fin_cases j <;> simp [outerStabilizerWords, relators, outerRelators]

theorem outerStabilizerWords_input_local (j : Fin 7) :
    IsLocalWord (outerStabilizerWords j).1 := by
  fin_cases j <;> unfold IsLocalWord <;> decide

theorem outerStabilizerWords_output_local (j : Fin 7) :
    IsLocalWord (outerStabilizerWords j).2.2 := by
  fin_cases j <;> unfold IsLocalWord <;> decide

/-- Each of the literal conjugation relations supplies a right-coset transition. -/
theorem outerStabilizerWords_transition (j : Fin 7) :
    doubleCosetRepresentative (outerStabilizerCoset j) *
        PresentedGroup.mk relators (word (outerStabilizerWords j).1) =
      PresentedGroup.mk relators (word (outerStabilizerWords j).2.2) *
        doubleCosetRepresentative (outerStabilizerCoset j) := by
  have hw : doubleCosetRepresentative (outerStabilizerCoset j) =
      (PresentedGroup.mk relators (word (outerStabilizerWords j).2.1))⁻¹ := by
    fin_cases j <;> rfl
  rw [hw]
  exact local_conjugation_transition _ _ _ (outerStabilizerWords_relator j)

/-- The input word of a conjugation relation, regarded as a local element. -/
@[expose] def outerStabilizerSeed (j : Fin 7) : localSubgroup :=
  ⟨PresentedGroup.mk relators (word (outerStabilizerWords j).1),
    localWord_mem _ (outerStabilizerWords_input_local j)⟩

theorem outerStabilizerSeed_mem (j : Fin 7) :
    outerStabilizerSeed j ∈ localDoubleCosetStabilizer (outerStabilizerCoset j) := by
  rw [mem_localDoubleCosetStabilizer]
  change (doubleCosetRepresentative (outerStabilizerCoset j) *
      PresentedGroup.mk relators (word (outerStabilizerWords j).1)) * _ ∈ _
  rw [outerStabilizerWords_transition]
  simpa only [mul_inv_cancel_right] using
    localWord_mem _ (outerStabilizerWords_output_local j)

/-- Any word in the certified seeds stays in the corresponding stabilizer. -/
theorem outerStabilizerSeed_closure_le (i : Fin 5) :
    Subgroup.closure {h | ∃ j, outerStabilizerCoset j = i ∧ h = outerStabilizerSeed j} ≤
      localDoubleCosetStabilizer i := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨j, rfl, rfl⟩
  exact outerStabilizerSeed_mem j

/-- The second local element in the first stabilizer, from the commutator
relation `[z,t] = bcBC`. -/
@[expose] def outerCommutatorSeed : localSubgroup :=
  ⟨PresentedGroup.mk relators (word "DCbaBDcdCdCBaB cDcd"),
    localWord_mem _ (by unfold IsLocalWord; decide)⟩

theorem outerCommutatorSeed_transition :
    doubleCosetRepresentative 1 * outerCommutatorSeed.val =
      (outerCommutatorSeed.val * (PresentedGroup.mk relators (word "bcBC"))⁻¹) *
        doubleCosetRepresentative 1 := by
  let z := PresentedGroup.mk relators (word "z")
  let t := outerCommutatorSeed.val
  let u := PresentedGroup.mk relators (word "bcBC")
  have hr : equationRelator
      (commutatorWord (word "z") (word "DCbaBDcdCdCBaB cDcd")) (word "bcBC") ∈
        relators := by
    simp only [relators, Set.mem_ofPred_eq, List.mem_append]
    exact Or.inr (by simp [outerRelators])
  have he : z⁻¹ * t⁻¹ * z * t = u := by
    simpa only [commutatorWord, map_mul, map_inv, z, t, u, outerCommutatorSeed] using
      PresentedGroup.mk_eq_mk_of_mul_inv_mem hr
  have ht : z⁻¹ * t⁻¹ * z = u * t⁻¹ := by
    simpa only [mul_inv_cancel_right] using congrArg (fun g => g * t⁻¹) he
  have hi : z⁻¹ * t * z = t * u⁻¹ := by
    simpa only [mul_inv_rev, inv_inv, mul_assoc] using congrArg Inv.inv ht
  have hf : z⁻¹ * t = (t * u⁻¹) * z⁻¹ := by
    simpa only [mul_inv_cancel_right] using congrArg (fun g => g * z⁻¹) hi
  exact hf

theorem outerCommutatorSeed_mem :
    outerCommutatorSeed ∈ localDoubleCosetStabilizer 1 := by
  rw [mem_localDoubleCosetStabilizer, outerCommutatorSeed_transition,
    mul_inv_cancel_right]
  exact localSubgroup.mul_mem outerCommutatorSeed.property
    (localSubgroup.inv_mem (localWord_mem _ (by unfold IsLocalWord; decide)))

/-- The two explicitly certified generators for the first stabilizer. -/
theorem outerFirstStabilizer_closure_le :
    Subgroup.closure {outerStabilizerSeed 0, outerCommutatorSeed} ≤
      localDoubleCosetStabilizer 1 := by
  apply (Subgroup.closure_le _).mpr
  intro h hh
  rcases hh with rfl | rfl
  · exact outerStabilizerSeed_mem 0
  · exact outerCommutatorSeed_mem

/-- The two-generator subgroup certified inside each nonidentity stabilizer. -/
@[expose] def certifiedLocalStabilizer (i : Fin 4) : Subgroup localSubgroup :=
  match i.val with
  | 0 => Subgroup.closure {outerStabilizerSeed 0, outerCommutatorSeed}
  | 1 => Subgroup.closure {outerStabilizerSeed 1, outerStabilizerSeed 2}
  | 2 => Subgroup.closure {outerStabilizerSeed 3, outerStabilizerSeed 4}
  | _ => Subgroup.closure {outerStabilizerSeed 5, outerStabilizerSeed 6}

theorem certifiedLocalStabilizer_le (i : Fin 4) :
    certifiedLocalStabilizer i ≤ localDoubleCosetStabilizer i.succ := by
  fin_cases i
  · exact outerFirstStabilizer_closure_le
  · apply (Subgroup.closure_le _).mpr
    intro h hh
    rcases hh with rfl | rfl
    · exact outerStabilizerSeed_mem 1
    · exact outerStabilizerSeed_mem 2
  · apply (Subgroup.closure_le _).mpr
    intro h hh
    rcases hh with rfl | rfl
    · exact outerStabilizerSeed_mem 3
    · exact outerStabilizerSeed_mem 4
  · apply (Subgroup.closure_le _).mpr
    intro h hh
    rcases hh with rfl | rfl
    · exact outerStabilizerSeed_mem 5
    · exact outerStabilizerSeed_mem 6

/-- It suffices to bound the indices of the explicit two-generator subgroups;
they need not be proved equal to the full stabilizers. -/
def localSubdegreeBoundsOfCertifiedIndices [Finite localSubgroup]
    (assignment : Equiv.Perm (Fin 4))
    (hindex : ∀ i, (certifiedLocalStabilizer i).index ≤
      proposedSubdegree (assignment i)) : LocalSubdegreeBounds where
  assignment := assignment
  index_le i := (Subgroup.index_antitone (certifiedLocalStabilizer_le i)).trans (hindex i)

end
end Lyons.Gebhardt
