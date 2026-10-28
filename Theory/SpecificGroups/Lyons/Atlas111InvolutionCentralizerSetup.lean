module

public import Theory.SpecificGroups.Lyons.Atlas111SimplicitySetup

/-!
# The ATLAS double-cover subgroup words in the Lyons matrix group

The program `LyG1-max4W1` defines an actual two-generated subgroup of the fixed
matrix carrier. Its first output is `ab`. The proposed central involution is
`(ab)⁷`, not the first standard generator `a`. A separate explicit word is a
candidate transporter from this involution to `a`.

Only the word definitions and their elementary consequences are asserted here.
Commutation, transport, the local center bound and maximality require separate
certificates. In particular the ATLAS label `2.A11` is not an identification
theorem.

Source: R. A. Wilson et al., ATLAS of Finite Group Representations,
https://brauer.maths.qmul.ac.uk/Atlas/v3/subgroup/LyG1-max4W1 .
The original straight-line program is preserved in `Atlas111InvolutionSource/`.
-/

namespace Lyons.SimplicityCertificate

/-- The sixteen instructions of the ATLAS program, retaining register order. -/
@[expose] public def max4Program {G : Type*} [Group G] (a b : G) : G × G :=
  let r3 := a * b
  let r4 := r3 * b
  let r5 := r3 * r4
  let r6 := r3 * r5
  let r8 := r6 * r5
  let r9 := r3 * r8
  let r10 := r9 * r4
  let r4 := r3 ^ 7
  let r5 := r4 * r10
  let r6 := r10 * r4
  let r7 := r6⁻¹
  let r6 := r7 * r5
  let r7 := r6 ^ 10
  let r2 := r10 * r7
  let r4 := a * a
  let r1 := r4 * r3
  (r1, r2)

public theorem max4Program_fst {G : Type*} [Group G] (a b : G) :
    (max4Program a b).1 = a ^ 2 * (a * b) := by
  simp only [max4Program, pow_two]

/-- The first subgroup word. -/
@[expose] public def involutionLocalA : LyonsGroup :=
  (max4Program generatorA generatorB).1

/-- The second subgroup word. -/
@[expose] public def involutionLocalB : LyonsGroup :=
  (max4Program generatorA generatorB).2

/-- The concrete subgroup specified by `LyG1-max4W1`. -/
@[expose] public def involutionLocalSubgroup : Subgroup LyonsGroup :=
  Subgroup.closure {involutionLocalA, involutionLocalB}

/-- The proposed central involution of the ATLAS subgroup. -/
@[expose] public def involutionLocalT : LyonsGroup :=
  (generatorA * generatorB) ^ 7

/-- A short word used to construct the candidate transporter. -/
@[expose] public def involutionTransportSeed : LyonsGroup :=
  generatorA * generatorB ^ 2 * generatorA * generatorB

/-- Candidate `w` for the identity `w⁻¹ * involutionLocalT * w = generatorA`.
The identity itself is a separate matrix certificate. -/
@[expose] public def involutionTransporter : LyonsGroup :=
  involutionTransportSeed *
    (generatorA * (involutionTransportSeed⁻¹ * involutionLocalT *
      involutionTransportSeed)) ^ 18

public theorem involutionLocalA_eq : involutionLocalA = generatorA * generatorB := by
  rw [involutionLocalA, max4Program_fst, generatorA_sq, one_mul]

public theorem involutionLocalA_mem : involutionLocalA ∈ involutionLocalSubgroup :=
  Subgroup.subset_closure (Set.mem_insert _ _)

public theorem involutionLocalB_mem : involutionLocalB ∈ involutionLocalSubgroup :=
  Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))

public theorem involutionLocalT_mem : involutionLocalT ∈ involutionLocalSubgroup := by
  change (generatorA * generatorB) ^ 7 ∈ involutionLocalSubgroup
  rw [← involutionLocalA_eq]
  exact involutionLocalSubgroup.pow_mem involutionLocalA_mem 7

public theorem involutionLocalA_commutes :
    involutionLocalA * involutionLocalT = involutionLocalT * involutionLocalA := by
  rw [involutionLocalA_eq]
  exact (Commute.refl (generatorA * generatorB)).pow_right 7

/-- Only the second generator requires a matrix commutation certificate. -/
public theorem involutionLocalSubgroup_le_centralizer
    (hcomm : involutionLocalB * involutionLocalT = involutionLocalT * involutionLocalB) :
    involutionLocalSubgroup ≤ Subgroup.centralizer {involutionLocalT} := by
  apply (Subgroup.closure_le (K := Subgroup.centralizer {involutionLocalT})).mpr
  intro x hx
  rcases hx with rfl | hx
  · exact Subgroup.mem_centralizer_singleton_iff.mpr involutionLocalA_commutes
  · rcases hx with rfl
    exact Subgroup.mem_centralizer_singleton_iff.mpr hcomm

end Lyons.SimplicityCertificate
