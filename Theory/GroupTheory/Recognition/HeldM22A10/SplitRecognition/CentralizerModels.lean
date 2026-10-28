module

public import Theory.Mathieu.M22.Basic

/-!
# Concrete centralizers for the two Held recognition branches

The alternating model uses the permutation (01)(23)(45)(67) in A10.
The Mathieu model uses the first Atlas generator inside the genuine even
Steiner-design automorphism group. Both selected elements have order two.
The two groups below are their actual intrinsic centralizers, not extension
shape records or alternative model tags.

The separation into these two local models is the remark on p.224 of
D. Held, "A Characterization of some multiply transitive permutation groups,
I", Illinois J. Math. 13 (1969), 224--240, DOI 10.1215/ijm/1256053756.
That paper proves the A10 recognition branch (Theorem B); it cites
Z. Janko, "A characterization of the Mathieu simple groups, I",
J. Algebra 9 (1968), 1--19, for the M22 branch and the local dichotomy.

This module only fixes the concrete carriers shared by those three proof
obligations. It does not assert their identification or recognition.
-/

namespace Theory.GroupTheory.HeldM22A10.CentralizerModels

/-- Four disjoint transpositions fixing the last two letters. -/
@[expose] public def a10Permutation : Equiv.Perm (Fin 10) :=
  Equiv.swap 0 1 * Equiv.swap 2 3 * Equiv.swap 4 5 * Equiv.swap 6 7

/-- The selected permutation lies in the alternating group. -/
public theorem a10Permutation_even : a10Permutation ∈ alternatingGroup (Fin 10) := by
  rw [Equiv.Perm.mem_alternatingGroup]
  simp [a10Permutation, Equiv.Perm.sign_swap']

/-- The selected involution in the concrete alternating group. -/
@[expose] public def a10Involution : alternatingGroup (Fin 10) :=
  ⟨a10Permutation, a10Permutation_even⟩

/-- The selected alternating element has order two. -/
public theorem a10Involution_order : orderOf a10Involution = 2 := by
  rw [← Subgroup.orderOf_coe a10Involution]
  change orderOf a10Permutation = 2
  apply orderOf_eq_prime
  · decide +kernel
  · decide +kernel

/-- The actual centralizer in A10 of the selected involution. -/
public abbrev a10Centralizer : Subgroup (alternatingGroup (Fin 10)) :=
  Subgroup.centralizer {a10Involution}

/-- The selected involution in the genuine Steiner-design Mathieu group. -/
@[expose] public def m22Involution : Sporadic.Mathieu.M22 :=
  ⟨Sporadic.Mathieu.m22GeneratorA, Sporadic.Mathieu.m22GeneratorA_mem_M22⟩

/-- The selected Mathieu element has order two. -/
public theorem m22Involution_order : orderOf m22Involution = 2 := by
  rw [← Subgroup.orderOf_coe m22Involution]
  exact Sporadic.Mathieu.m22GeneratorA_order

/-- The actual centralizer in the Steiner Mathieu group of the selected involution. -/
public noncomputable abbrev m22Centralizer : Subgroup Sporadic.Mathieu.M22 :=
  Subgroup.centralizer {m22Involution}

end Theory.GroupTheory.HeldM22A10.CentralizerModels
