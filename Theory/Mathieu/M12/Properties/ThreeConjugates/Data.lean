module
public import Theory.Mathieu.M12.ExceptionalParabolics.Extension.Seeds

/-!
# Word certificates for three-conjugate generation in the M₁₂ extension

The three representatives and both conjugators for each are the fixed degree-24
permutations from the search recorded in `source/generation.txt`. All membership
and generator-word identities are checked by the kernel in the adjoining module.
The conjugators use only the marked inner generators. GAP words have been
reversed to account for Lean's left-composition convention.
Generator provenance: ATLAS M12d2G1-p24B0, as documented in `Extension.Seeds`.
-/

@[expose] public section
namespace Sporadic.Mathieu.M12ThreeConjugates
open M12ExceptionalExtension

/-- Evaluate a positive word in three specified elements. -/
def word {G : Type*} [Group G] (s : Fin 3 → G) : List (Fin 3) → G
  | [] => 1
  | i :: w => s i * word s w


def seedAPerm : Equiv.Perm (Fin 24) :=
  { toFun := ![22, 4, 17, 15, 1, 18, 19, 12, 10, 21, 8, 13, 7, 11, 16, 3, 14, 2, 5, 6, 23, 9, 0, 20]
    invFun := ![22, 4, 17, 15, 1, 18, 19, 12, 10, 21, 8, 13, 7, 11, 16, 3, 14, 2, 5, 6, 23, 9, 0, 20]
    left_inv := by decide +kernel
    right_inv := by decide +kernel }

theorem seedAPerm_eq : seedAPerm = generatorA := by decide +kernel

def seedBPerm : Equiv.Perm (Fin 24) :=
  { toFun := ![20, 1, 18, 19, 11, 10, 6, 22, 8, 9, 16, 21, 12, 7, 3, 15, 5, 0, 23, 14, 17, 4, 13, 2]
    invFun := ![17, 1, 23, 14, 21, 16, 6, 13, 8, 9, 5, 4, 12, 22, 19, 15, 10, 20, 2, 3, 0, 11, 7, 18]
    left_inv := by decide +kernel
    right_inv := by decide +kernel }

theorem seedBPerm_eq : seedBPerm = generatorB := by decide +kernel

def innerSeedAPerm : Equiv.Perm (Fin 24) :=
  { toFun := ![0, 3, 23, 1, 20, 12, 11, 7, 22, 9, 10, 6, 5, 19, 14, 17, 16, 15, 18, 13, 4, 21, 8, 2]
    invFun := ![0, 3, 23, 1, 20, 12, 11, 7, 22, 9, 10, 6, 5, 19, 14, 17, 16, 15, 18, 13, 4, 21, 8, 2]
    left_inv := by decide +kernel
    right_inv := by decide +kernel }

theorem innerSeedAPerm_eq : innerSeedAPerm = innerAPerm := by decide +kernel

def innerSeedBPerm : Equiv.Perm (Fin 24) :=
  { toFun := ![15, 2, 3, 1, 5, 12, 10, 19, 13, 22, 16, 0, 4, 18, 9, 11, 6, 21, 8, 23, 17, 20, 14, 7]
    invFun := ![11, 3, 1, 2, 12, 4, 16, 23, 18, 14, 6, 15, 5, 8, 22, 0, 10, 20, 13, 7, 21, 17, 9, 19]
    left_inv := by decide +kernel
    right_inv := by decide +kernel }

theorem innerSeedBPerm_eq : innerSeedBPerm = innerBPerm := by decide +kernel

/-- Lookup forms of the two literal extension generators and the second inverse. -/
def outerGenerators : Fin 3 → Carrier :=
  ![⟨seedAPerm, by rw [seedAPerm_eq]; exact Subgroup.subset_closure (by simp)⟩,
    ⟨seedBPerm, by rw [seedBPerm_eq]; exact Subgroup.subset_closure (by simp)⟩,
    (⟨seedBPerm, by rw [seedBPerm_eq]; exact Subgroup.subset_closure (by simp)⟩ : Carrier)⁻¹]

/-- Lookup forms of the two marked inner generators and the second inverse. -/
def innerGenerators : Fin 3 → Carrier :=
  ![⟨innerSeedAPerm, by rw [innerSeedAPerm_eq]; exact innerAPerm_mem⟩,
    ⟨innerSeedBPerm, by rw [innerSeedBPerm_eq]; exact innerBPerm_mem⟩,
    (⟨innerSeedBPerm, by rw [innerSeedBPerm_eq]; exact innerBPerm_mem⟩ : Carrier)⁻¹]

theorem innerGenerators_eq : ∀ i : Fin 3,
    innerGenerators i = ![innerA, innerB, innerB⁻¹] i := by decide +kernel

def representativePerm0 : Equiv.Perm (Fin 24) :=
  { toFun := ![21, 1, 18, 14, 17, 5, 10, 7, 8, 13, 6, 11, 15, 9, 3, 12, 16, 4, 2, 23, 20, 0, 22, 19]
    invFun := ![21, 1, 18, 14, 17, 5, 10, 7, 8, 13, 6, 11, 15, 9, 3, 12, 16, 4, 2, 23, 20, 0, 22, 19]
    left_inv := by decide +kernel
    right_inv := by decide +kernel }

def representativePerm1 : Equiv.Perm (Fin 24) :=
  { toFun := ![12, 19, 3, 2, 11, 6, 5, 14, 22, 13, 15, 4, 0, 9, 7, 10, 17, 16, 23, 1, 21, 20, 8, 18]
    invFun := ![12, 19, 3, 2, 11, 6, 5, 14, 22, 13, 15, 4, 0, 9, 7, 10, 17, 16, 23, 1, 21, 20, 8, 18]
    left_inv := by decide +kernel
    right_inv := by decide +kernel }

def representativePerm2 : Equiv.Perm (Fin 24) :=
  { toFun := ![1, 0, 20, 21, 9, 18, 23, 10, 17, 4, 7, 13, 19, 11, 15, 14, 22, 8, 5, 12, 2, 3, 16, 6]
    invFun := ![1, 0, 20, 21, 9, 18, 23, 10, 17, 4, 7, 13, 19, 11, 15, 14, 22, 8, 5, 12, 2, 3, 16, 6]
    left_inv := by decide +kernel
    right_inv := by decide +kernel }

def representativePerm : Fin 3 → Equiv.Perm (Fin 24) :=
  ![representativePerm0, representativePerm1, representativePerm2]

def firstConjugatorPerm0 : Equiv.Perm (Fin 24) :=
  { toFun := ![11, 22, 3, 23, 5, 12, 4, 19, 9, 2, 16, 6, 10, 18, 13, 15, 0, 17, 8, 1, 21, 20, 7, 14]
    invFun := ![16, 19, 9, 2, 6, 4, 11, 22, 18, 8, 12, 0, 5, 14, 23, 15, 10, 17, 13, 7, 21, 20, 1, 3]
    left_inv := by decide +kernel
    right_inv := by decide +kernel }

def firstConjugatorPerm1 : Equiv.Perm (Fin 24) :=
  { toFun := ![16, 2, 8, 13, 0, 17, 5, 14, 23, 3, 6, 20, 15, 18, 7, 12, 11, 4, 1, 9, 21, 10, 19, 22]
    invFun := ![4, 18, 1, 9, 17, 6, 10, 14, 2, 19, 21, 16, 15, 3, 7, 12, 0, 5, 13, 22, 11, 20, 23, 8]
    left_inv := by decide +kernel
    right_inv := by decide +kernel }

def firstConjugatorPerm2 : Equiv.Perm (Fin 24) :=
  { toFun := ![16, 7, 3, 19, 17, 20, 0, 9, 1, 2, 6, 12, 5, 8, 22, 10, 21, 15, 18, 13, 11, 4, 14, 23]
    invFun := ![6, 8, 9, 2, 21, 12, 10, 1, 13, 7, 15, 20, 11, 19, 22, 17, 0, 4, 18, 3, 5, 16, 14, 23]
    left_inv := by decide +kernel
    right_inv := by decide +kernel }

def firstConjugatorPerm : Fin 3 → Equiv.Perm (Fin 24) :=
  ![firstConjugatorPerm0, firstConjugatorPerm1, firstConjugatorPerm2]

def secondConjugatorPerm0 : Equiv.Perm (Fin 24) :=
  { toFun := ![17, 1, 7, 18, 16, 11, 20, 8, 3, 9, 4, 10, 12, 14, 23, 6, 5, 15, 2, 13, 0, 21, 19, 22]
    invFun := ![20, 1, 18, 8, 10, 16, 15, 2, 7, 9, 11, 5, 12, 19, 13, 17, 4, 0, 3, 22, 6, 21, 23, 14]
    left_inv := by decide +kernel
    right_inv := by decide +kernel }

def secondConjugatorPerm1 : Equiv.Perm (Fin 24) :=
  { toFun := ![20, 13, 8, 14, 4, 5, 12, 9, 19, 23, 16, 17, 21, 18, 1, 0, 10, 6, 7, 22, 11, 15, 2, 3]
    invFun := ![15, 14, 22, 23, 4, 5, 17, 18, 2, 7, 16, 20, 6, 1, 3, 21, 10, 11, 13, 8, 0, 12, 19, 9]
    left_inv := by decide +kernel
    right_inv := by decide +kernel }

def secondConjugatorPerm2 : Equiv.Perm (Fin 24) :=
  { toFun := ![4, 1, 14, 2, 6, 16, 15, 19, 3, 13, 0, 11, 21, 7, 18, 10, 17, 12, 8, 22, 20, 5, 9, 23]
    invFun := ![10, 1, 3, 8, 0, 21, 4, 13, 18, 22, 15, 11, 17, 9, 2, 6, 5, 16, 14, 7, 20, 12, 19, 23]
    left_inv := by decide +kernel
    right_inv := by decide +kernel }

def secondConjugatorPerm : Fin 3 → Equiv.Perm (Fin 24) :=
  ![secondConjugatorPerm0, secondConjugatorPerm1, secondConjugatorPerm2]

def representativeWords : Fin 3 → List (Fin 3) :=
  ![[0, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0],
    [0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2],
    [1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 0, 2, 0, 2]]

def firstConjugatorWords : Fin 3 → List (Fin 3) :=
  ![[0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1],
    [0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0],
    [2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 0]]

def secondConjugatorWords : Fin 3 → List (Fin 3) :=
  ![[1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0],
    [0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2],
    [2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 2]]

def innerAWords : Fin 3 → List (Fin 3) :=
  ![[1, 2, 1, 2, 1, 0, 2, 1, 0, 1, 2, 0, 1, 2, 1, 2, 1],
    [0, 2, 0, 1, 0, 2, 1, 2, 0, 2, 1, 2, 1, 0, 2, 0],
    [0, 1, 0, 2, 1, 0, 1, 0, 2, 1, 0, 2, 1, 0, 1, 2, 0, 1, 0, 1]]

def innerBWords : Fin 3 → List (Fin 3) :=
  ![[0, 1, 0, 2, 1, 0, 1, 2, 1, 0, 2, 0, 1, 2, 1, 2, 0, 2, 0, 1],
    [1, 0, 2, 1, 0, 2, 1, 2, 1, 0, 2, 0, 1, 2, 0, 1],
    [0, 2, 1, 0, 1, 2, 0, 2, 1, 0, 1, 0, 1, 0, 2, 0]]

end Sporadic.Mathieu.M12ThreeConjugates
