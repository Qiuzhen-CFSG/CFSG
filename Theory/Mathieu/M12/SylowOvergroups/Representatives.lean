module

public import Theory.Mathieu.M12.Basic
public import Theory.Mathieu.M12.Properties.SylowAutomorphismGroup.Coordinates

/-!
# Proposed Sylow double-coset representatives in M₁₂

These 44 words lie in the actual degree-twelve Witt-design automorphism group.
The proposed double-coset decomposition uses the marked Sylow subgroup of
`SmallParabolicPair`. Membership of each representative is proved by evaluation
in the two standard generators. The separate proposition `Covers` states the
remaining exhaustiveness obligation; this module does not assert it.

The words were found by breadth-first enumeration followed by Sylow double-coset
enumeration. Their short prime-order obstructions are checked in `Obstructions`.
Source context: Aschbacher, *Overgroups of Sylow subgroups in sporadic groups*,
Memoirs AMS 60 (1986), no. 343; GLS3 Table 5.3b; Aschbacher–Smith, printed p.511.
-/

@[expose] public section
namespace Sporadic.Mathieu.M12SmallPair.SylowOvergroups

noncomputable def standardGenerator (i : Fin 2) : M12 :=
  ![⟨m12GeneratorA, m12GeneratorA_mem⟩, ⟨m12GeneratorB, m12GeneratorB_mem⟩] i

noncomputable def standardWord : List (Fin 2) → M12
  | [] => 1
  | i :: w => standardGenerator i * standardWord w

/-- Untrusted word data; exhaustiveness is a separate mathematical assertion. -/
def representativeWords : Array (List (Fin 2)) := #[
  [],
  [0],
  [1],
  [0,1],
  [1,1],
  [0,1,0],
  [1,0,1],
  [0,1,0,1],
  [0,1,1,0],
  [1,0,1,1],
  [1,1,0,1],
  [0,1,0,1,0],
  [0,1,0,1,1],
  [0,1,1,0,1],
  [0,1,0,1,1,0],
  [0,1,1,0,1,0],
  [0,1,1,0,1,1],
  [0,1,0,1,0,1,0],
  [0,1,0,1,0,1,1],
  [0,1,0,1,1,0,1],
  [1,0,1,1,0,1,0],
  [0,1,0,1,1,0,1,0],
  [0,1,0,1,1,0,1,1],
  [1,0,1,0,1,0,1,0],
  [1,0,1,0,1,0,1,1],
  [0,1,0,1,0,1,0,1,0],
  [0,1,0,1,0,1,0,1,1],
  [1,0,1,1,0,1,0,1,1],
  [0,1,0,1,0,1,0,1,1,0],
  [0,1,0,1,0,1,1,0,1,0],
  [0,1,0,1,1,0,1,0,1,0],
  [0,1,1,0,1,0,1,0,1,1],
  [1,0,1,0,1,0,1,1,0,1],
  [0,1,0,1,0,1,0,1,1,0,1],
  [0,1,1,0,1,0,1,1,0,1,1],
  [0,1,0,1,0,1,0,1,1,0,1,1],
  [0,1,1,0,1,0,1,1,0,1,0,1],
  [1,0,1,1,0,1,0,1,0,1,1,0],
  [1,0,1,0,1,0,1,0,1,1,0,1,1],
  [0,1,0,1,1,0,1,0,1,1,0,1,0,1],
  [0,1,0,1,0,1,0,1,1,0,1,1,0,1,1,0,1,0],
  [1,1,0,1,1,0,1,0,1,0,1,0,1,1,0,1,0,1,0],
  [0,1,0,1,1,0,1,0,1,1,0,1,0,1,0,1,1,0,1,0],
  [0,1,0,1,1,0,1,0,1,1,0,1,0,1,0,1,0,1,1,0,1,1]]

noncomputable def representative (i : Fin 44) : M12 :=
  standardWord (representativeWords[i.val]!)

/-- Exact double-coset coverage, with both factors in the actual marked Sylow
subgroup. This is not assumed by any unconditional theorem in this module. -/
def Covers : Prop :=
  ∀ g : M12, ∃ (i : Fin 44) (s t : sylowCandidate),
    (s : M12) * representative i * (t : M12) = g

/-- Three letters in the marked Sylow subgroup and one chosen representative. -/
noncomputable def localGenerator (i : Fin 44) (j : Fin 4) : M12 :=
  ![(SylowAutomorphismGroup.generator 0 : M12),
    (SylowAutomorphismGroup.generator 1 : M12),
    (SylowAutomorphismGroup.generator 2 : M12), representative i] j

noncomputable def localWord (i : Fin 44) : List (Fin 4) → M12
  | [] => 1
  | j :: w => localGenerator i j * localWord i w

/-- Suggested short words producing elements of order five or eleven, except
at the three representatives lying in the marked parabolics. -/
def obstructionWords : Array (List (Fin 4)) := #[
  [],
  [0,3,2],
  [0,3],
  [3],
  [0,3,3],
  [2,3],
  [3],
  [3],
  [0,3,2],
  [0,2,0,3],
  [0,1,3],
  [3],
  [0,0,3],
  [1,3],
  [0,3],
  [0,3,1,3],
  [3],
  [1,3],
  [2,3],
  [0,3],
  [1,3],
  [3],
  [0,0,3],
  [3],
  [3],
  [0,2,3],
  [3],
  [1,3],
  [3],
  [0,3],
  [0,1,3],
  [3],
  [3],
  [3],
  [3],
  [1,3],
  [0,0,3],
  [],
  [3],
  [3],
  [3,3],
  [],
  [0,3,3],
  [0,3,3]]

noncomputable def obstruction (i : Fin 44) : M12 :=
  localWord i (obstructionWords[i.val]!)

/-- Word evaluation preserves membership in any subgroup containing the letters. -/
theorem localWord_mem (H : Subgroup M12) (hS : sylowCandidate ≤ H)
    (i : Fin 44) (hi : representative i ∈ H) (w : List (Fin 4)) :
    localWord i w ∈ H := by
  have hg (j : Fin 4) : localGenerator i j ∈ H := by
    fin_cases j
    · exact hS (SylowAutomorphismGroup.generator 0).property
    · exact hS (SylowAutomorphismGroup.generator 1).property
    · exact hS (SylowAutomorphismGroup.generator 2).property
    · exact hi
  induction w with
  | nil => exact H.one_mem
  | cons j w ih => exact H.mul_mem (hg j) ih

end Sporadic.Mathieu.M12SmallPair.SylowOvergroups
