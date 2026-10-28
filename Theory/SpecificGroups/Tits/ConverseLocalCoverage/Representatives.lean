module

public import Theory.SpecificGroups.Tits.ExceptionalParabolics

/-!
# Candidate Sylow double-coset representatives in the Tits group

These eighteen explicit positive Parrott words are the common input to two
independent certificates: coverage by Sylow double cosets, and generation
of the ambient group after adjoining any representative with index at least
three. The definitions themselves assert neither certificate. The first
three words are the identity and the two marked parabolic reflections.

Source: Parrott (1972), §5, p.683, in the certified Atlas marking. The
untrusted exploration in `source/explore.py` identifies this candidate list;
only separately proved Lean theorems can establish coverage or generation.
-/

@[expose] public section
namespace Tits.ConverseLocalCoverage

/-- Explicit positive words, with the three parabolic cases first. -/
def doubleCosetWord : Fin 18 → List ParrottGenerator :=
  ![[],
    [.r1],
    [.r8],
    [.r1, .r8],
    [.r8, .r1],
    [.r1, .r8, .r1],
    [.r8, .r1, .r8],
    [.r1, .r8, .r1, .r8],
    [.r8, .r1, .r8, .r1],
    [.r1, .r8, .r1, .r8, .r1],
    [.r8, .r1, .r8, .r1, .r8],
    [.r1, .r8, .r1, .r8, .r1, .r8],
    [.r8, .r1, .r8, .r1, .r8, .r1],
    [.r1, .r8, .r1, .r8, .r1, .r8, .r1],
    [.r8, .r1, .r8, .r1, .r8, .r1, .r8],
    [.r1, .r8, .r1, .r8, .r1, .r8, .r1, .r8],
    [.r1, .r8, .r1, .r8, .r1, .r8, .r1, .s1, .r1],
    [.r1, .r8, .r1, .r8, .r1, .r8, .r1, .s1, .r1, .r8]]

/-- Evaluation uses Lean's left-action multiplication convention. -/
def doubleCosetRep (i : Fin 18) : Atlas1600Group :=
  ((doubleCosetWord i).map atlas1600ParrottAssignment).prod

@[simp] theorem doubleCosetRep_zero : doubleCosetRep 0 = 1 := rfl

@[simp] theorem doubleCosetRep_one :
    doubleCosetRep 1 = atlas1600ParrottAssignment .r1 := by
  simp [doubleCosetRep, doubleCosetWord]

@[simp] theorem doubleCosetRep_two :
    doubleCosetRep 2 = atlas1600ParrottAssignment .r8 := by
  simp [doubleCosetRep, doubleCosetWord]

end Tits.ConverseLocalCoverage
end
