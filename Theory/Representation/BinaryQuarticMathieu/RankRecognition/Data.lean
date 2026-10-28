module

public import Theory.Representation.BinaryQuarticMathieu.RankRecognition.FiniteModel

/-!
# Candidate classes and their finite marking certificates

The labels are transcribed from `../source/orbit-witnesses.json`, whose orbit
and rank assertions remain untrusted. This module certifies just the partition
sizes, its zero class, and equality of its fourth class with the existing marked
22-point configuration. Short rows keep the kernel checks inexpensive.

The four displayed histograms are distinct functions on all natural ranks.
Their occurrence as actual contraction histograms, except for the zero vector,
is a separate obligation. The orbit and representative calculations feed
`Reduction.lean`; these label certificates alone prove neither assertion.
-/

@[expose] public section

namespace BinaryQuarticMathieu.RankRecognition

/-- The representative attached to each of the four candidate classes. -/
def representative (c : Fin 4) : Word := ![0, 1, 2, 8] c

/-- Claimed nonzero histogram of the class represented by the word 1. -/
def largeDistribution (r : Nat) : Nat :=
  if r = 0 then 2 else if r = 4 then 18 else if r = 6 then 540 else
    if r = 8 then 464 else 0

/-- Claimed nonzero histogram of the class represented by the word 2. -/
def pairDistribution (r : Nat) : Nat :=
  if r = 0 then 2 else if r = 2 then 30 else if r = 4 then 32 else
    if r = 6 then 960 else 0

def profile (c : Fin 4) : Nat → Nat :=
  ![zeroDistribution, largeDistribution, pairDistribution, pointDistribution] c

def classSize (c : Fin 4) : Nat := ![1, 770, 231, 22] c

/-- Labels transcribed from the untrusted orbit witness. These are not yet
asserted to be orbits or contraction-rank classes. -/
def wordClassRows : Array (Array (Fin 4)) := #[
  #[0, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 2, 2, 1, 2, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 1],
  #[1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2],
  #[1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1],
  #[2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1],
  #[2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1],
  #[2, 3, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2],
  #[2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2],
  #[1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2],
  #[2, 2, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1],
  #[1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1],
  #[1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 1, 1, 1],
  #[2, 2, 1, 2, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
  #[1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1],
  #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1],
  #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 1],
  #[2, 1, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1],
  #[1, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1],
  #[1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
  #[1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1],
  #[2, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 1],
  #[1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1],
  #[1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 1, 1, 1, 2, 1],
  #[1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1],
  #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 1],
  #[1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 1],
  #[1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1],
  #[1, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2],
  #[2, 1, 2, 1, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1],
  #[1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 1],
  #[1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1],
  #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1],
  #[1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2]
]

/-- Two short lookups avoid repeated traversal of a 1024-entry literal during
kernel reduction. Every input of `Word` is covered by the checks below. -/
def wordClass (n : Word) : Fin 4 :=
  (wordClassRows[n.val / 32]!).getD (n.val % 32) 0

set_option maxRecDepth 4096 in
theorem wordClass_counts : ∀ c : Fin 4,
    (Finset.univ.filter (fun n : Word => wordClass n = c)).card = classSize c := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem wordClass_zero_iff : ∀ n : Word, wordClass n = 0 ↔ n = 0 := by
  decide +kernel

/-- Each literal marked point fits in the ten binary coordinates. -/
theorem pointWord_lt : ∀ i : Fin 22, pointWord i < 1024 := by
  decide +kernel

/-- Packed word corresponding to the existing marked point, with the existing
marking applied exactly once. -/
def pointIndexWord (i : Fin 22) : Word :=
  ⟨pointWord (pointMarking.symm i), pointWord_lt _⟩

theorem decode_pointIndexWord (i : Fin 22) : decode (pointIndexWord i) = point i := rfl

set_option maxRecDepth 4096 in
private theorem wordClass_pointIndexWord_iff : ∀ n : Word,
    wordClass n = 3 ↔ ∃ i : Fin 22, pointIndexWord i = n := by
  decide +kernel

theorem wordClass_point_iff (n : Word) :
    wordClass n = 3 ↔ decode n ∈ Set.range point := by
  rw [wordClass_pointIndexWord_iff]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i, (decode_pointIndexWord i).symm⟩
  · rintro ⟨i, hi⟩
    exact ⟨i, decode_injective ((decode_pointIndexWord i).trans hi)⟩

private theorem profile_separated : ∀ c d : Fin 4,
    profile c 0 = profile d 0 → profile c 2 = profile d 2 →
    profile c 4 = profile d 4 → c = d := by
  decide +kernel

theorem profile_injective : Function.Injective profile := by
  intro c d h
  exact profile_separated c d (congrFun h 0) (congrFun h 2) (congrFun h 4)

theorem representative_zero_distribution :
    rankDistribution quartic (decode (representative 0)) = profile 0 := by
  have hz : decode (representative 0) = 0 := by decide +kernel
  rw [hz]
  exact rankDistribution_zero quartic

end BinaryQuarticMathieu.RankRecognition
