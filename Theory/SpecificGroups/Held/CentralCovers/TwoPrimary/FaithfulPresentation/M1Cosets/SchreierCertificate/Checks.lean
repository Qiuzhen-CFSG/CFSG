module

public import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Cosets.SchreierData
import Mathlib.Tactic.FinCases

/-!
# Checking the Held Schreier tree and symbol numbering

For a positive edge marked zero, one of the two representative words extends
exactly the other by the appropriate signed letter. Every other positive edge
has a label in 4..2062, whose entry in `symbolEdge` is exactly that edge.
These are finite syntactic identities in the published data, checked by kernel
reduction in blocks of 64 vertices. The sample block took 0.684 seconds of
kernel type checking; no native evaluation or external computation is trusted.

Source: John Bray's ATLAS `HeG1-P1.M` and the retained right-action permutation
data, as described in `M1Cosets/source/README.md`. The abstract group meaning
of these checks is proved in the parent `SchreierCertificate` module.
-/

namespace Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Cosets.Schreier

/-- The syntactic tree identity or the precise non-tree symbol lookup. -/
@[expose] public def PositiveCheck (i : Fin 2058) (a : Fin 2) : Prop :=
  if positiveIndex i.val a = 0 then
    representativeWord (destination i (a, true)).val = representativeWord i.val ++ [(a, true)] ∨
    representativeWord i.val = representativeWord (destination i (a, true)).val ++ [(a, false)]
  else
    4 ≤ positiveIndex i.val a ∧ positiveIndex i.val a < 2063 ∧
    symbolEdge (positiveIndex i.val a - 4) = (i, a)

public instance (i : Fin 2058) (a : Fin 2) : Decidable (PositiveCheck i a) := by
  unfold PositiveCheck
  infer_instance

private theorem allPointsByBlocks (P : Fin 2058 → Prop)
    (h : ∀ q : Fin 33, ∀ r : Fin 64, P (Fin.ofNat 2058 (q.val * 64 + r.val))) :
    ∀ i, P i := by
  intro i
  have hi := h ⟨i.val / 64, by omega⟩ ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
  have he : i.val / 64 * 64 + i.val % 64 = i.val := by omega
  simpa only [he, Fin.ofNat_eq_cast, Fin.cast_val_eq_self] using hi

private theorem positiveCheckBlock0 : ∀ r : Fin 64, ∀ a : Fin 2,
    PositiveCheck (Fin.ofNat 2058 (0 * 64 + r.val)) a := by
  decide +kernel

private theorem positiveCheckBlock1 : ∀ r : Fin 64, ∀ a : Fin 2,
    PositiveCheck (Fin.ofNat 2058 (1 * 64 + r.val)) a := by
  decide +kernel

private theorem positiveCheckBlock2 : ∀ r : Fin 64, ∀ a : Fin 2,
    PositiveCheck (Fin.ofNat 2058 (2 * 64 + r.val)) a := by
  decide +kernel

private theorem positiveCheckBlock3 : ∀ r : Fin 64, ∀ a : Fin 2,
    PositiveCheck (Fin.ofNat 2058 (3 * 64 + r.val)) a := by
  decide +kernel

private theorem positiveCheckBlock4 : ∀ r : Fin 64, ∀ a : Fin 2,
    PositiveCheck (Fin.ofNat 2058 (4 * 64 + r.val)) a := by
  decide +kernel

private theorem positiveCheckBlock5 : ∀ r : Fin 64, ∀ a : Fin 2,
    PositiveCheck (Fin.ofNat 2058 (5 * 64 + r.val)) a := by
  decide +kernel

private theorem positiveCheckBlock6 : ∀ r : Fin 64, ∀ a : Fin 2,
    PositiveCheck (Fin.ofNat 2058 (6 * 64 + r.val)) a := by
  decide +kernel

private theorem positiveCheckBlock7 : ∀ r : Fin 64, ∀ a : Fin 2,
    PositiveCheck (Fin.ofNat 2058 (7 * 64 + r.val)) a := by
  decide +kernel

private theorem positiveCheckBlock8 : ∀ r : Fin 64, ∀ a : Fin 2,
    PositiveCheck (Fin.ofNat 2058 (8 * 64 + r.val)) a := by
  decide +kernel

private theorem positiveCheckBlock9 : ∀ r : Fin 64, ∀ a : Fin 2,
    PositiveCheck (Fin.ofNat 2058 (9 * 64 + r.val)) a := by
  decide +kernel

private theorem positiveCheckBlock10 : ∀ r : Fin 64, ∀ a : Fin 2,
    PositiveCheck (Fin.ofNat 2058 (10 * 64 + r.val)) a := by
  decide +kernel

private theorem positiveCheckBlock11 : ∀ r : Fin 64, ∀ a : Fin 2,
    PositiveCheck (Fin.ofNat 2058 (11 * 64 + r.val)) a := by
  decide +kernel

private theorem positiveCheckBlock12 : ∀ r : Fin 64, ∀ a : Fin 2,
    PositiveCheck (Fin.ofNat 2058 (12 * 64 + r.val)) a := by
  decide +kernel

private theorem positiveCheckBlock13 : ∀ r : Fin 64, ∀ a : Fin 2,
    PositiveCheck (Fin.ofNat 2058 (13 * 64 + r.val)) a := by
  decide +kernel

private theorem positiveCheckBlock14 : ∀ r : Fin 64, ∀ a : Fin 2,
    PositiveCheck (Fin.ofNat 2058 (14 * 64 + r.val)) a := by
  decide +kernel

private theorem positiveCheckBlock15 : ∀ r : Fin 64, ∀ a : Fin 2,
    PositiveCheck (Fin.ofNat 2058 (15 * 64 + r.val)) a := by
  decide +kernel

private theorem positiveCheckBlock16 : ∀ r : Fin 64, ∀ a : Fin 2,
    PositiveCheck (Fin.ofNat 2058 (16 * 64 + r.val)) a := by
  decide +kernel

private theorem positiveCheckBlock17 : ∀ r : Fin 64, ∀ a : Fin 2,
    PositiveCheck (Fin.ofNat 2058 (17 * 64 + r.val)) a := by
  decide +kernel

private theorem positiveCheckBlock18 : ∀ r : Fin 64, ∀ a : Fin 2,
    PositiveCheck (Fin.ofNat 2058 (18 * 64 + r.val)) a := by
  decide +kernel

private theorem positiveCheckBlock19 : ∀ r : Fin 64, ∀ a : Fin 2,
    PositiveCheck (Fin.ofNat 2058 (19 * 64 + r.val)) a := by
  decide +kernel

private theorem positiveCheckBlock20 : ∀ r : Fin 64, ∀ a : Fin 2,
    PositiveCheck (Fin.ofNat 2058 (20 * 64 + r.val)) a := by
  decide +kernel

private theorem positiveCheckBlock21 : ∀ r : Fin 64, ∀ a : Fin 2,
    PositiveCheck (Fin.ofNat 2058 (21 * 64 + r.val)) a := by
  decide +kernel

private theorem positiveCheckBlock22 : ∀ r : Fin 64, ∀ a : Fin 2,
    PositiveCheck (Fin.ofNat 2058 (22 * 64 + r.val)) a := by
  decide +kernel

private theorem positiveCheckBlock23 : ∀ r : Fin 64, ∀ a : Fin 2,
    PositiveCheck (Fin.ofNat 2058 (23 * 64 + r.val)) a := by
  decide +kernel

private theorem positiveCheckBlock24 : ∀ r : Fin 64, ∀ a : Fin 2,
    PositiveCheck (Fin.ofNat 2058 (24 * 64 + r.val)) a := by
  decide +kernel

private theorem positiveCheckBlock25 : ∀ r : Fin 64, ∀ a : Fin 2,
    PositiveCheck (Fin.ofNat 2058 (25 * 64 + r.val)) a := by
  decide +kernel

private theorem positiveCheckBlock26 : ∀ r : Fin 64, ∀ a : Fin 2,
    PositiveCheck (Fin.ofNat 2058 (26 * 64 + r.val)) a := by
  decide +kernel

private theorem positiveCheckBlock27 : ∀ r : Fin 64, ∀ a : Fin 2,
    PositiveCheck (Fin.ofNat 2058 (27 * 64 + r.val)) a := by
  decide +kernel

private theorem positiveCheckBlock28 : ∀ r : Fin 64, ∀ a : Fin 2,
    PositiveCheck (Fin.ofNat 2058 (28 * 64 + r.val)) a := by
  decide +kernel

private theorem positiveCheckBlock29 : ∀ r : Fin 64, ∀ a : Fin 2,
    PositiveCheck (Fin.ofNat 2058 (29 * 64 + r.val)) a := by
  decide +kernel

private theorem positiveCheckBlock30 : ∀ r : Fin 64, ∀ a : Fin 2,
    PositiveCheck (Fin.ofNat 2058 (30 * 64 + r.val)) a := by
  decide +kernel

private theorem positiveCheckBlock31 : ∀ r : Fin 64, ∀ a : Fin 2,
    PositiveCheck (Fin.ofNat 2058 (31 * 64 + r.val)) a := by
  decide +kernel

private theorem positiveCheckBlock32 : ∀ r : Fin 64, ∀ a : Fin 2,
    PositiveCheck (Fin.ofNat 2058 (32 * 64 + r.val)) a := by
  decide +kernel

/-- All 4116 positive edges have the certified tree or symbol interpretation. -/
public theorem positiveCheck (i : Fin 2058) (a : Fin 2) : PositiveCheck i a := by
  have h : ∀ i : Fin 2058, ∀ a : Fin 2, PositiveCheck i a := by
    apply allPointsByBlocks
    intro q
    fin_cases q
    · exact positiveCheckBlock0
    · exact positiveCheckBlock1
    · exact positiveCheckBlock2
    · exact positiveCheckBlock3
    · exact positiveCheckBlock4
    · exact positiveCheckBlock5
    · exact positiveCheckBlock6
    · exact positiveCheckBlock7
    · exact positiveCheckBlock8
    · exact positiveCheckBlock9
    · exact positiveCheckBlock10
    · exact positiveCheckBlock11
    · exact positiveCheckBlock12
    · exact positiveCheckBlock13
    · exact positiveCheckBlock14
    · exact positiveCheckBlock15
    · exact positiveCheckBlock16
    · exact positiveCheckBlock17
    · exact positiveCheckBlock18
    · exact positiveCheckBlock19
    · exact positiveCheckBlock20
    · exact positiveCheckBlock21
    · exact positiveCheckBlock22
    · exact positiveCheckBlock23
    · exact positiveCheckBlock24
    · exact positiveCheckBlock25
    · exact positiveCheckBlock26
    · exact positiveCheckBlock27
    · exact positiveCheckBlock28
    · exact positiveCheckBlock29
    · exact positiveCheckBlock30
    · exact positiveCheckBlock31
    · exact positiveCheckBlock32
  exact h i a

end Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Cosets.Schreier
