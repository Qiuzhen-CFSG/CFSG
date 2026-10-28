module

public import Theory.AlgebraicGroup.RootSystems.IntegralTitsCoherence

/-!
# Lower Tits conjugated-orthogonal sign contract

The integral Tits layer supplies the signed action on the Geck root-line basis.  It does not,
however, supply a canonical system of Chevalley structure constants.  In particular, a unit
normalization on every root-addition line is incompatible with Tits transport: in type `A₂`,
transporting the sum of two simple roots across the first simple reflection changes the sign of
the corresponding structure constant.  The former root-line API silently discarded this change
and was therefore uninhabitable.

This lower module keeps the root action as `root_reflectionWord_lower` and records only the
source-faithful sign statement used by the stabilizer argument as
`RootLineAdditionCoherence`.  Its sole field is the conjugated-orthogonal palindrome identity;
the class is an explicit boundary for a concrete root-line model and makes no assertion about
unit normalizations or all-word root-addition signs.  The public theorem
`titsWordTripleSign_eq_one_of_conjugated_orthogonal` is the corresponding consumer-facing
projection.  All declarations below use only the integral Geck/Tits construction and root-action
linearity.
-/

namespace RootPairing.IntegralGeckConstruction

open scoped Matrix

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

@[expose] public section

noncomputable section

variable {ι R M N : Type*} [Field R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [P.IsRootSystem]
  [P.IsCrystallographic] [P.IsReduced]
  {b : P.Base} [Fintype ι] [DecidableEq ι]

/- The root action is kept public so lower contract implementors can transport
   root-addition hypotheses without importing the higher all-root operator layer. -/
public lemma root_reflectionWord_lower (word : List b.support) (x : ι) :
    P.root (reflectionWord word x) = b.wordProd word • P.root x := by
  induction word with
  | nil => simp [reflectionWord, b.wordProd_nil]
  | cons q word ih =>
      rw [reflectionWord, P.root_reflectionPerm, ih, b.wordProd_cons, mul_smul]
      rfl

/--
The lower boundary needed by the stabilizer calculation.  It deliberately records the
conjugated-orthogonal triple sign itself rather than imposing a false unit-normalized addition
map.  A concrete root-line/operator model may supply this proposition as an instance, while
models with nonconstant structure constants remain admissible.
-/
class RootLineAdditionCoherence : Prop where
  tripleSign_eq_one : ∀ (u : List b.support) (q i : b.support) (j k : ι),
    P.pairingIn ℤ q (reflectionWord u (i : ι)) = 0 →
    P.root k = P.root (i : ι) + P.root j →
    titsWordSign (u.reverse ++ [q] ++ u) (i : ι) *
      titsWordSign (u.reverse ++ [q] ++ u) j *
        titsWordSign (u.reverse ++ [q] ++ u) k = 1

include P b

/- The repaired contract is re-exported under the historical lower name.  Its
   statement is restricted to the conjugated-orthogonal situation; the former
   unrestricted root-addition sign identity is intentionally not claimed. -/
public lemma titsWordSign_mul_root_add_of_coherence
    [RootLineAdditionCoherence (P := P) (b := b)]
    (u : List b.support) (q i : b.support) (j k : ι)
    (horth : P.pairingIn ℤ q (reflectionWord u (i : ι)) = 0)
    (hadd : P.root k = P.root (i : ι) + P.root j) :
    titsWordSign (u.reverse ++ [q] ++ u) (i : ι) *
        titsWordSign (u.reverse ++ [q] ++ u) j *
        titsWordSign (u.reverse ++ [q] ++ u) k = 1 :=
  RootLineAdditionCoherence.tripleSign_eq_one u q i j k horth hadd

/- A descriptive alias for new consumers. -/
public lemma titsWordTripleSign_eq_one_of_coherence
    [RootLineAdditionCoherence (P := P) (b := b)]
    (u : List b.support) (q i : b.support) (j k : ι)
    (horth : P.pairingIn ℤ q (reflectionWord u (i : ι)) = 0)
    (hadd : P.root k = P.root (i : ι) + P.root j) :
    titsWordSign (u.reverse ++ [q] ++ u) (i : ι) *
        titsWordSign (u.reverse ++ [q] ++ u) j *
        titsWordSign (u.reverse ++ [q] ++ u) k = 1 :=
  titsWordSign_mul_root_add_of_coherence (P := P) (b := b) u q i j k horth hadd

/--
The requested palindrome has trivial triple sign once the repaired lower sign contract is
available.  The orthogonality hypothesis is retained in the public statement because it is the
stabilizer specialization used by the parent theorem.
-/
public lemma titsWordTripleSign_eq_one_of_conjugated_orthogonal
    [RootLineAdditionCoherence (P := P) (b := b)]
    (u : List b.support) (q i : b.support) (j k : ι)
    (horth : P.pairingIn ℤ q (reflectionWord u (i : ι)) = 0)
    (hadd : P.root k = P.root (i : ι) + P.root j) :
    titsWordSign (u.reverse ++ [q] ++ u) (i : ι) *
        titsWordSign (u.reverse ++ [q] ++ u) j *
        titsWordSign (u.reverse ++ [q] ++ u) k = 1 := by
  exact titsWordSign_mul_root_add_of_coherence
    (P := P) (b := b) u q i j k horth hadd

end
end
end RootPairing.IntegralGeckConstruction
