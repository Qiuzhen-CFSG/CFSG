module

public import CFSG.Quasithin.ChapterE.Section01.Basic
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.BinaryUpper.Flags

/-!
# Binary classical flag route to E.1.14(1)

`Flags` proves generation by two actual flag overgroups. For dimensions four
and five, the outer-root flag overgroup should be solvable. The middle-root
flag overgroup is solvable in dimension four; in dimension five its unipotent
kernel has an almost-simple binary PSL₃ quotient, including the graph extension.

The interface below states only that latter structural property. The normal
subgroup is intrinsic to the local group, its order is a power of two, and the
quotient has an actual PSL₃(2) generalized Fitting subgroup. It contains no
E-generation conclusion. Constructing this quotient for flags compatible with
the ambient Sylow subgroup, and proving the resulting local E-generation
bounds, remain outstanding. No case of E.1.14 is asserted here yet.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
E.1.12--14, printed p.214; E.1.14 cites Aschbacher (1982), Lemma 4.7.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterE.ValuesEvenClassical.BinaryUpper

/-- The genuine quotient structure required at the middle flag in dimension
five. This is an upstream local-structure assertion, not a generation bound. -/
def HasBinaryMiddleSection (H : Type*) [Group H] [Finite H] : Prop :=
  ∃ (Q : Subgroup H) (hQ : Q.Normal),
    letI : Q.Normal := hQ
    IsPGroup 2 Q ∧
      IsSimpleGroup (Theory.GroupTheory.generalizedFitting (H ⧸ Q)) ∧
      Nonempty (Theory.GroupTheory.generalizedFitting (H ⧸ Q) ≃* PSL 3) ∧
      ∃ S : Sylow 2 (H ⧸ Q),
        Theory.GroupTheory.generalizedFitting (H ⧸ Q) ⊔ (S : Subgroup (H ⧸ Q)) = ⊤

end CFSG.Quasithin.ChapterE.ValuesEvenClassical.BinaryUpper
