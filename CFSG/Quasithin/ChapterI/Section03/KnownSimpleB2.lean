module

public import CFSG.KnownSimple.CarrierCatalogue
public import Theory.SpecificGroups.Alternating.SmallInvolutoryTwoComponents
public import Theory.SpecificGroups.Suzuki.InvolutoryTwoComponents
public import Theory.SpecificGroups.SymplecticFour.Binary.ProjectiveDerived

/-!
# The known-simple input to GLS II, Lemma 5.28

The source B₂ condition asks that every two-component of the fixed subgroup
of an automorphism of order two be quasisimple. It uses the intrinsic odd
core in `Subgroup.IsTwoComponent`, not an ordinary-component hypothesis.

This module proves the prime cyclic, A₅/A₆/A₇ and full Suzuki branches of
`CFSG.KnownSimple.IsKnownSimpleCarrier`. Transport is through the actual
carrier isomorphism and its induced fixed-subgroup isomorphism. The binary
projective symplectic derived carrier is handled through its actual A₆
equivalence, with the central quotient taken before the commutator. The remaining
alternating, classical, exceptional, small-derived and sporadic branches are
still needed before the B₂ property for the whole catalogue can be asserted.

Sources: GLS II, Definition 2.4, and Lemma 5.28 (`refs/KGroup/GLS2/ChapterA.tex`
and `ChapterB.tex`); Aschbacher--Smith, I.3, printed p.414 / PDF p.425.
-/

public section

open Theory.GroupTheory

namespace CFSG.Quasithin.ChapterI.Section03.KnownSimpleB2

variable {S : Type*} [Group S]

/-- The cyclic catalogue branch has no two-components in its fixed subgroups. -/
theorem of_primeCyclic (hS : KnownSimple.IsPrimeCyclicCarrier S) :
    HasInvolutoryB2 S := by
  obtain ⟨p, _, ⟨e⟩⟩ := hS
  exact (HasInvolutoryB2.of_solvable (G := Multiplicative (ZMod p))).of_mulEquiv e

/-- Transport all involutory automorphisms in the small alternating branches. -/
theorem of_small_alternating (n : ℕ) (hn : 5 ≤ n) (hn7 : n ≤ 7)
    (hS : Nonempty (S ≃* alternatingGroup (Fin n))) : HasInvolutoryB2 S := by
  obtain ⟨e⟩ := hS
  exact (alternatingGroup.small_hasInvolutoryB2 n hn hn7).of_mulEquiv e

/-- The complete Suzuki branch with exactly the catalogue's parameter convention. -/
theorem of_suzuki (m : ℕ) (hm : 1 ≤ m)
    (hS : Nonempty (S ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)) :
    HasInvolutoryB2 S := by
  obtain ⟨e⟩ := hS
  exact (BenderSuzuki.MatrixGroups.suzuki_hasInvolutoryB2 m hm).of_mulEquiv e

/-- The small derived symplectic constructor uses the actual commutator of PSp₄(2). -/
theorem of_small_symplectic
    (hS : Nonempty (S ≃* commutator (ClassicalGroup.PSp 2 (ZMod 2)))) :
    HasInvolutoryB2 S := by
  obtain ⟨e⟩ := hS
  exact alternatingGroup.six_hasInvolutoryB2.of_mulEquiv
    (e.trans Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix)

end CFSG.Quasithin.ChapterI.Section03.KnownSimpleB2
