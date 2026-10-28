module

public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Configuration.Marked
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Action
public import Theory.Representation.BinaryOffender.SubspaceAction

/-!
# The remaining source conditions of the pre-B.4 configuration

Condition (ii) uses the embedded preimage of O₃(C/O₂(C)), not the join
of the two prime cores. Condition (iii) is expressed on the faithful
`Action.starRepresentation` and its literal `Action.seedSpace`: the seed,
not the entire module, has binary dimension two. Condition (iv) requires
actual symmetric-three isomorphisms for the pairs in X̂. The universal
quantifier permits left conjugates, by inversion of the book's conjugator.

These predicates are specifications, not asserted source theorems.
Source: Aschbacher–Smith, combined manuscript, 13.5.21, printed p.923
(PDF p.940), conditions (ii)–(iv).
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Configuration
open Section08.Source
variable {G : Type*} [Group G] [Finite G]
  {D : ChapterF.Section09.Setup G} {K : Subgroup G}

/-- The source O₂,₃(C), embedded in its original ambient group. -/
def twoThreeCore {A : Type*} [Group A] [Finite A] (C : Subgroup A) : Subgroup A :=
  ((pCore 3 (C ⧸ pCore 2 C)).comap (QuotientGroup.mk' (pCore 2 C))).map C.subtype

/-- The two commutator equalities and the dimension in source condition (iii). -/
def ModuleConditions (D : ChapterF.Section09.Setup G) (h : D.Hypothesis) : Prop :=
  letI := Action.point_normal D h
  letI := Action.quotient_elementary D h
  Representation.BinaryOffender.subspaceCommutator (Action.starRepresentation D h)
      ⊤ (starImage D.H D.V) = Action.seedSpace D ∧
    Representation.BinaryOffender.subspaceCommutator (Action.starRepresentation D h)
      (Action.seedSpace D) (starImage D.H D.L₁) = Action.seedSpace D ∧
    Module.finrank (ZMod 2) (Action.seedSpace D) = 2

variable (s : Selected D K) (h : D.Hypothesis)
  [(componentCentralizer s h).Normal]

/-- The remaining inclusion in condition (ii). -/
def LocalCoreCondition : Prop :=
  L1hat s h ≤ twoThreeCore (centralizer (Vhat s h : Set (Xhat s h)))

/-- The actual two-conjugate subgroup of X̂, with left conjugation. -/
def markedPair (x : Xhat s h) : Subgroup (Xhat s h) :=
  Vhat s h ⊔ (Vhat s h).map (MulAut.conj x).toMonoidHom

/-- Source condition (iv), with a genuine S₃ isomorphism. -/
def PairCondition : Prop :=
  ∀ x : Xhat s h, ¬ IsPGroup 2 (markedPair s h x) →
    Nonempty (markedPair s h x ≃* Equiv.Perm (Fin 3))

end CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Configuration
end
