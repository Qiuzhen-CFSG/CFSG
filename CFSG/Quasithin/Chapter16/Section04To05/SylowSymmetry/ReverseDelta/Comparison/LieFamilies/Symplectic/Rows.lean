module

public import CFSG.Quasithin.Chapter16.Section01To02.LiePreliminaries.SymplecticFour
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.FieldFixedResidual
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.GraphFieldFixedResidual

/-!
# The symplectic involution rows consumed by the residual comparison

These are explicit earlier-table inputs, not assertions of the table. Root
and c₂ rows concern actual matrix conjugation. The root residual is
identified with an actual point or plane determinant kernel. Outer rows retain
intertwining automorphisms with the field and graph-field representatives.
The binary rows act on the derived carrier, allowing root elements of the
full Sp₄(2), and distinguish A₄ from the cyclic group Sz(2)′ of order five.

No row asserts a comparison between two residuals or its impossibility.
Source: Aschbacher–Smith, 16.1.3–4, printed pp.1170–1171; the consumer is
16.4.11(2), printed p.1193, in the combined 1 March 2004 manuscript.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.Intersections.SylowSymmetry.ReverseDelta.Comparison.LieFamilies
open Subgroup Theory.SpecificGroups.SymplecticFour
open DiagramAutomorphisms DiagramAutomorphisms.GraphFieldFixedResidual
open BenderSuzuki.MatrixGroups

/-- Exact consumed centralizer and conjugacy data over a nonbinary field. -/
structure SymplecticInvolutionRows (F : Type*) [Field F] [Finite F] [CharP F 2]
    (n : ℕ) : Prop where
  inner : ∀ a : MulAut (Sp F), orderOf a = 2 → (∃ x, a = MulAut.conj x) →
    ∃ x : Sp F, orderOf x = 2 ∧ a = MulAut.conj x ∧
      ((InvolutionTypes.IsRootElement x ∧
        (Nonempty (pResidual 2 a.fixedSubgroup ≃* pointLocal (F := F)) ∨
         Nonempty (pResidual 2 a.fixedSubgroup ≃* planeLocal (F := F)))) ∨
       (InvolutionTypes.IsC2 x ∧ IsPGroup 2 a.fixedSubgroup))
  outer : ∀ a : MulAut (Sp F), orderOf a = 2 → (¬ ∃ x, a = MulAut.conj x) →
    (∃ m : ℕ, 1 ≤ m ∧ n = 2 * m ∧ ∃ c : MulAut (Sp F),
      ∀ x, c (a x) = FieldFixedResidual.representative m (c x)) ∨
    (∃ m : ℕ, n = 2 * m + 1 ∧ ∃ c : MulAut (Sp F),
      (∀ x, c (a x) = graphFieldAut m (c x)) ∧
      Nonempty ((graphFieldAut (F := F) m).fixedSubgroup ≃* SuzukiMatrixGroup m))

/-- The earlier nonbinary table at every field witness; the family assembly
must discharge this input before asserting the source theorem. -/
def SymplecticInvolutionTable : Prop :=
  ∀ (F : Type) [Field F] [Finite F] [CharP F 2] (n : ℕ),
    2 ≤ n → Nat.card F = 2 ^ n → SymplecticInvolutionRows F n

/-- The binary rows use the derived group itself and actions from the full
symplectic group. The last equivalence is the actual Sz(2)′ endpoint. -/
structure BinarySymplecticInvolutionRows : Prop where
  inner : ∀ a : MulAut (commutator (Sp (ZMod 2))), orderOf a = 2 →
    (∃ x, a = MulAut.conj x) →
    ∃ x : commutator (Sp (ZMod 2)), a = MulAut.conj x ∧
      InvolutionTypes.IsC2 x.val ∧ IsPGroup 2 a.fixedSubgroup
  outer : ∀ a : MulAut (commutator (Sp (ZMod 2))), orderOf a = 2 →
    (¬ ∃ x, a = MulAut.conj x) →
    (∃ x : Sp (ZMod 2), InvolutionTypes.IsRootElement x ∧
      a = MulAut.conjNormal (H := commutator (Sp (ZMod 2))) x ∧
      Nonempty (pResidual 2 a.fixedSubgroup ≃* alternatingGroup (Fin 4))) ∨
    ((∃ c : MulAut (commutator (Sp (ZMod 2))),
      ∀ x, c (a x) = derivedGraphFieldAut 0 (c x)) ∧
      Nonempty (pResidual 2 a.fixedSubgroup ≃* Multiplicative (ZMod 5)))

end CFSG.Quasithin.Chapter16.Intersections.SylowSymmetry.ReverseDelta.Comparison.LieFamilies
