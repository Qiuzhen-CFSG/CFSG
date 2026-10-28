module
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.OneAbelian.CoreModels
public import Theory.GroupTheory.C4SquareSymmetricThreeSplit
/-!
# An actual cubic-normalizer complement in the one-abelian source vertex

The faithful Goldschmidt hypotheses give common Sylow order thirty-two
and identify the abelian core with C₄ × C₄. Its cubic normalizer is a
complement, identified with the original symmetric-three quotient.
Thus no split-extension premise is added to the local recognition.

Source: Aschbacher–Smith F.1.12(I)(8), printed p.263.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.SourceAssembly.OneAbelian
variable {G : Type*} [Group G] [Finite G] {A B : Subgroup G}
/-- Splitting on the literal original abelian-core vertex. -/
theorem source_cubic_normalizer_complement
    (h : IsGoldschmidtTriple A B) (hcore : pCore 2 G=⊥)
    (hA : generalizedFitting A=pCore 2 A) (hB : generalizedFitting B=pCore 2 B)
    [IsMulCommutative (pCore 2 A)]
    (S : Sylow 2 G) (hS : A⊓B=(S : Subgroup G)) (hlarge : 8<Nat.card S)
    (hns : ¬ Nonempty (S≃*Multiplicative (ZMod 2)×DihedralGroup 4)) :
    ∃c : A, orderOf c=3 ∧
      (pCore 2 A).IsComplement' (normalizer (zpowers c : Set A)) ∧
      Nonempty (normalizer (zpowers c : Set A) ≃* Equiv.Perm (Fin 3)) := by
  obtain ⟨e⟩ := abelian_core_equiv_c4_square h hcore hA hB S hS hlarge hns
  have hQ : Nat.card (pCore 2 A)=16 := by
    rw [Nat.card_congr e.toEquiv,Nat.card_eq_fintype_card]
    decide
  have hc : Nat.card A=96 := by
    rw [SymmetricThreeTwoCore.card_eq h.quotient_left.some,hQ]
  exact C4SquareExtension.exists_symmetric_three_complement (pCore 2 A) e hc
    (h.local_core_selfCentralizing hA) h.quotient_left.some
end CFSG.Quasithin.ChapterF.SourceAssembly.OneAbelian
