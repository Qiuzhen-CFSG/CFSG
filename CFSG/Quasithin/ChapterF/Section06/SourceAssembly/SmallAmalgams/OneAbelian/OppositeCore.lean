module
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.OneAbelian.Vertex
public import Theory.GroupTheory.WreathedThirtyTwoVertex.SourceCore
/-!
# The original opposite vertex and its quaternion–cyclic core

The source common Sylow has order thirty-two and its abelian endpoint
identifies it with C₄ wreath C₂. The opposite endpoint has order 96 and
nonabelian two-core of order sixteen: two abelian cores would force overlap
order at most sixteen. The genuine wreathed centric-core theorem therefore
identifies the original opposite core with Q₈ ◦ C₄.

Source: Aschbacher–Smith F.1.12(I)(8), printed p.263, using ABG II.1 Lemma 3.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.SourceAssembly.OneAbelian
variable {G : Type*} [Group G] [Finite G] {A B : Subgroup G}
/-- All isolated recognition hypotheses hold for the unchanged opposite vertex. -/
theorem opposite_vertex_parameters
    (h : IsGoldschmidtTriple A B) (hcore : pCore 2 G=⊥)
    (hA : generalizedFitting A=pCore 2 A) (hB : generalizedFitting B=pCore 2 B)
    [IsMulCommutative (pCore 2 A)]
    (S : Sylow 2 G) (hS : A⊓B=(S : Subgroup G)) (hlarge : 8<Nat.card S)
    (hns : ¬ Nonempty (S≃*Multiplicative (ZMod 2)×DihedralGroup 4)) :
    Nat.card B=96 ∧ Nat.card (pCore 2 B)=16 ∧ ¬IsMulCommutative (pCore 2 B) ∧
      Nonempty ((S.subtype (hS.symm.le.trans inf_le_right))≃*WreathedThirtyTwo) := by
  have hs := remaining_source_card_thirty_two h hcore hA hB S hS hlarge hns
  have hb : Nat.card B=96 := by
    rw [h.symm.local_card_eq_three_mul_intersection,inf_comm B A,hS,hs]
  have hq : Nat.card (pCore 2 B)=16 := by
    have hh := SymmetricThreeTwoCore.card_eq h.quotient_right.some
    omega
  have hn : ¬IsMulCommutative (pCore 2 B) := by
    intro he
    let := he
    have hh := BothAbelian.intersection_card_le_sixteen h hcore hA hB
    rw [hS,hs] at hh
    omega
  obtain ⟨e⟩ := common_sylow_wreathed h hcore hA hB S hS hlarge hns
  exact ⟨hb,hq,hn,⟨(subgroupOfEquivOfLe (hS.symm.le.trans inf_le_right)).trans e⟩⟩

/-- The actual opposite two-core, without any model premise. -/
theorem opposite_core_quaternion_cyclic
    (h : IsGoldschmidtTriple A B) (hcore : pCore 2 G=⊥)
    (hA : generalizedFitting A=pCore 2 A) (hB : generalizedFitting B=pCore 2 B)
    [IsMulCommutative (pCore 2 A)]
    (S : Sylow 2 G) (hS : A⊓B=(S : Subgroup G)) (hlarge : 8<Nat.card S)
    (hns : ¬ Nonempty (S≃*Multiplicative (ZMod 2)×DihedralGroup 4)) :
    Nonempty (pCore 2 B≃*QuaternionCyclic.Model) := by
  obtain ⟨hb,_,hn,⟨e⟩⟩ := opposite_vertex_parameters h hcore hA hB S hS hlarge hns
  exact WreathedVertex.twoCore_equiv_of_card96 hb (h.symm.local_core_selfCentralizing hB)
    hn (S.subtype (hS.symm.le.trans inf_le_right)) e
end CFSG.Quasithin.ChapterF.SourceAssembly.OneAbelian
