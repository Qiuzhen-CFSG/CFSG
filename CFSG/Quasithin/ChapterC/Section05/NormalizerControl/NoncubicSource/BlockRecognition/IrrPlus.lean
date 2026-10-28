module
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.BlockRecognition.Displacement
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.DualOffender.MovedFixed
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.AlternatingSevenMaximal.Basic
public import Theory.Representation.BinaryOffender.AlternatingSevenIrrPlus.FullMoved

/-!
# Irr⁺ on the actual source moved representation

Reducedness proves faithfulness on I, while the original full commutator
identity proves that its dual has no fixed vectors. A five-element in the
actual K-image lifts to the given group and its displacement lies in U.
The strict-eight bound then forces irreducibility modulo fixed vectors.
The full central cover remains present throughout.
Source: Aschbacher–Smith C.5.13, p.163.
-/
public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl.DualOffender
open Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G]

theorem moved_isIrrPlus_of_reduced (V K U : Subgroup G)
    [V.Normal] [IsElementaryAbelian 2 V]
    (hV : Theory.GroupTheory.IsPReduced 2 V)
    (hcomm : ⁅V,K⁆ ≤ U) (hU : Nat.log 2 (Nat.card U) < 8)
    (hfive : 5 ∣ Nat.card (K.map (QuotientGroup.mk' (centralizer (V : Set G)))))
    (hmodel : IsAlternating (closureImage V K) 7)
    (hfix : fixedSpace (movedRepresentation V K).dual ⊤ = ⊥) :
    IsIrrPlus (movedRepresentation V K) ⊤ ⊤ := by
  let q := QuotientGroup.mk' (centralizer (V : Set G))
  let B := K.map q
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨b,hb⟩ := exists_prime_orderOf_dvd_card' (G := B) 5 hfive
  obtain ⟨k,hk,he⟩ := b.property
  let a : closureImage V K := ⟨q k,mem_map_of_mem _ (le_normalClosure hk)⟩
  have ha : orderOf a = 5 := by
    rw [← orderOf_coe a]
    change orderOf (q k) = 5
    rw [he]
    exact (orderOf_coe b).trans hb
  let : IsSimpleGroup (closureImage V K) :=
    EmbeddingSelection.AlternatingSevenMaximal.simple_of_model hmodel
  apply isIrrPlus_top_of_five_displacement _ (moved_faithful_of_reduced V K hV).1
    (subspaceCommutator_top_eq_top_of_dual_fixed _ hfix) a ha
  exact lt_of_le_of_lt (moved_displacement_le_card V K U hcomm k hk) hU
end CFSG.Quasithin.ChapterC.Section05.NormalizerControl.DualOffender
