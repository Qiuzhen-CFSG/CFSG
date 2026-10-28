module
public import Theory.GroupTheory.AmalgamGraph.LocalAction
public import Theory.GroupTheory.WeakBNPair.RegularTree.ApartmentPaths
public import Mathlib.GroupTheory.PGroup

/-!
# Paths fixed by the actual order-seven Cartan

In a coset graph of valences three and nine, an order-seven subgroup fixing
a vertex fixes at least two of its neighbors. The orbit congruence gives
three fixed neighbors at a cubic vertex and at least two at a nine-valent
vertex. In the universal tree this extends any fixed edge to arbitrarily
long fixed paths, without assuming reflection lifts in advance.
-/

public noncomputable section
open Subgroup SimpleGraph
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
namespace Theory.GroupTheory.WeakBNPair.RegularTree
variable {X : Type*} [Group X] (F : Bool → Subgroup X)

/-- The fixed vertices of an actual order-seven subgroup have at least two
fixed neighbors at every vertex when both valences are three or nine. -/
theorem seven_fixed_twoNeighbors (C : Subgroup X) (hC : Nat.card C = 7)
    (hval : ∀ v : Vertex F,
      Nat.card ((graph F).neighborSet v) = 3 ∨ Nat.card ((graph F).neighborSet v) = 9) :
    TwoNeighborsIn (graph F) {v | ∀ c ∈ C, c • v = v} := by
  intro v hv
  have hCv : C ≤ stabilizer F v := hv
  let a := (localAction F v).comp (inclusion hCv)
  let : MulAction C ((graph F).neighborSet v) := MulAction.compHom _ a
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  let : Finite C := Nat.finite_of_card_ne_zero (by rw [hC]; decide)
  let : Finite ((graph F).neighborSet v) := Nat.finite_of_card_ne_zero (by
    rcases hval v with hh | hh <;> rw [hh] <;> decide)
  have hp : IsPGroup 7 C := IsPGroup.of_card (n := 1) (by simpa using hC)
  have hm := hp.card_modEq_card_fixedPoints ((graph F).neighborSet v)
  have ht : 1 < Nat.card (MulAction.fixedPoints C ((graph F).neighborSet v)) := by
    have hc := hval v
    change Nat.card ((graph F).neighborSet v) % 7 =
      Nat.card (MulAction.fixedPoints C ((graph F).neighborSet v)) % 7 at hm
    omega
  let : Nontrivial (MulAction.fixedPoints C ((graph F).neighborSet v)) :=
    Finite.one_lt_card_iff_nontrivial.mp ht
  obtain ⟨b,d,hbd⟩ := exists_pair_ne (MulAction.fixedPoints C ((graph F).neighborSet v))
  have hb (c : X) (hc : c ∈ C) : c • b.val.val = b.val.val :=
    congrArg Subtype.val (b.property (⟨c,hc⟩ : C))
  have hd (c : X) (hc : c ∈ C) : c • d.val.val = d.val.val :=
    congrArg Subtype.val (d.property (⟨c,hc⟩ : C))
  refine ⟨b.val.val,hb,d.val.val,hd,b.val.property,d.val.property,?_⟩
  exact fun he => hbd (Subtype.ext (Subtype.ext he))

/-- A fixed original edge in the universal tree extends to any prescribed
length while retaining the same order-seven subgroup pointwise. -/
theorem seven_fixed_edge_path (C : Subgroup X) (hC : Nat.card C = 7)
    (hval : ∀ v : Vertex F,
      Nat.card ((graph F).neighborSet v) = 3 ∨ Nat.card ((graph F).neighborSet v) = 9)
    (htree : (graph F).IsAcyclic) {v w : Vertex F} (hvw : (graph F).Adj v w)
    (hCv : ∀ c ∈ C, c • v = v) (hCw : ∀ c ∈ C, c • w = w)
    (n : ℕ) (hn : 0 < n) :
    ∃ z, ∃ p : (graph F).Walk v z, p.IsPath ∧ p.length = n ∧
      (∀ y ∈ p.support, ∀ c ∈ C, c • y = y) ∧ p.getVert 1 = w := by
  let p : (graph F).Walk v w := .cons hvw .nil
  have hp : p.IsPath := by simpa [p] using hvw.ne
  have hfix : ∀ y ∈ p.support, y ∈ {v : Vertex F | ∀ c ∈ C, c • v = v} := by
    intro y hy
    simp only [p,Walk.support_cons,Walk.support_nil,List.mem_cons,List.not_mem_nil,or_false] at hy
    rcases hy with rfl | rfl
    · exact hCv
    · exact hCw
  exact path_extension_in_set htree (seven_fixed_twoNeighbors F C hC hval) p hp hfix
    (show p.length ≤ n by simp only [p,Walk.length_cons,Walk.length_nil]; omega)

end Theory.GroupTheory.WeakBNPair.RegularTree
