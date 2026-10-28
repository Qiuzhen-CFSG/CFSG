module

public import Theory.SpecificGroups.PSL3Three.GraphWitnesses.EightCentralizers.Reselection
public import Theory.SpecificGroups.PSL3Three.GraphWitnesses.EightCentralizers.GraphModel
public import Theory.SpecificGroups.PSL3Three.GraphWitnesses.EightCentralizers.NormalFourNormalizer

/-!
# The PSL₃(3) elementary-eight witness

An elementary eight-subgroup contains an outer involution by the inner
two-rank bound. Outer-involution conjugacy moves the whole subgroup to one
containing inverse transpose. Its inner intersection has order four. A
nonnormal intersection supplies a cubic commutator in the graph-fixed S₄;
for a normal intersection, the outer involution is first reselected using
the exact full-normalizer comparison. Transport returns the witness to the
original subgroup, preserving `a c * c⁻¹`.

The native theorem `eight_witness` supplies the actual fixed-group S₄
equivalence and full graph-centralizer splitting from `GraphModel`, and the
ambient normalizer equality from `NormalFourNormalizer`. Its only additional
input is outer-involution conjugacy. The structural assembly is retained as
a separate conditional theorem.

The conclusion is precisely the native input of
`TwelveFixedSpaces.GraphWitnesses.three_witness_of_centerless_model_calculations`.
No representation theory or order-thirteen calculation is used here.

Source: Guralnick--Malle, Classification of 2F-modules I, Proposition 4.2,
manuscript p.10.
-/

public section

open Subgroup
namespace Matrix.PSL3Three.GraphWitnesses.EightCentralizers
open scoped IsMulCommutative
private abbrev graph := Matrix.PSL3.OuterSolvable.graph (ZMod 3)

private theorem center_eq_bot_of_symmetricFour {G : Type*} [Group G]
    (e : G ≃* Equiv.Perm (Fin 4)) : center G = ⊥ := by
  apply eq_bot_iff.mpr
  intro x hx
  apply e.injective
  have he : e x ∈ center (Equiv.Perm (Fin 4)) := by
    rw [mem_center_iff]
    intro y
    obtain ⟨z, rfl⟩ := e.surjective y
    simpa only [← map_mul] using congrArg e (mem_center_iff.mp hx z)
  simpa only [symmetricFour_center_eq_bot, mem_bot, map_one] using he

private noncomputable def fixedEquivOfConjugate (b : MulAut PSL)
    (e : graph.fixedSubgroup ≃* Equiv.Perm (Fin 4))
    (h : ∃ u : MulAut PSL, b = u * graph * u⁻¹) :
    b.fixedSubgroup ≃* Equiv.Perm (Fin 4) := by
  let u := Classical.choose h
  have hu := Classical.choose_spec h
  have he : MulAut.congr u graph = b := by rw [hu]; ext x; rfl
  exact ((MulEquiv.subgroupCongr (congrArg MulAut.fixedSubgroup he).symm).trans
    (MulAut.fixedSubgroupCongr u graph).symm).trans e

theorem eight_witness_of_graph_centralizer_calculations
    (hconj : ∀ b : MulAut PSL, orderOf b = 2 →
      b ∉ MulAut.innerSubgroup PSL → ∃ u : MulAut PSL,
        b = u * Matrix.PSL3.OuterSolvable.graph (ZMod 3) * u⁻¹)
    (e : (Matrix.PSL3.OuterSolvable.graph (ZMod 3)).fixedSubgroup ≃*
      Equiv.Perm (Fin 4))
    (hsplit : ∀ a : MulAut PSL,
      Commute a (Matrix.PSL3.OuterSolvable.graph (ZMod 3)) →
      ∃ x : PSL, a = MulAut.conj x ∨
        a = MulAut.conj x * Matrix.PSL3.OuterSolvable.graph (ZMod 3))
    (hnorm : ∀ D : Subgroup PSL, IsElementaryAbelian 2 D → Nat.card D = 4 →
      D ≤ (Matrix.PSL3.OuterSolvable.graph (ZMod 3)).fixedSubgroup →
      (D.subgroupOf (Matrix.PSL3.OuterSolvable.graph (ZMod 3)).fixedSubgroup).Normal →
      normalizer (D : Set PSL) = (Matrix.PSL3.OuterSolvable.graph (ZMod 3)).fixedSubgroup)
    (B : Subgroup (MulAut PSL)) (hB : IsElementaryAbelian 2 B)
    (hc : Nat.card B = 8) :
    ∃ b ∈ B, b ∉ MulAut.innerSubgroup PSL ∧ ∃ a ∈ B, ∃ c : PSL,
      b c = c ∧ orderOf (a c * c⁻¹) = 3 := by
  apply eight_witness_of_graph_case hconj ?_ B hB hc
  intro B hB hc hgraph
  let : IsElementaryAbelian 2 B := hB
  have hout : graph ∉ MulAut.innerSubgroup PSL := by
    intro hi
    obtain ⟨a, ha, haout⟩ := elementary_eight_has_outer B hB hc
    have hcomm : Commute a graph :=
      congrArg Subtype.val (mul_comm (⟨a, ha⟩ : B) ⟨graph, hgraph⟩)
    obtain ⟨x, hx | hx⟩ := hsplit a hcomm
    · exact haout ⟨x, hx.symm⟩
    · exact haout (hx ▸ (MulAut.innerSubgroup PSL).mul_mem ⟨x, rfl⟩ hi)
  let D := B.comap MulAut.conj
  obtain ⟨hD, hcD, hle⟩ := inner_four B hB hc graph hgraph hsplit
  have hDB : D.map MulAut.conj ≤ B := Subgroup.map_comap_le _ _
  by_cases hn : (D.subgroupOf graph.fixedSubgroup).Normal
  · have hne : D ≠ ⊥ := by
      intro he
      have h := hcD
      change Nat.card D = 4 at h
      have h1 : Nat.card D = 1 := Subgroup.card_eq_one.mpr he
      omega
    obtain ⟨b', hb', ho', hDle', hn'⟩ := reselect_outer hconj B hB graph hgraph hout
      D hle hDB hne (hnorm D hD hcD hle hn) (center_eq_bot_of_symmetricFour e)
    have horder : orderOf b' = 2 := orderOf_eq_prime
      (elemPow_eq_one_of_isElementaryAbelian b' hb')
      (fun h => ho' (h ▸ (MulAut.innerSubgroup PSL).one_mem))
    let e' := fixedEquivOfConjugate b' e (hconj b' horder ho')
    exact ⟨b', hb', ho', cubic_witness_of_nonnormal_four b' e' B D hD hcD hDle' hDB hn'⟩
  · exact ⟨graph, hgraph, hout,
      cubic_witness_of_nonnormal_four graph e B D hD hcD hle hDB hn⟩

/-- Every elementary eight-subgroup has an outer involution whose fixed subgroup
contains an element with cubic displacement under another member of the eight.
Only outer-involution conjugacy remains explicit; the graph centralizer and
full normalizer calculations are supplied on the actual PSL₃(3) model. -/
theorem eight_witness
    (hconj : ∀ b : MulAut PSL, orderOf b = 2 →
      b ∉ MulAut.innerSubgroup PSL → ∃ u : MulAut PSL,
        b = u * Matrix.PSL3.OuterSolvable.graph (ZMod 3) * u⁻¹)
    (B : Subgroup (MulAut PSL)) (hB : IsElementaryAbelian 2 B)
    (hc : Nat.card B = 8) :
    ∃ b ∈ B, b ∉ MulAut.innerSubgroup PSL ∧ ∃ a ∈ B, ∃ c : PSL,
      b c = c ∧ orderOf (a c * c⁻¹) = 3 :=
  eight_witness_of_graph_centralizer_calculations hconj
    GraphModel.graphFixedEquivSymmetricFour GraphModel.graph_centralizer_split
    normalizer_eq_graph_fixed_of_normal_four B hB hc

end Matrix.PSL3Three.GraphWitnesses.EightCentralizers
