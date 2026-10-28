module

public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicLine.Complement
public import Mathlib.GroupTheory.Complement

/-!
# A complement to the canonical odd core in the cubic-line normalizer

The source factorization transports to the literal subgroup of N_G(W),
producing an internal complement of order48 to O₂′(N_G(W)) and its exact
index. This is the complement clause of Aschbacher45.8(1),pp245–246.
-/

public section
open Subgroup
namespace Theory.GroupTheory.Recognition.UnitaryFourThree
variable {G:Type*} [Group G] [Finite G] {z:G}
namespace CubicLine
theorem oddCore_isComplement_of_factorization (W K:Subgroup G)
    (hK:K≤normalizer (W:Set G)) (hdis:Disjoint (oddKernel W) K)
    (hgen:normalizer (W:Set G)=oddKernel W⊔K) :
    (pPrimeCore 2 (normalizer (W:Set G))).IsComplement' (K.subgroupOf (normalizer (W:Set G))) := by
  let N:=normalizer (W:Set G)
  apply isComplement'_of_card_mul_and_disjoint
  · have hc:=card_sup_eq_mul_of_normalizes_of_disjoint (oddKernel W) K
      (hK.trans (normalizer_normalizes_oddKernel W)) hdis
    rw [←hgen] at hc
    change Nat.card N=Nat.card ((pPrimeCore 2 N).map N.subtype)*Nat.card K at hc
    rw [card_map_of_injective N.subtype_injective] at hc
    rw [Nat.card_congr (subgroupOfEquivOfLe hK).toEquiv]
    exact hc.symm
  · rw [Subgroup.disjoint_def]
    intro x hx hy
    apply Subtype.ext
    exact Subgroup.disjoint_def.mp hdis (show (x:G)∈oddKernel W from ⟨x,hx,rfl⟩) hy
end CubicLine
namespace IsType
variable (h:IsType z)
include h in
theorem original_cubic_line_internal_complement (P:Sylow 3 (centralizer z)) :
    ∃W:Subgroup G, Nat.card W=3 ∧ W≤(P:Subgroup (centralizer z)).map (centralizer z).subtype ∧
      ∃K:Subgroup (normalizer (W:Set G)), Nat.card K=48 ∧
      (pPrimeCore 2 (normalizer (W:Set G))).IsComplement' K ∧
      (pPrimeCore 2 (normalizer (W:Set G))).index=48 := by
  obtain ⟨W,J,K,hW,hWX,_,_,_,hK,hKN,_,_,hg,hd⟩:=h.original_cubic_line_complement P
  have hc:=CubicLine.oddCore_isComplement_of_factorization W K (hKN.trans inf_le_right) hd hg
  have hcard:Nat.card (K.subgroupOf (normalizer (W:Set G)))=48:=
    (Nat.card_congr (subgroupOfEquivOfLe (hKN.trans inf_le_right)).toEquiv).trans hK
  exact ⟨W,hW,hWX,_,hcard,hc,hc.symm.index_eq_card.trans hcard⟩
end IsType
end Theory.GroupTheory.Recognition.UnitaryFourThree
