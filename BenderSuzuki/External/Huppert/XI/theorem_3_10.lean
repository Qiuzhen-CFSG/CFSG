module

public import Theory.SpecificGroups.Suzuki.NonsplitTori

/-!
# Huppert--Blackburn XI.3.10: Suzuki tori and their normalizers

For `q = 2^(2m+1)` and `r = 2^m`, the two nonsplit tori have orders
`q + 2r + 1` and `q - 2r + 1`. They are cyclic Hall subgroups and are the
centralizers of their nonidentity elements. Each normalizer has a cyclic
quotient and a cyclic complement of order four; a complement generator acts
by right conjugation as the `q`th power map. The root group, split torus,
and these two tori give the subgroup partition.

The reusable proofs are in `Theory.SpecificGroups.Suzuki`: the ovoid action
gives the root and split-torus geometry, the linear representation gives
cyclic nonsplit subgroups, and the partition count determines the two orders.
This module assembles their conclusions and the dihedral split normalizer.
It also re-exports the concrete root, split-torus and Borel subgroups and
their coordinate, order, Sylow and normalizer interfaces.

Source: Huppert--Blackburn, *Finite Groups III*, XI.3.10, printed pp. 190--193;
the split normalizer is also recorded in XI.3.12(e). No subgroup
classification is used.
-/

namespace BenderSuzuki.External

open BenderSuzuki.MatrixGroups

/-- The torus, normalizer and partition assertions of XI.3.10, together with
the dihedral split-torus normalizer. The plus torus is `U₁` and the minus
torus is `U₂`. The complement action uses the source's right-conjugation
convention `uᵗ = t⁻¹ * u * t`.

The partition assertion means that each nonidentity element belongs to
exactly one subgroup among the conjugates of the four displayed subgroups.
-/
public theorem huppert_blackburn_XI_3_10 (m : ℕ) (hm : 0 < m) :
    let q := 2 ^ (2 * m + 1)
    let r := 2 ^ m
    ∃ U₁ U₂ : Subgroup (SuzukiMatrixGroup m),
      Nat.card U₁ = q + 2 * r + 1 ∧
      Nat.card U₂ = q - 2 * r + 1 ∧
      (∀ U ∈ ({U₁, U₂} : Set (Subgroup (SuzukiMatrixGroup m))),
        IsCyclic U ∧ Nat.Coprime (Nat.card U) U.index ∧
        (∀ u ∈ U, u ≠ 1 → Subgroup.centralizer {u} = U) ∧
        IsCyclic ((Subgroup.normalizer (U : Set (SuzukiMatrixGroup m))) ⧸
          U.subgroupOf (Subgroup.normalizer (U : Set (SuzukiMatrixGroup m)))) ∧
        Nat.card ((Subgroup.normalizer (U : Set (SuzukiMatrixGroup m))) ⧸
          U.subgroupOf (Subgroup.normalizer (U : Set (SuzukiMatrixGroup m)))) = 4 ∧
        ∃ t : SuzukiMatrixGroup m,
          orderOf t = 4 ∧
          t ∈ Subgroup.normalizer (U : Set (SuzukiMatrixGroup m)) ∧
          U ⊔ Subgroup.zpowers t = Subgroup.normalizer (U : Set (SuzukiMatrixGroup m)) ∧
          Disjoint U (Subgroup.zpowers t) ∧
          ∀ u ∈ U, t⁻¹ * u * t = u ^ q) ∧
      (∀ x : SuzukiMatrixGroup m, x ≠ 1 →
        ∃! U : Subgroup (SuzukiMatrixGroup m),
          ((∃ g, U = (SuzukiRootSubgroup m).map (MulAut.conj g).toMonoidHom) ∨
            (∃ g, U = (SuzukiSplitTorus m).map (MulAut.conj g).toMonoidHom) ∨
            (∃ g, U = U₁.map (MulAut.conj g).toMonoidHom) ∨
            (∃ g, U = U₂.map (MulAut.conj g).toMonoidHom)) ∧ x ∈ U) ∧
      Nonempty (Subgroup.normalizer (SuzukiSplitTorus m : Set (SuzukiMatrixGroup m)) ≃*
        DihedralGroup (q - 1)) := by
  obtain ⟨T⟩ := exists_suzukiNonsplitTorusPair m hm
  refine ⟨T.plus, T.minus, T.plus_card, T.minus_card, ?_,
    T.partition_existsUnique hm, suzukiSplitTorus_normalizer_dihedral m hm⟩
  intro U hU
  have hmax : IsSuzukiMaximalNonsplit m U := by
    rcases Set.mem_insert_iff.mp hU with rfl | hU
    · exact T.plus_maximal
    · rw [Set.mem_singleton_iff.mp hU]
      exact T.minus_maximal
  exact ⟨hmax.isCyclic hm, hmax.card_coprime_index hm,
    fun _ hu hne => hmax.centralizer_eq hm hu hne,
    (hmax.normalizer_quotient_order_four hm).1,
    (hmax.normalizer_quotient_order_four hm).2,
    hmax.normalizer_complement hm⟩

end BenderSuzuki.External
