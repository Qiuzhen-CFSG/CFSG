module

public import Theory.GroupTheory.SteinerSystem
public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity

/-!
# Invariant Steiner systems from block orbits

Let a group act `t`-transitively on a finite set. Fix a `t`-subset `S` and a
point `p` outside it, and suppose the setwise stabilizer of `S` is transitive
on the points outside `S ∪ {p}`. If the group is not transitive on the
`(t + 1)`-subsets, the orbit of `insert p S` is a Steiner system invariant
under the group.

The key step is uniqueness above `S`: a second orbit block containing `S`
would, by the local transitivity hypothesis, put every extension of `S` in
the same orbit. Multiple transitivity would then put every `(t + 1)`-subset
in that orbit, a contradiction. Transporting uniqueness proves the Steiner
property for every `t`-subset.

The source interfaces are `Theory.GroupTheory.SteinerSystem` for finite
designs and `Mathlib.GroupTheory.GroupAction.MultipleTransitivity` for actions
on ordered tuples. Neither finiteness of the acting group nor an additional
fixed-point hypothesis on the setwise stabilizer is needed.
-/

open scoped Pointwise

namespace Theory.GroupTheory

/-- Multiple transitivity transports unordered subsets of the same size. -/
private theorem exists_smul_finset_eq
    {G α : Type*} [Group G] [MulAction G α] [DecidableEq α]
    {t : ℕ} (htrans : MulAction.IsMultiplyPretransitive G α t)
    (S T : Finset α) (hS : S.card = t) (hT : T.card = t) :
    ∃ g : G, g • S = T := by
  let eS := (Finset.equivFinOfCardEq hS).symm
  let eT := (Finset.equivFinOfCardEq hT).symm
  let x : Fin t ↪ α := eS.toEmbedding.trans (Function.Embedding.subtype _)
  let y : Fin t ↪ α := eT.toEmbedding.trans (Function.Embedding.subtype _)
  obtain ⟨g, hg⟩ := htrans.exists_smul_eq x y
  refine ⟨g, Finset.eq_of_subset_of_card_le ?_ ?_⟩
  · intro b hb
    obtain ⟨a, ha, rfl⟩ := Finset.mem_smul_finset.mp hb
    obtain ⟨i, hi⟩ := eS.surjective ⟨a, ha⟩
    have hgi : g • x i = y i := congrArg (fun z : Fin t ↪ α => z i) hg
    have hxi : x i = a := congrArg Subtype.val hi
    rw [hxi] at hgi
    rw [hgi]
    exact (eT i).property
  · rw [Finset.card_smul_finset, hS, hT]

/-- The orbit of a distinguished extension gives an invariant Steiner system
when the other extensions are locally transitive but all `(t + 1)`-subsets
are not globally transitive. -/
public theorem SteinerSystem.exists_invariant_of_two_extension_orbits
    {G α : Type*} [Group G] [MulAction G α] [Fintype α] [DecidableEq α]
    (t : ℕ) (htrans : MulAction.IsMultiplyPretransitive G α t)
    (hnot : ¬ (∀ B : Finset α, B.card = t + 1 →
      ∀ C : Finset α, C.card = t + 1 → ∃ g : G, g • B = C))
    (S : Finset α) (p : α) (hS : S.card = t) (hp : p ∉ S)
    (hlocal : ∀ q, q ∉ S → q ≠ p → ∀ r, r ∉ S → r ≠ p →
      ∃ g : G, g • S = S ∧ g • q = r) :
    ∃ D : SteinerSystem α t (t + 1), ∀ g : G, MulAction.toPerm g ∈ D.aut := by
  classical
  let B := insert p S
  have hB : B.card = t + 1 := by simp [B, hp, hS]
  -- A second orbit block above `S` would force global transitivity.
  have hbase : ∀ C : Finset α, (∃ g : G, g • B = C) → S ⊆ C → C = B := by
    rintro C ⟨c, hc⟩ hSC
    by_contra hCB
    have hC : C.card = t + 1 := by rw [← hc, Finset.card_smul_finset, hB]
    obtain ⟨q, hqS, hqC⟩ := Finset.exists_eq_insert_iff.mpr ⟨hSC, by rw [hS, hC]⟩
    have hqp : q ≠ p := by
      intro hqp
      apply hCB
      rw [← hqC, hqp]
    have habove : ∀ A : Finset α, A.card = t + 1 → S ⊆ A → ∃ g : G, g • B = A := by
      intro A hA hSA
      obtain ⟨r, hrS, hrA⟩ := Finset.exists_eq_insert_iff.mpr ⟨hSA, by rw [hS, hA]⟩
      by_cases hrp : r = p
      · refine ⟨1, ?_⟩
        simpa [B, hrp] using hrA
      · obtain ⟨g, hgS, hgq⟩ := hlocal q hqS hqp r hrS hrp
        refine ⟨g * c, ?_⟩
        rw [mul_smul, hc, ← hqC, Finset.smul_finset_insert, hgS, hgq, hrA]
    have hall : ∀ A : Finset α, A.card = t + 1 → ∃ g : G, g • B = A := by
      intro A hA
      obtain ⟨T, hTA, hT⟩ := Finset.exists_subset_card_eq (show t ≤ A.card by omega)
      obtain ⟨g, hg⟩ := exists_smul_finset_eq htrans T S hT hS
      obtain ⟨k, hk⟩ := habove (g • A) (by simpa using hA) (by
        rw [← hg]
        exact Finset.smul_finset_subset_smul_finset hTA)
      refine ⟨g⁻¹ * k, ?_⟩
      rw [mul_smul, hk, inv_smul_smul]
    apply hnot
    intro A hA C hC
    obtain ⟨a, ha⟩ := hall A hA
    obtain ⟨c, hc⟩ := hall C hC
    refine ⟨c * a⁻¹, ?_⟩
    rw [← ha, mul_smul, inv_smul_smul, hc]
  let blocks : Finset (Finset α) := Finset.univ.filter (fun C => ∃ g : G, g • B = C)
  have mem_blocks (C : Finset α) : C ∈ blocks ↔ ∃ g : G, g • B = C := by
    simp only [blocks, Finset.mem_filter, Finset.mem_univ, true_and]
  let D : SteinerSystem α t (t + 1) := {
    blocks := blocks
    block_card := by
      intro C hC
      obtain ⟨g, rfl⟩ := (mem_blocks C).mp hC
      simpa using hB
    steiner := by
      intro T hT
      obtain ⟨g, hg⟩ := exists_smul_finset_eq htrans T S hT hS
      apply Finset.card_eq_one_iff_existsUnique.mpr
      refine ⟨g⁻¹ • B, ?_, ?_⟩
      · apply Finset.mem_filter.mpr
        refine ⟨(mem_blocks _).mpr ⟨g⁻¹, rfl⟩, ?_⟩
        apply Finset.subset_smul_finset_iff.mpr
        simp [hg, B]
      · intro C hC
        obtain ⟨hC, hTC⟩ := Finset.mem_filter.mp hC
        obtain ⟨c, hc⟩ := (mem_blocks C).mp hC
        have hgC : g • C = B := hbase (g • C) ⟨g * c, by rw [mul_smul, hc]⟩ (by
          rw [← hg]
          exact Finset.smul_finset_subset_smul_finset hTC)
        rw [← hgC, inv_smul_smul]
  }
  refine ⟨D, ?_⟩
  intro g
  rw [SteinerSystem.mem_aut_iff]
  change (MulAction.toPerm g : Equiv.Perm α) • (blocks : Set (Finset α)) = blocks
  ext C
  constructor
  · intro hC
    obtain ⟨A, hA, hAC⟩ := Set.mem_smul_set.mp hC
    obtain ⟨a, ha⟩ := (mem_blocks A).mp hA
    apply (mem_blocks C).mpr
    refine ⟨g * a, ?_⟩
    change g • A = C at hAC
    rw [mul_smul, ha, hAC]
  · intro hC
    obtain ⟨c, hc⟩ := (mem_blocks C).mp hC
    apply Set.mem_smul_set.mpr
    refine ⟨g⁻¹ • C, (mem_blocks _).mpr ⟨g⁻¹ * c, ?_⟩, ?_⟩
    · rw [mul_smul, hc]
    · change g • (g⁻¹ • C) = C
      exact smul_inv_smul g C

end Theory.GroupTheory
