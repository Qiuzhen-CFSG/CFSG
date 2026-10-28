module

public import Theory.Mathieu.M24.Basic
public import Theory.Mathieu.M24.Properties.GolayModule

/-!
# Recognizing native M₂₄ elements from Golay row images

The binary code is closed under xor. Thus checking the twelve generating
rows suffices to show that a coordinate permutation preserves every codeword.
It then preserves all weight-eight words, which are precisely the native
Witt octads. This criterion is used to certify the affine trio generators.

Source: Aschbacher, *Sporadic Groups*, Chapter 7, §§18–20.
-/

@[expose] public section

open scoped Pointwise
namespace Sporadic.Mathieu.M24LocalGeometry.PairOvergroups.QuotientConstruction.AffineLiftConstruction

private theorem code_image_of_rows (g : Equiv.Perm (Fin 24))
    (h : ∀ i, ∃ u, m24PermuteMask g (m24GolayRow i) = m24GolayCode u)
    (u : Fin 4096) : ∃ v, m24PermuteMask g (m24GolayCode u) = m24GolayCode v := by
  have hx {x y : BitVec 24}
      (hx : ∃ u, x = m24GolayCode u) (hy : ∃ u, y = m24GolayCode u) :
      ∃ u, x ^^^ y = m24GolayCode u := by
    obtain ⟨u, rfl⟩ := hx
    obtain ⟨v, rfl⟩ := hy
    exact ⟨m24GolayMessageXor u v, (m24GolayCode_xor u v).symm⟩
  have hs (b : Bool) (i : Fin 12) :
      ∃ v, m24PermuteMask g (m24GolaySelect b (m24GolayRow i)) = m24GolayCode v := by
    cases b
    · exact ⟨0, (m24PermuteMask_zero g).trans m24GolayCode_zero.symm⟩
    · exact h i
  unfold m24GolayCode
  simp only [m24PermuteMask_xor]
  repeat first | apply hx | exact hs _ _

/-- Code membership of the twelve row images certifies native M₂₄ membership. -/
theorem mem_M24_of_rows (g : Equiv.Perm (Fin 24))
    (h : ∀ i, ∃ u, m24PermuteMask g (m24GolayRow i) = m24GolayCode u) :
    g ∈ M24 := by
  have hw (u : Fin 4096) : ∃ v, g • m24GolayWord u = m24GolayWord v := by
    obtain ⟨v, hv⟩ := code_image_of_rows g h u
    refine ⟨v, ?_⟩
    ext x
    rw [← Finset.inv_smul_mem_iff]
    simp only [m24GolayWord, Finset.mem_filter, Finset.mem_univ, true_and,
      Equiv.Perm.smul_def, Equiv.Perm.inv_def]
    rw [← hv]
    simp [m24PermuteMask]
  have hb : g • m24Blocks ⊆ m24Blocks := by
    intro B hB
    obtain ⟨A, hA, rfl⟩ := Finset.mem_smul_finset.mp hB
    rw [m24Blocks] at hA
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hA
    rw [m24BlockAt_eq_m24GolayWord]
    obtain ⟨v, hv⟩ := hw (m24BlockMessage i)
    rw [hv]
    apply m24GolayWord_mem_blocks_of_card_eq_eight
    rw [← hv, Finset.card_smul_finset, ← m24BlockAt_eq_m24GolayWord]
    exact m24BlockAt_card i
  have he : g • m24Blocks = m24Blocks :=
    Finset.eq_of_subset_of_card_le hb (Finset.card_smul_finset g m24Blocks).ge
  apply (mem_M24_iff g).mpr
  simpa only [Finset.coe_smul_finset] using
    congrArg (fun s : Finset (Finset (Fin 24)) => (s : Set (Finset (Fin 24)))) he

end Sporadic.Mathieu.M24LocalGeometry.PairOvergroups.QuotientConstruction.AffineLiftConstruction
