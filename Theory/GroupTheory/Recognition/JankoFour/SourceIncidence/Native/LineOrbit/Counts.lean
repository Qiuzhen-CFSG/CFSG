module
public import Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.Native.LineOrbit.Data
public import Mathlib.Data.Fintype.BigOperators
/-!
# Valencies from bounded counts of the existing catalogue

The colour fibre is equivalent to the disjoint union of its 64-entry blocks.
Small kernel-checked block counts sum to the five source valencies; the last
block retains only its nineteen actual entries. The proof does not repeat
large reductions on the full 3795-element finite type.

Source: AS91 (3.4), (5.4), pp.594,600.
-/
public section
set_option Elab.async false
open scoped Matrix BigOperators
namespace Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.NativeLineOrbit
private def counts : Fin 60 → Fin 5 → ℕ :=
  ![![0, 0, 0, 13, 51],
    ![0, 1, 2, 23, 38],
    ![0, 0, 0, 11, 53],
    ![0, 1, 2, 22, 39],
    ![0, 1, 2, 23, 38],
    ![0, 1, 2, 16, 45],
    ![0, 0, 0, 17, 47],
    ![0, 0, 0, 14, 50],
    ![0, 1, 2, 20, 41],
    ![0, 0, 0, 15, 49],
    ![0, 0, 0, 12, 52],
    ![0, 0, 0, 12, 52],
    ![0, 0, 0, 13, 51],
    ![0, 0, 0, 13, 51],
    ![0, 0, 0, 13, 51],
    ![0, 0, 0, 12, 52],
    ![0, 2, 2, 28, 32],
    ![0, 0, 2, 16, 46],
    ![0, 1, 2, 22, 39],
    ![0, 0, 0, 14, 50],
    ![0, 0, 0, 14, 50],
    ![0, 1, 2, 20, 41],
    ![0, 1, 2, 22, 39],
    ![0, 1, 2, 21, 40],
    ![0, 0, 0, 14, 50],
    ![0, 0, 0, 14, 50],
    ![0, 2, 4, 28, 30],
    ![0, 0, 0, 12, 52],
    ![0, 0, 0, 13, 51],
    ![0, 0, 0, 14, 50],
    ![0, 0, 0, 11, 53],
    ![0, 1, 1, 20, 42],
    ![0, 1, 1, 18, 44],
    ![0, 0, 0, 12, 52],
    ![0, 2, 2, 28, 32],
    ![0, 2, 4, 25, 33],
    ![0, 0, 0, 14, 50],
    ![0, 0, 0, 13, 51],
    ![0, 0, 0, 16, 48],
    ![0, 0, 0, 9, 55],
    ![1, 12, 1, 15, 35],
    ![0, 1, 1, 17, 45],
    ![0, 0, 0, 13, 51],
    ![0, 1, 0, 18, 45],
    ![0, 1, 4, 21, 38],
    ![0, 0, 4, 17, 43],
    ![0, 0, 0, 8, 56],
    ![0, 0, 0, 12, 52],
    ![0, 0, 0, 21, 43],
    ![0, 5, 0, 19, 40],
    ![0, 3, 0, 24, 37],
    ![0, 0, 0, 15, 49],
    ![0, 0, 4, 18, 42],
    ![0, 0, 0, 23, 41],
    ![0, 0, 0, 14, 50],
    ![0, 0, 0, 10, 54],
    ![0, 0, 4, 18, 42],
    ![0, 0, 2, 30, 32],
    ![0, 0, 2, 18, 44],
    ![0, 0, 0, 10, 9]]

private abbrev chunk (k : Fin 60) (r : Fin 5) :=
  {j : Fin 64 // 64*k.val+j.val < 3795 ∧ (blocks k j).root = r}

private def chunkEquiv (r : Fin 5) :
    {i : Fin 3795 // (node i).root = r} ≃ Σ k : Fin 60, chunk k r where
  toFun i := ⟨⟨i.val.val / 64,by omega⟩,⟨⟨i.val.val % 64,by omega⟩,
    by dsimp; have := i.val.isLt; omega,by simpa only [node] using i.property⟩⟩
  invFun p := ⟨⟨64*p.1.val+p.2.val.val,p.2.property.1⟩,by
    change (blocks ⟨(64*p.1.val+p.2.val.val)/64,_⟩
      ⟨(64*p.1.val+p.2.val.val)%64,_⟩).root = r
    have hq : (⟨(64*p.1.val+p.2.val.val)/64,by omega⟩ : Fin 60) = p.1 := by
      apply Fin.ext; dsimp; have := p.2.val.isLt; omega
    have hr : (⟨(64*p.1.val+p.2.val.val)%64,by omega⟩ : Fin 64) = p.2.val := by
      apply Fin.ext; dsimp; have := p.2.val.isLt; omega
    rw [hq,hr]
    exact p.2.property.2⟩
  left_inv i := by apply Subtype.ext; apply Fin.ext; dsimp; omega
  right_inv p := by
    rcases p with ⟨k,j,hj⟩
    have hq : (⟨(64*k.val+j.val)/64,by omega⟩ : Fin 60) = k := by
      apply Fin.ext; dsimp; omega
    apply Sigma.ext hq
    apply (Subtype.heq_iff_coe_eq (fun n => by dsimp; rw [hq]; have hv := congrArg Fin.val hq; dsimp at hv; rw [hv])).mpr
    apply Fin.ext
    dsimp
    omega

private theorem count00 : ∀ r : Fin 5, Fintype.card (chunk 0 r) = counts 0 r := by
  intro r
  rw [Fintype.card_subtype]
  revert r
  decide +kernel

private theorem count01 : ∀ r : Fin 5, Fintype.card (chunk 1 r) = counts 1 r := by
  intro r
  rw [Fintype.card_subtype]
  revert r
  decide +kernel

private theorem count02 : ∀ r : Fin 5, Fintype.card (chunk 2 r) = counts 2 r := by
  intro r
  rw [Fintype.card_subtype]
  revert r
  decide +kernel

private theorem count03 : ∀ r : Fin 5, Fintype.card (chunk 3 r) = counts 3 r := by
  intro r
  rw [Fintype.card_subtype]
  revert r
  decide +kernel

private theorem count04 : ∀ r : Fin 5, Fintype.card (chunk 4 r) = counts 4 r := by
  intro r
  rw [Fintype.card_subtype]
  revert r
  decide +kernel

private theorem count05 : ∀ r : Fin 5, Fintype.card (chunk 5 r) = counts 5 r := by
  intro r
  rw [Fintype.card_subtype]
  revert r
  decide +kernel

private theorem count06 : ∀ r : Fin 5, Fintype.card (chunk 6 r) = counts 6 r := by
  intro r
  rw [Fintype.card_subtype]
  revert r
  decide +kernel

private theorem count07 : ∀ r : Fin 5, Fintype.card (chunk 7 r) = counts 7 r := by
  intro r
  rw [Fintype.card_subtype]
  revert r
  decide +kernel

private theorem count08 : ∀ r : Fin 5, Fintype.card (chunk 8 r) = counts 8 r := by
  intro r
  rw [Fintype.card_subtype]
  revert r
  decide +kernel

private theorem count09 : ∀ r : Fin 5, Fintype.card (chunk 9 r) = counts 9 r := by
  intro r
  rw [Fintype.card_subtype]
  revert r
  decide +kernel

private theorem count10 : ∀ r : Fin 5, Fintype.card (chunk 10 r) = counts 10 r := by
  intro r
  rw [Fintype.card_subtype]
  revert r
  decide +kernel

private theorem count11 : ∀ r : Fin 5, Fintype.card (chunk 11 r) = counts 11 r := by
  intro r
  rw [Fintype.card_subtype]
  revert r
  decide +kernel

private theorem count12 : ∀ r : Fin 5, Fintype.card (chunk 12 r) = counts 12 r := by
  intro r
  rw [Fintype.card_subtype]
  revert r
  decide +kernel

private theorem count13 : ∀ r : Fin 5, Fintype.card (chunk 13 r) = counts 13 r := by
  intro r
  rw [Fintype.card_subtype]
  revert r
  decide +kernel

private theorem count14 : ∀ r : Fin 5, Fintype.card (chunk 14 r) = counts 14 r := by
  intro r
  rw [Fintype.card_subtype]
  revert r
  decide +kernel

private theorem count15 : ∀ r : Fin 5, Fintype.card (chunk 15 r) = counts 15 r := by
  intro r
  rw [Fintype.card_subtype]
  revert r
  decide +kernel

private theorem count16 : ∀ r : Fin 5, Fintype.card (chunk 16 r) = counts 16 r := by
  intro r
  rw [Fintype.card_subtype]
  revert r
  decide +kernel

private theorem count17 : ∀ r : Fin 5, Fintype.card (chunk 17 r) = counts 17 r := by
  intro r
  rw [Fintype.card_subtype]
  revert r
  decide +kernel

private theorem count18 : ∀ r : Fin 5, Fintype.card (chunk 18 r) = counts 18 r := by
  intro r
  rw [Fintype.card_subtype]
  revert r
  decide +kernel

private theorem count19 : ∀ r : Fin 5, Fintype.card (chunk 19 r) = counts 19 r := by
  intro r
  rw [Fintype.card_subtype]
  revert r
  decide +kernel

private theorem count20 : ∀ r : Fin 5, Fintype.card (chunk 20 r) = counts 20 r := by
  intro r
  rw [Fintype.card_subtype]
  revert r
  decide +kernel

private theorem count21 : ∀ r : Fin 5, Fintype.card (chunk 21 r) = counts 21 r := by
  intro r
  rw [Fintype.card_subtype]
  revert r
  decide +kernel

private theorem count22 : ∀ r : Fin 5, Fintype.card (chunk 22 r) = counts 22 r := by
  intro r
  rw [Fintype.card_subtype]
  revert r
  decide +kernel

private theorem count23 : ∀ r : Fin 5, Fintype.card (chunk 23 r) = counts 23 r := by
  intro r
  rw [Fintype.card_subtype]
  revert r
  decide +kernel

private theorem count24 : ∀ r : Fin 5, Fintype.card (chunk 24 r) = counts 24 r := by
  intro r
  rw [Fintype.card_subtype]
  revert r
  decide +kernel

private theorem count25 : ∀ r : Fin 5, Fintype.card (chunk 25 r) = counts 25 r := by
  intro r
  rw [Fintype.card_subtype]
  revert r
  decide +kernel

private theorem count26 : ∀ r : Fin 5, Fintype.card (chunk 26 r) = counts 26 r := by
  intro r
  rw [Fintype.card_subtype]
  revert r
  decide +kernel

private theorem count27 : ∀ r : Fin 5, Fintype.card (chunk 27 r) = counts 27 r := by
  intro r
  rw [Fintype.card_subtype]
  revert r
  decide +kernel

private theorem count28 : ∀ r : Fin 5, Fintype.card (chunk 28 r) = counts 28 r := by
  intro r
  rw [Fintype.card_subtype]
  revert r
  decide +kernel

private theorem count29 : ∀ r : Fin 5, Fintype.card (chunk 29 r) = counts 29 r := by
  intro r
  rw [Fintype.card_subtype]
  revert r
  decide +kernel

private theorem count30 : ∀ r : Fin 5, Fintype.card (chunk 30 r) = counts 30 r := by
  intro r
  rw [Fintype.card_subtype]
  revert r
  decide +kernel

private theorem count31 : ∀ r : Fin 5, Fintype.card (chunk 31 r) = counts 31 r := by
  intro r
  rw [Fintype.card_subtype]
  revert r
  decide +kernel

private theorem count32 : ∀ r : Fin 5, Fintype.card (chunk 32 r) = counts 32 r := by
  intro r
  rw [Fintype.card_subtype]
  revert r
  decide +kernel

private theorem count33 : ∀ r : Fin 5, Fintype.card (chunk 33 r) = counts 33 r := by
  intro r
  rw [Fintype.card_subtype]
  revert r
  decide +kernel

private theorem count34 : ∀ r : Fin 5, Fintype.card (chunk 34 r) = counts 34 r := by
  intro r
  rw [Fintype.card_subtype]
  revert r
  decide +kernel

private theorem count35 : ∀ r : Fin 5, Fintype.card (chunk 35 r) = counts 35 r := by
  intro r
  rw [Fintype.card_subtype]
  revert r
  decide +kernel

private theorem count36 : ∀ r : Fin 5, Fintype.card (chunk 36 r) = counts 36 r := by
  intro r
  rw [Fintype.card_subtype]
  revert r
  decide +kernel

private theorem count37 : ∀ r : Fin 5, Fintype.card (chunk 37 r) = counts 37 r := by
  intro r
  rw [Fintype.card_subtype]
  revert r
  decide +kernel

private theorem count38 : ∀ r : Fin 5, Fintype.card (chunk 38 r) = counts 38 r := by
  intro r
  rw [Fintype.card_subtype]
  revert r
  decide +kernel

private theorem count39 : ∀ r : Fin 5, Fintype.card (chunk 39 r) = counts 39 r := by
  intro r
  rw [Fintype.card_subtype]
  revert r
  decide +kernel

private theorem count40 : ∀ r : Fin 5, Fintype.card (chunk 40 r) = counts 40 r := by
  intro r
  rw [Fintype.card_subtype]
  revert r
  decide +kernel

private theorem count41 : ∀ r : Fin 5, Fintype.card (chunk 41 r) = counts 41 r := by
  intro r
  rw [Fintype.card_subtype]
  revert r
  decide +kernel

private theorem count42 : ∀ r : Fin 5, Fintype.card (chunk 42 r) = counts 42 r := by
  intro r
  rw [Fintype.card_subtype]
  revert r
  decide +kernel

private theorem count43 : ∀ r : Fin 5, Fintype.card (chunk 43 r) = counts 43 r := by
  intro r
  rw [Fintype.card_subtype]
  revert r
  decide +kernel

private theorem count44 : ∀ r : Fin 5, Fintype.card (chunk 44 r) = counts 44 r := by
  intro r
  rw [Fintype.card_subtype]
  revert r
  decide +kernel

private theorem count45 : ∀ r : Fin 5, Fintype.card (chunk 45 r) = counts 45 r := by
  intro r
  rw [Fintype.card_subtype]
  revert r
  decide +kernel

private theorem count46 : ∀ r : Fin 5, Fintype.card (chunk 46 r) = counts 46 r := by
  intro r
  rw [Fintype.card_subtype]
  revert r
  decide +kernel

private theorem count47 : ∀ r : Fin 5, Fintype.card (chunk 47 r) = counts 47 r := by
  intro r
  rw [Fintype.card_subtype]
  revert r
  decide +kernel

private theorem count48 : ∀ r : Fin 5, Fintype.card (chunk 48 r) = counts 48 r := by
  intro r
  rw [Fintype.card_subtype]
  revert r
  decide +kernel

private theorem count49 : ∀ r : Fin 5, Fintype.card (chunk 49 r) = counts 49 r := by
  intro r
  rw [Fintype.card_subtype]
  revert r
  decide +kernel

private theorem count50 : ∀ r : Fin 5, Fintype.card (chunk 50 r) = counts 50 r := by
  intro r
  rw [Fintype.card_subtype]
  revert r
  decide +kernel

private theorem count51 : ∀ r : Fin 5, Fintype.card (chunk 51 r) = counts 51 r := by
  intro r
  rw [Fintype.card_subtype]
  revert r
  decide +kernel

private theorem count52 : ∀ r : Fin 5, Fintype.card (chunk 52 r) = counts 52 r := by
  intro r
  rw [Fintype.card_subtype]
  revert r
  decide +kernel

private theorem count53 : ∀ r : Fin 5, Fintype.card (chunk 53 r) = counts 53 r := by
  intro r
  rw [Fintype.card_subtype]
  revert r
  decide +kernel

private theorem count54 : ∀ r : Fin 5, Fintype.card (chunk 54 r) = counts 54 r := by
  intro r
  rw [Fintype.card_subtype]
  revert r
  decide +kernel

private theorem count55 : ∀ r : Fin 5, Fintype.card (chunk 55 r) = counts 55 r := by
  intro r
  rw [Fintype.card_subtype]
  revert r
  decide +kernel

private theorem count56 : ∀ r : Fin 5, Fintype.card (chunk 56 r) = counts 56 r := by
  intro r
  rw [Fintype.card_subtype]
  revert r
  decide +kernel

private theorem count57 : ∀ r : Fin 5, Fintype.card (chunk 57 r) = counts 57 r := by
  intro r
  rw [Fintype.card_subtype]
  revert r
  decide +kernel

private theorem count58 : ∀ r : Fin 5, Fintype.card (chunk 58 r) = counts 58 r := by
  intro r
  rw [Fintype.card_subtype]
  revert r
  decide +kernel

private theorem count59 : ∀ r : Fin 5, Fintype.card (chunk 59 r) = counts 59 r := by
  intro r
  rw [Fintype.card_subtype]
  revert r
  decide +kernel

private theorem chunk_card (k : Fin 60) (r : Fin 5) : Fintype.card (chunk k r) = counts k r := by
  fin_cases k
  · exact count00 r
  · exact count01 r
  · exact count02 r
  · exact count03 r
  · exact count04 r
  · exact count05 r
  · exact count06 r
  · exact count07 r
  · exact count08 r
  · exact count09 r
  · exact count10 r
  · exact count11 r
  · exact count12 r
  · exact count13 r
  · exact count14 r
  · exact count15 r
  · exact count16 r
  · exact count17 r
  · exact count18 r
  · exact count19 r
  · exact count20 r
  · exact count21 r
  · exact count22 r
  · exact count23 r
  · exact count24 r
  · exact count25 r
  · exact count26 r
  · exact count27 r
  · exact count28 r
  · exact count29 r
  · exact count30 r
  · exact count31 r
  · exact count32 r
  · exact count33 r
  · exact count34 r
  · exact count35 r
  · exact count36 r
  · exact count37 r
  · exact count38 r
  · exact count39 r
  · exact count40 r
  · exact count41 r
  · exact count42 r
  · exact count43 r
  · exact count44 r
  · exact count45 r
  · exact count46 r
  · exact count47 r
  · exact count48 r
  · exact count49 r
  · exact count50 r
  · exact count51 r
  · exact count52 r
  · exact count53 r
  · exact count54 r
  · exact count55 r
  · exact count56 r
  · exact count57 r
  · exact count58 r
  · exact count59 r

/-- The five exact colour-fibre cardinalities, before geometric transport. -/
theorem fibre_card (r : Fin 5) : Nat.card {i : Fin 3795 // (node i).root = r} =
    (![1,42,56,1008,2688] : Fin 5 → ℕ) r := by
  rw [Nat.card_eq_fintype_card,Fintype.card_congr (chunkEquiv r),Fintype.card_sigma]
  simp only [chunk_card]
  revert r
  decide +kernel
end Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.NativeLineOrbit
