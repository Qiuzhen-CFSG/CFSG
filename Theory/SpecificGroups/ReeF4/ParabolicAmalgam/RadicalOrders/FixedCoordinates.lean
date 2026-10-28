module

public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.RadicalOrders.FixedCoordinates.Blocks
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.RadicalOrders.FixedCoordinates.MatrixRelations
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.RadicalOrders.FixedCoordinates.RootPartition

/-!
# Ree twist-fixed root coordinates

A geometric partition into commuting pairs and B₂ quartets supplies an order
of all supported roots. The product of the block words is exactly the split
coordinate word in that order. Unique split coordinates make this product
injective, so the actual Ree fixed equation is equivalent to the separate
collected equations in each block. The scalar solutions give one free field
coordinate per pair and two per quartet. Change of order then gives the same
cardinality, and hence a parameter equivalence, in every split root order.

The final theorem `fixedParametersEquiv` uses the concrete root partition and
the proved F₄ matrix relations to discharge every block-calculation input.
It gives 12 free coordinates for the positive support, 10 for the Suzuki
radical and 11 for the linear radical. Only the split-factorization hypothesis
is retained for the caller. All arguments include `m = 0`, the full binary
Ree group.

Source: Aschbacher–Smith F.1.12(I)(5), printed p.263 (PDF p.274)
of `refs/quasithin.pdf`.
-/

@[expose] public section
noncomputable section

namespace ReeF4.Parabolics.RadicalCoordinates.FixedCoordinates

open Theory.AlgebraicGroup

abbrev BlockParameters (m : ℕ) (k : Support) :=
  (Fin (pairCount k) → Fin 2 → CoefficientField m) ×
    (Fin (quartetCount k) → Fin 4 → CoefficientField m)

def blockTwist (m : ℕ) {k : Support} (t : BlockParameters m k) : BlockParameters m k :=
  (fun i => pairTwist m (t.1 i), fun i => quartetTwist m (t.2 i))

def blockSolution (m : ℕ) {k : Support}
    (t : (Fin (pairCount k) → CoefficientField m) ×
      (Fin (quartetCount k) → Fin 2 → CoefficientField m)) : BlockParameters m k :=
  (fun i => pairSolution m (t.1 i), fun i => quartetSolution m (t.2 i 0) (t.2 i 1))

def blockFixedEquiv (m : ℕ) (k : Support) :
    {t : BlockParameters m k // blockTwist m t = t} ≃
      (Fin (pairCount k) → CoefficientField m) ×
        (Fin (quartetCount k) → Fin 2 → CoefficientField m) where
  toFun t := (fun i => t.val.1 i 0, fun i => ![t.val.2 i 0, t.val.2 i 2])
  invFun t := ⟨blockSolution m t, by
    apply Prod.ext
    · funext i
      exact pairSolution_fixed m _
    · funext i
      exact quartetSolution_fixed m _ _⟩
  left_inv t := by
    apply Subtype.ext
    apply Prod.ext
    · funext i
      exact ((pairTwist_fixed_iff m _).mp (congrFun (congrArg Prod.fst t.property) i)).symm
    · funext i
      exact ((quartetTwist_fixed_iff m _).mp (congrFun (congrArg Prod.snd t.property) i)).symm
  right_inv t := by
    apply Prod.ext
    · rfl
    · funext i j
      fin_cases j <;> rfl

def RootBlocks.repack {k : Support} (B : RootBlocks k) (m : ℕ) :
    Parameters m k ≃ BlockParameters m k where
  toFun t := (fun i j => t (B.roots (.inl (i, j))), fun i j => t (B.roots (.inr (i, j))))
  invFun t r := Sum.elim (fun ij => t.1 ij.1 ij.2) (fun ij => t.2 ij.1 ij.2) (B.roots.symm r)
  left_inv t := by
    funext r
    obtain ⟨s, rfl⟩ := B.roots.surjective r
    cases s <;> simp
  right_inv t := by
    apply Prod.ext <;> funext i j <;> simp

def RootBlocks.blockWord {k : Support} (B : RootBlocks k) (m : ℕ)
    (t : BlockParameters m k) : SplitGroup m :=
  (List.ofFn fun i => pairWord m (fun j => (B.roots (.inl (i, j))).val) (t.1 i)).prod *
    (List.ofFn fun i => quartetWord m (fun j => (B.roots (.inr (i, j))).val) (t.2 i)).prod

def slotOrder (k : Support) :
    Fin (pairCount k * 2 + quartetCount k * 4) ≃ Slot k :=
  finSumFinEquiv.symm.trans (Equiv.sumCongr finProdFinEquiv.symm finProdFinEquiv.symm)

theorem RootBlocks.card_roots {k : Support} (B : RootBlocks k) :
    Nat.card (Root k) = pairCount k * 2 + quartetCount k * 4 := by
  simpa using (Nat.card_congr ((slotOrder k).trans B.roots)).symm

def RootBlocks.order {k : Support} (B : RootBlocks k) : RootOrder k :=
  (finCongr B.card_roots).trans ((slotOrder k).trans B.roots)

private theorem ofFn_slotOrder {α : Type*} (k : Support) (f : Slot k → α) :
    List.ofFn (fun i => f (slotOrder k i)) =
      (List.ofFn fun i => List.ofFn fun j => f (.inl (i, j))).flatten ++
        (List.ofFn fun i => List.ofFn fun j => f (.inr (i, j))).flatten := by
  rw [List.ofFn_add]
  change (List.ofFn fun i : Fin (pairCount k * 2) =>
    f (slotOrder k (Fin.castAdd (quartetCount k * 4) i))) ++
    (List.ofFn fun i : Fin (quartetCount k * 4) =>
      f (slotOrder k (Fin.natAdd (pairCount k * 2) i))) = _
  simp only [slotOrder, Equiv.trans_apply, finSumFinEquiv_symm_apply_castAdd,
    finSumFinEquiv_symm_apply_natAdd, Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr]
  congr 1 <;> rw [List.ofFn_mul] <;> congr 1 <;> apply congrArg List.ofFn <;> funext i <;>
    apply congrArg List.ofFn <;> funext j
  all_goals
    congr 2
    apply finProdFinEquiv.injective
    rw [Equiv.apply_symm_apply]
    apply Fin.ext
    change _ * _ + _ = _ + _ * _
    ac_rfl

theorem RootBlocks.word_eq_blockWord {k : Support} (B : RootBlocks k) (m : ℕ)
    (t : Parameters m k) : word m B.order t = B.blockWord m (B.repack m t) := by
  unfold word RootBlocks.order
  change (List.ofFn (fun i =>
    rootGeneratorInGroup m (B.roots (slotOrder k (Fin.cast B.card_roots i))).val
      (t (B.roots (slotOrder k (Fin.cast B.card_roots i)))))).prod = _
  rw [← List.ofFn_congr B.card_roots.symm
    (fun i => rootGeneratorInGroup m (B.roots (slotOrder k i)).val
      (t (B.roots (slotOrder k i))))]
  rw [ofFn_slotOrder k (fun s => rootGeneratorInGroup m (B.roots s).val (t (B.roots s))),
    List.prod_append]
  simp only [List.prod_flatten, List.map_ofFn]
  unfold RootBlocks.blockWord RootBlocks.repack
  congr 1 <;> apply congrArg List.prod <;> apply congrArg List.ofFn <;> funext i
  · simp [List.ofFn_succ, pairWord]
  · simp [List.ofFn_succ, quartetWord, mul_assoc]

theorem RootBlocks.blockWord_injective {k : Support} (B : RootBlocks k) (m : ℕ)
    (hsplit : Function.Bijective (wordInSubgroup m B.order)) :
    Function.Injective (B.blockWord m) := by
  intro x y h
  apply (B.repack m).symm.injective
  apply hsplit.1
  apply Subtype.ext
  change word m B.order _ = word m B.order _
  simpa only [B.word_eq_blockWord, Equiv.apply_symm_apply] using h

theorem RootBlocks.twist_blockWord {k : Support} (B : RootBlocks k) (m : ℕ)
    (hcomm : MixedRootCommutation m) (hswap : B2RootSwap m)
    (t : BlockParameters m k) :
    reeTwist m (B.blockWord m t) = B.blockWord m (blockTwist m t) := by
  simp only [RootBlocks.blockWord, map_mul, map_list_prod, List.map_ofFn,
    Function.comp_def, B.twist_pair m hcomm, B.twist_quartet m hcomm hswap, blockTwist]

def RootBlocks.fixedParametersEquiv {k : Support} (B : RootBlocks k) (m : ℕ)
    (hsplit : Function.Bijective (wordInSubgroup m B.order))
    (hcomm : MixedRootCommutation m) (hswap : B2RootSwap m) :
    FixedParameters m B.order ≃ {t : BlockParameters m k // blockTwist m t = t} where
  toFun t := ⟨B.repack m t.val, by
    apply B.blockWord_injective m hsplit
    rw [← B.twist_blockWord m hcomm hswap, ← B.word_eq_blockWord]
    exact t.property⟩
  invFun t := ⟨(B.repack m).symm t.val, by
    rw [B.word_eq_blockWord, Equiv.apply_symm_apply, B.twist_blockWord m hcomm hswap,
      t.property]⟩
  left_inv t := Subtype.ext ((B.repack m).symm_apply_apply t.val)
  right_inv t := Subtype.ext ((B.repack m).apply_symm_apply t.val)

theorem card_blockFixedParameters (m : ℕ) (k : Support) :
    Nat.card {t : BlockParameters m k // blockTwist m t = t} =
      Nat.card (Fin (fixedDimension k) → CoefficientField m) := by
  rw [Nat.card_congr (blockFixedEquiv m k), Nat.card_prod, Nat.card_fun,
    Nat.card_fun, Nat.card_fun, Nat.card_fin, Nat.card_fin, Nat.card_fin,
    ← pow_mul, ← pow_add, Nat.card_fun, Nat.card_fin, dimension_eq, Nat.mul_comm 2]

theorem fixedParametersEquiv_of_blocks (m : ℕ) {k : Support} (B : RootBlocks k)
    (hsplit : ∀ e : RootOrder k, Function.Bijective (wordInSubgroup m e))
    (hcomm : MixedRootCommutation m) (hswap : B2RootSwap m) (e : RootOrder k) :
    Nonempty (FixedParameters m e ≃ (Fin (fixedDimension k) → CoefficientField m)) := by
  let : Finite (FixedParameters m e) := by unfold FixedParameters; infer_instance
  apply Finite.card_eq.mp
  calc
    Nat.card (FixedParameters m e) = Nat.card (FixedParameters m B.order) :=
      Nat.card_congr (changeOrder m e B.order (hsplit e) (hsplit B.order))
    _ = Nat.card {t : BlockParameters m k // blockTwist m t = t} :=
      Nat.card_congr (B.fixedParametersEquiv m (hsplit B.order) hcomm hswap)
    _ = _ := card_blockFixedParameters m k

/-- Unique split factorization gives the actual Ree-fixed locus exactly
`fixedDimension k` free field coordinates, in every root order. The concrete
root partition and both matrix relations are proved, including at `m = 0`. -/
theorem fixedParametersEquiv (m : ℕ) {k : Support}
    (hsplit : ∀ e : RootOrder k, Function.Bijective (wordInSubgroup m e))
    (e : RootOrder k) :
    Nonempty (FixedParameters m e ≃ (Fin (fixedDimension k) → CoefficientField m)) :=
  fixedParametersEquiv_of_blocks m (rootBlocks k) hsplit
    (mixedRootCommutation m) (b2RootSwap m) e

end ReeF4.Parabolics.RadicalCoordinates.FixedCoordinates
