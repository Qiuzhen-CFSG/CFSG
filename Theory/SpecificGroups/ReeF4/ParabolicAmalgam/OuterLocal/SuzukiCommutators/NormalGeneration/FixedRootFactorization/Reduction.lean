module

public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.SuzukiCommutators.NormalGeneration.FixedRootFactorization.Inputs

/-!
# Fixed-block factorization and central-parameter generation

A B₂ fixed tuple `(a, f(a), c, g(c) + a*g(a))` equals the main word at `a`
times the central word at `g(c) + a*g(a)`. Top-root commutation proves this
identity in the actual split carrier. Unique split coordinates then force
the twist equation for a product of blocks to hold in every block, giving
an explicit four-pair/three-quartet factorization of the fixed radical.

The B₂ multiplication formula at first parameter 1 expresses every central
word as the inverse of one main word times two main words. Thus the seven
main curves generate the fixed radical. This proof uses no subgroup-order
comparison, normal generation, or perfectness.

The theorems remain conditional on a matching geometric layout, the exact
block matrix relations, and `MainParameterProduct`. Their assembly owner
must discharge those inputs; split bijectivity is the separately authorized
coordinate premise of the final task.

Source: GLS3 2.3.7 and Table 2.4, type V, in
`refs/KGroup/GLS3/chapter2.tex`; application to Aschbacher–Smith F.1.12(II)(i),
printed pp.263–264 of `refs/quasithin.pdf`.
-/

public section
noncomputable section
namespace ReeF4.Parabolics.OuterLocal.SuzukiCommutators.NormalGeneration
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open LargeLocalSeeds RadicalCoordinates RadicalCoordinates.FixedCoordinates Subgroup

namespace RootWordLayout
variable {k : Support} (L : RootWordLayout k)

private theorem root_zero (m : ℕ) (r : F4Chevalley.Root) :
    rootGeneratorInGroup m r 0 = 1 := Subtype.ext (F4Chevalley.rootCurve_zero r)

private theorem root_add (m : ℕ) (r : F4Chevalley.Root) (a b : CoefficientField m) :
    rootGeneratorInGroup m r (a + b) =
      rootGeneratorInGroup m r a * rootGeneratorInGroup m r b :=
  Subtype.ext (F4Chevalley.rootCurve_add r a b)

theorem pair_fieldEnd (m : ℕ) (j : Fin (pairCount k)) :
    rootFieldEnd m (longRoot (L.pairIndex j)) = halfFrobenius m := by
  have h := L.blocks.pair_long j
  rw [L.pair_long] at h
  simp [rootFieldEnd, h, halfFrobenius]

theorem quartet_fieldEnd (m : ℕ) (j : Fin (quartetCount k)) :
    rootFieldEnd m (longRoot (L.quartetIndex j)) = halfFrobenius m := by
  have h := L.blocks.quartet_long j
  rw [L.quartet_long] at h
  simp [rootFieldEnd, h, halfFrobenius]

theorem pair_rootWord (m : ℕ) (j : Fin (pairCount k)) (a : CoefficientField m) :
    rootWord m (L.pairIndex j) a =
      pairWord m (fun s => (L.blocks.roots (.inl (j, s))).val) (pairSolution m a) := by
  simp [rootWord, L.pair_odd, pairWord, pairSolution, L.pair_long, L.pair_short,
    L.pair_fieldEnd]

theorem pair_centralWord (m : ℕ) (j : Fin (pairCount k)) (a : CoefficientField m) :
    centralWord m (L.pairIndex j) a = rootWord m (L.pairIndex j) a := by
  simp [centralWord, rootWord, L.pair_odd, L.pair_high, L.pair_mixed]

theorem quartet_rootWord (m : ℕ) (j : Fin (quartetCount k)) (a : CoefficientField m) :
    rootWord m (L.quartetIndex j) a =
      quartetWord m (fun s => (L.blocks.roots (.inr (j, s))).val)
        (quartetSolution m a (a * halfFrobenius m a)) := by
  simp [rootWord, L.quartet_even, quartetWord, quartetSolution,
    L.quartet_long, L.quartet_short, L.quartet_mixed, L.quartet_high,
    L.quartet_fieldEnd, map_mul, titsEnd_halfFrobenius, mul_comm,
    CharTwo.add_self_eq_zero, root_zero]

private theorem supported_pos {r : F4Chevalley.Root} (h : Supported k r) :
    typeF4RootPairing_base.IsPos r := by
  cases k with
  | positive => exact h
  | radical s => exact h.1

theorem quartet_top_commute (m : ℕ) (hc : MixedRootCommutation m)
    (j : Fin (quartetCount k)) (a b : CoefficientField m) :
    Commute (rootGeneratorInGroup m (highRoot (L.quartetIndex j)) a)
      (rootGeneratorInGroup m (mixedRoot (L.quartetIndex j)) b) := by
  have hl : IsLongRoot (L.blocks.roots (.inr (j, 3))).val := by
    rw [← L.blocks.quartet_dual_two]
    exact (exceptionalRootPermutation_short_iff _).mp (L.blocks.quartet_short_two j)
  have hh := hc _ _ (supported_pos (L.blocks.roots (.inr (j, 3))).property)
    (supported_pos (L.blocks.roots (.inr (j, 2))).property) hl
    (L.blocks.quartet_short_two j)
    (by rw [L.blocks.quartet_top_dot]; norm_num) a b
  simpa only [L.quartet_high, L.quartet_mixed] using hh

theorem quartet_centralWord (m : ℕ) (hc : MixedRootCommutation m)
    (j : Fin (quartetCount k)) (u : CoefficientField m) :
    centralWord m (L.quartetIndex j) u =
      quartetWord m (fun s => (L.blocks.roots (.inr (j, s))).val)
        (quartetSolution m 0 (halfFrobenius m u)) := by
  simpa [centralWord, quartetWord, quartetSolution, L.quartet_long, L.quartet_short,
    L.quartet_mixed, L.quartet_high, L.quartet_fieldEnd, root_zero,
    titsEnd_halfFrobenius] using (L.quartet_top_commute m hc j u (halfFrobenius m u)).eq

/-- The actual fixed B₂ word factors into its main and central parameters. -/
theorem quartet_factorization (m : ℕ) (hc : MixedRootCommutation m)
    (j : Fin (quartetCount k)) (a c : CoefficientField m) :
    quartetWord m (fun s => (L.blocks.roots (.inr (j, s))).val)
        (quartetSolution m a c) =
      rootWord m (L.quartetIndex j) a *
        centralWord m (L.quartetIndex j) (titsEnd m c + a * titsEnd m a) := by
  let u := titsEnd m c + a * titsEnd m a
  have he : a * halfFrobenius m a + halfFrobenius m u = c := by
    simp [u, map_add, map_mul, halfFrobenius_titsEnd, mul_comm,
      add_left_comm, CharTwo.add_self_eq_zero]
  simp only [quartetWord, quartetSolution, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, L.quartet_long, L.quartet_short, L.quartet_mixed,
    L.quartet_high, rootWord, if_pos (L.quartet_even j), centralWord,
    L.quartet_fieldEnd]
  change _ = _ * (rootGeneratorInGroup m (highRoot (L.quartetIndex j)) u *
    rootGeneratorInGroup m (mixedRoot (L.quartetIndex j)) (halfFrobenius m u))
  rw [(L.quartet_top_commute m hc j u (halfFrobenius m u)).eq]
  simp only [← mul_assoc]
  rw [mul_assoc (rootGeneratorInGroup m (longRoot (L.quartetIndex j)) a *
    rootGeneratorInGroup m (shortRoot (L.quartetIndex j)) (halfFrobenius m a))
    (rootGeneratorInGroup m (mixedRoot (L.quartetIndex j)) (a * halfFrobenius m a))
    (rootGeneratorInGroup m (mixedRoot (L.quartetIndex j)) (halfFrobenius m u)),
    ← root_add, he]

private theorem generator_mem (m : ℕ) (r : Root k) (a : CoefficientField m) :
    rootGeneratorInGroup m r.val a ∈ splitSubgroup m k := by
  cases k <;> exact subset_closure ⟨_, _, r.property, rfl⟩

private theorem pair_mem (m : ℕ) (j : Fin (pairCount k)) (t : Fin 2 → CoefficientField m) :
    pairWord m (fun s => (L.blocks.roots (.inl (j, s))).val) t ∈ splitSubgroup m k :=
  mul_mem (generator_mem m _ _) (generator_mem m _ _)

private theorem quartet_mem (m : ℕ) (j : Fin (quartetCount k))
    (t : Fin 4 → CoefficientField m) :
    quartetWord m (fun s => (L.blocks.roots (.inr (j, s))).val) t ∈ splitSubgroup m k :=
  mul_mem (mul_mem (mul_mem (generator_mem m _ _) (generator_mem m _ _))
    (generator_mem m _ _)) (generator_mem m _ _)

theorem pair_root_fixed_mem (m : ℕ) (hc : MixedRootCommutation m)
    (j : Fin (pairCount k)) (a : CoefficientField m) :
    reeTwist m (rootWord m (L.pairIndex j) a) = rootWord m (L.pairIndex j) a ∧
      rootWord m (L.pairIndex j) a ∈ splitSubgroup m k := by
  rw [L.pair_rootWord]
  exact ⟨by rw [L.blocks.twist_pair m hc, pairSolution_fixed], L.pair_mem m _ _⟩

theorem pair_central_fixed_mem (m : ℕ) (hc : MixedRootCommutation m)
    (j : Fin (pairCount k)) (a : CoefficientField m) :
    reeTwist m (centralWord m (L.pairIndex j) a) = centralWord m (L.pairIndex j) a ∧
      centralWord m (L.pairIndex j) a ∈ splitSubgroup m k := by
  rw [L.pair_centralWord]
  exact L.pair_root_fixed_mem m hc j a

theorem quartet_root_fixed_mem (m : ℕ) (hc : MixedRootCommutation m)
    (hs : B2RootSwap m) (j : Fin (quartetCount k)) (a : CoefficientField m) :
    reeTwist m (rootWord m (L.quartetIndex j) a) = rootWord m (L.quartetIndex j) a ∧
      rootWord m (L.quartetIndex j) a ∈ splitSubgroup m k := by
  rw [L.quartet_rootWord]
  exact ⟨by rw [L.blocks.twist_quartet m hc hs, quartetSolution_fixed], L.quartet_mem m _ _⟩

theorem quartet_central_fixed_mem (m : ℕ) (hc : MixedRootCommutation m)
    (hs : B2RootSwap m) (j : Fin (quartetCount k)) (a : CoefficientField m) :
    reeTwist m (centralWord m (L.quartetIndex j) a) = centralWord m (L.quartetIndex j) a ∧
      centralWord m (L.quartetIndex j) a ∈ splitSubgroup m k := by
  rw [L.quartet_centralWord m hc]
  exact ⟨by rw [L.blocks.twist_quartet m hc hs, quartetSolution_fixed], L.quartet_mem m _ _⟩

/-- A covering geometric layout proves fixedness and support membership of
both literal word families, using the exact matrix twist relations. -/
theorem words_fixed_mem (m : ℕ)
    (hcover : ∀ i : Fin 8, (∃ j, L.pairIndex j = i) ∨ (∃ j, L.quartetIndex j = i))
    (hc : MixedRootCommutation m) (hs : B2RootSwap m) (i : Fin 8) (a : CoefficientField m) :
    (reeTwist m (rootWord m i a) = rootWord m i a ∧
      rootWord m i a ∈ splitSubgroup m k) ∧
    (reeTwist m (centralWord m i a) = centralWord m i a ∧
      centralWord m i a ∈ splitSubgroup m k) := by
  rcases hcover i with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · exact ⟨L.pair_root_fixed_mem m hc j a, L.pair_central_fixed_mem m hc j a⟩
  · exact ⟨L.quartet_root_fixed_mem m hc hs j a, L.quartet_central_fixed_mem m hc hs j a⟩

/-- Collect the individually fixed blocks without commuting different blocks. -/
theorem blockWord_factorization (m : ℕ) (hc : MixedRootCommutation m)
    (t : BlockParameters m k) (hf : blockTwist m t = t) :
    L.blocks.blockWord m t =
      (List.ofFn fun j => rootWord m (L.pairIndex j) (t.1 j 0)).prod *
        (List.ofFn fun j => rootWord m (L.quartetIndex j) (t.2 j 0) *
          centralWord m (L.quartetIndex j)
            (titsEnd m (t.2 j 2) + t.2 j 0 * titsEnd m (t.2 j 0))).prod := by
  have hp (j : Fin (pairCount k)) :
      pairWord m (fun s => (L.blocks.roots (.inl (j, s))).val) (t.1 j) =
        rootWord m (L.pairIndex j) (t.1 j 0) := by
    have he := (pairTwist_fixed_iff m _).mp (congrFun (congrArg Prod.fst hf) j)
    exact (congrArg (pairWord m _) he).trans (L.pair_rootWord m j _).symm
  have hq (j : Fin (quartetCount k)) :
      quartetWord m (fun s => (L.blocks.roots (.inr (j, s))).val) (t.2 j) =
        rootWord m (L.quartetIndex j) (t.2 j 0) * centralWord m (L.quartetIndex j)
          (titsEnd m (t.2 j 2) + t.2 j 0 * titsEnd m (t.2 j 0)) := by
    have he := (quartetTwist_fixed_iff m _).mp (congrFun (congrArg Prod.snd hf) j)
    exact (congrArg (quartetWord m _) he).trans (L.quartet_factorization m hc j _ _)
  simp only [RootBlocks.blockWord, hp, hq]

end RootWordLayout

/-- Every central parameter follows from the B₂ product at first parameter 1.
This also applies at the binary endpoint. -/
theorem centralWord_mem_closure_of_product (m : ℕ) (hp : MainParameterProduct m)
    (i : Fin 8) (hi : i ≠ 0) (he : i.val % 2 = 0) (u : CoefficientField m) :
    centralWord m i u ∈ closure {z | ∃ i : Fin 8, i ≠ 0 ∧
      ∃ t : CoefficientField m, z = rootWord m i t} := by
  have hmain (a : CoefficientField m) : rootWord m i a ∈
      closure {z | ∃ i : Fin 8, i ≠ 0 ∧ ∃ t : CoefficientField m, z = rootWord m i t} :=
    subset_closure ⟨i, hi, a, rfl⟩
  have heq : centralWord m i u =
      (rootWord m i (1 + u))⁻¹ * (rootWord m i 1 * rootWord m i u) := by
    rw [hp i he u, inv_mul_cancel_left]
  rw [heq]
  exact mul_mem (inv_mem (hmain _)) (mul_mem (hmain _) (hmain _))

/-- Unique split coordinates force every radical block to be fixed separately.
The resulting factorization has four paired parameters and three B₂ pairs. -/
theorem fixed_radical_factorization_of_blocks (m : ℕ)
    (L : RootWordLayout (.radical .suzuki))
    (hc : MixedRootCommutation m) (hs : B2RootSwap m)
    (hsplit : ∀ e : RootOrder (.radical .suzuki), Function.Bijective (wordInSubgroup m e))
    (z : SplitGroup m) (hz : z ∈ splitRadical m .suzuki) (hf : reeTwist m z = z) :
    ∃ (a : Fin 4 → CoefficientField m) (b c : Fin 3 → CoefficientField m),
      z = (List.ofFn fun j => rootWord m (L.pairIndex j) (a j)).prod *
        (List.ofFn fun j => rootWord m (L.quartetIndex j) (b j) *
          centralWord m (L.quartetIndex j) (c j)).prod := by
  obtain ⟨t, ht⟩ := (hsplit L.blocks.order).2 ⟨z, hz⟩
  have hw : word m L.blocks.order t = z := congrArg Subtype.val ht
  have hfixed : blockTwist m (L.blocks.repack m t) = L.blocks.repack m t := by
    apply L.blocks.blockWord_injective m (hsplit L.blocks.order)
    rw [← L.blocks.twist_blockWord m hc hs, ← L.blocks.word_eq_blockWord, hw, hf]
  let p := L.blocks.repack m t
  refine ⟨(fun j => p.1 j 0), (fun j => p.2 j 0),
    (fun j => titsEnd m (p.2 j 2) + p.2 j 0 * titsEnd m (p.2 j 0)), ?_⟩
  exact hw.symm.trans ((L.blocks.word_eq_blockWord m t).trans
    (L.blockWord_factorization m hc p hfixed))

/-- Fixed factorization and the B₂ product generate the radical from its seven
main curves. The only coordinate premise is the supplied split bijectivity. -/
theorem fixed_radical_mem_closure_of_blocks (m : ℕ)
    (L : RootWordLayout (.radical .suzuki))
    (hpair : ∀ j, L.pairIndex j ≠ 0) (hquartet : ∀ j, L.quartetIndex j ≠ 0)
    (hc : MixedRootCommutation m) (hs : B2RootSwap m) (hp : MainParameterProduct m)
    (hsplit : ∀ e : RootOrder (.radical .suzuki), Function.Bijective (wordInSubgroup m e))
    (z : SplitGroup m) (hz : z ∈ splitRadical m .suzuki) (hf : reeTwist m z = z) :
    z ∈ closure {z | ∃ i : Fin 8, i ≠ 0 ∧
      ∃ t : CoefficientField m, z = rootWord m i t} := by
  obtain ⟨a, b, c, rfl⟩ := fixed_radical_factorization_of_blocks m L hc hs hsplit z hz hf
  apply mul_mem
  · apply list_prod_mem
    intro x hx
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx
    exact subset_closure ⟨L.pairIndex j, hpair j, _, rfl⟩
  · apply list_prod_mem
    intro x hx
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx
    exact mul_mem (subset_closure ⟨L.quartetIndex j, hquartet j, _, rfl⟩)
      (centralWord_mem_closure_of_product m hp _ (hquartet j) (L.quartet_even j) _)

/-- Transfer the two fixed word families into any supplied local twist, which
agrees with the concrete Ree twist on the split matrix group. -/
theorem words_fixed_mem_seed_of_blocks {m : ℕ} (d : LocalBlockInput m)
    (L : RootWordLayout .positive)
    (hcover : ∀ i : Fin 8, (∃ j, L.pairIndex j = i) ∨ (∃ j, L.quartetIndex j = i))
    (hc : MixedRootCommutation m) (hs : B2RootSwap m) (i : Fin 8) (a : CoefficientField m) :
    (d.twist (rootWord m i a) = rootWord m i a ∧ rootWord m i a ∈ splitSeed m .suzuki) ∧
    (d.twist (centralWord m i a) = centralWord m i a ∧
      centralWord m i a ∈ splitSeed m .suzuki) := by
  obtain ⟨⟨hx, hxmem⟩, ⟨hy, hymem⟩⟩ := L.words_fixed_mem m hcover hc hs i a
  have htw (z : SplitGroup m) : d.twist z = reeTwist m z :=
    DFunLike.congr_fun d.twist_toMonoidHom_eq z
  exact ⟨⟨(htw _).trans hx, splitUnipotent_le_splitSeed m .suzuki hxmem⟩,
    ⟨(htw _).trans hy, splitUnipotent_le_splitSeed m .suzuki hymem⟩⟩

/-- The conditional generation conclusion in the exact local-twist form used
by `radical_le_normalClosure_of_root_words`. The geometric and matrix inputs
must still be constructed before applying this to the canonical seed. -/
theorem fixed_radical_mem_closure_of_block_inputs {m : ℕ} (d : LocalBlockInput m)
    (L : RootWordLayout (.radical .suzuki))
    (hpair : ∀ j, L.pairIndex j ≠ 0) (hquartet : ∀ j, L.quartetIndex j ≠ 0)
    (hc : MixedRootCommutation m) (hs : B2RootSwap m) (hp : MainParameterProduct m)
    (hsplit : ∀ e : RootOrder (.radical .suzuki), Function.Bijective (wordInSubgroup m e))
    (z : SplitGroup m) (hz : z ∈ splitRadical m .suzuki) (hf : d.twist z = z) :
    z ∈ closure {z | ∃ i : Fin 8, i ≠ 0 ∧
      ∃ t : CoefficientField m, z = rootWord m i t} := by
  apply fixed_radical_mem_closure_of_blocks m L hpair hquartet hc hs hp hsplit z hz
  exact (DFunLike.congr_fun d.twist_toMonoidHom_eq z).symm.trans hf

end ReeF4.Parabolics.OuterLocal.SuzukiCommutators.NormalGeneration
