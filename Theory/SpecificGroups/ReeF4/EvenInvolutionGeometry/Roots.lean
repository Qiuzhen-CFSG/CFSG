module

public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.SuzukiCommutators.NormalGeneration.FixedRootFactorization
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.SuzukiCommutators.NormalGeneration.MatrixRelations.WeylGeometry
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.RadicalOrders.SplitCoordinates

/-!
# Concrete root involutions in the exceptional Ree carrier

The marked curves are the fifth block's central parameter `y₅(t)` and the
fourth block's additive parameter `x₄(t)` in the GLS numbering. Their split
words are `centralWord m 4 t` and `rootWord m 3 t`; indices in Lean start at
zero. They are elements of the actual exceptional-twist fixed group.

Fixed block coordinates prove membership in the positive subgroup. The
commuting top roots give the first additive law, and Weyl transport gives
the second. Injectivity follows by inserting each curve into the unique
positive block coordinates. Thus every nonzero parameter has order two.
The range subgroups and root-class predicates retain these actual matrices.

This module does not assert exhaustion, centralizer containment, or the
identification of the long-root class with the 2-central involutions.
Those are the remaining geometric calculations for Aschbacher–Smith,
16.1.4(1), 16.1.6, and 16.5.13–14, printed pp.1171–1172,1201–1203 of
`refs/quasithin.pdf`. Root-word conventions: GLS3 Table 2.4 and 2.4.5(d),
`refs/KGroup/GLS3/chapter2.tex`.
-/

@[expose] public section
noncomputable section
namespace ReeF4.EvenInvolutionGeometry
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open Parabolics LargeLocalSeeds
open Parabolics.OuterLocal.SuzukiCommutators.NormalGeneration
open Parabolics.RadicalCoordinates.FixedCoordinates

private theorem root_zero (m : ℕ) (r : F4Chevalley.Root) :
    rootGeneratorInGroup m r 0 = 1 := Subtype.ext (F4Chevalley.rootCurve_zero r)
private theorem root_add (m : ℕ) (r : F4Chevalley.Root) (a b : CoefficientField m) :
    rootGeneratorInGroup m r (a + b) = rootGeneratorInGroup m r a * rootGeneratorInGroup m r b :=
  Subtype.ext (F4Chevalley.rootCurve_add r a b)

private theorem exists_quartet_four :
    ∃ j, positiveRootWordLayout.quartetIndex j = 4 := by
  rcases positiveRootWordLayout.positive_covers 4 with ⟨j, hj⟩ | h
  · have hp := positiveRootWordLayout.pair_odd j
    rw [hj] at hp
    exact (hp (by decide)).elim
  · exact h

private theorem exists_pair_three :
    ∃ j, positiveRootWordLayout.pairIndex j = 3 := by
  rcases positiveRootWordLayout.positive_covers 3 with h | ⟨j, hj⟩
  · exact h
  · have hp := positiveRootWordLayout.quartet_even j
    rw [hj] at hp
    norm_num at hp

def longRootElement (m : ℕ) (t : CoefficientField m) : Model m :=
  ⟨centralWord m 4 t, by
    simpa only [ReeF4.mem_fixedSubgroup, LocalBlockInput.twist_eq_reeAutomorphism, reeAutomorphism_apply]
      using (centralWord_fixed_mem_seed (canonicalLocalBlockInput m) 4 t).1⟩

def shortRootElement (m : ℕ) (t : CoefficientField m) : Model m :=
  ⟨rootWord m 3 t, by
    simpa only [ReeF4.mem_fixedSubgroup, LocalBlockInput.twist_eq_reeAutomorphism, reeAutomorphism_apply]
      using (rootWord_fixed_mem_seed (canonicalLocalBlockInput m) 3 t).1⟩

@[simp] theorem longRootElement_coe (m : ℕ) (t : CoefficientField m) :
    toSplitGroup m (longRootElement m t) = centralWord m 4 t := toSplitGroup_apply m _
@[simp] theorem shortRootElement_coe (m : ℕ) (t : CoefficientField m) :
    toSplitGroup m (shortRootElement m t) = rootWord m 3 t := toSplitGroup_apply m _

theorem longRootElement_add (m : ℕ) (a b : CoefficientField m) :
    longRootElement m (a + b) = longRootElement m a * longRootElement m b := by
  apply Subtype.ext
  change centralWord m 4 (a + b) = centralWord m 4 a * centralWord m 4 b
  have hc (u v : CoefficientField m) :
      Commute (rootGeneratorInGroup m (highRoot 4) u)
        (rootGeneratorInGroup m (mixedRoot 4) v) :=
    by
      obtain ⟨j, hj⟩ := exists_quartet_four
      have h := positiveRootWordLayout.quartet_top_commute m (mixedRootCommutation m) j u v
      rw [hj] at h
      exact h
  simp only [centralWord, map_add, root_add]
  exact (hc b _).mul_mul_mul_comm _ _

theorem shortRootElement_add (m : ℕ) (a b : CoefficientField m) :
    shortRootElement m (a + b) = shortRootElement m a * shortRootElement m b :=
  Subtype.ext (rootWord_fourth_add m a b)

@[simp] theorem longRootElement_zero (m : ℕ) : longRootElement m 0 = 1 := by
  apply Subtype.ext
  simp [longRootElement, centralWord, root_zero]
@[simp] theorem shortRootElement_zero (m : ℕ) : shortRootElement m 0 = 1 := by
  apply Subtype.ext
  simp [shortRootElement, rootWord, root_zero]

theorem longRootElement_sq (m : ℕ) (t : CoefficientField m) :
    longRootElement m t ^ 2 = 1 := by
  rw [pow_two, ← longRootElement_add, CharTwo.add_self_eq_zero, longRootElement_zero]
theorem shortRootElement_sq (m : ℕ) (t : CoefficientField m) :
    shortRootElement m t ^ 2 = 1 := by
  rw [pow_two, ← shortRootElement_add, CharTwo.add_self_eq_zero, shortRootElement_zero]

theorem longRootElement_mem_unipotent (m : ℕ) (t : CoefficientField m) :
    longRootElement m t ∈ unipotent m := by
  obtain ⟨j, hj⟩ := exists_quartet_four
  have h := (positiveRootWordLayout.quartet_central_fixed_mem m (mixedRootCommutation m)
    (b2RootSwap m) j t).2
  rw [hj] at h
  change toSplitGroup m (longRootElement m t) ∈ splitUnipotent m
  rw [longRootElement_coe]
  exact h

theorem shortRootElement_mem_unipotent (m : ℕ) (t : CoefficientField m) :
    shortRootElement m t ∈ unipotent m := by
  obtain ⟨j, hj⟩ := exists_pair_three
  have h := (positiveRootWordLayout.pair_root_fixed_mem m (mixedRootCommutation m) j t).2
  rw [hj] at h
  change toSplitGroup m (shortRootElement m t) ∈ splitUnipotent m
  rw [shortRootElement_coe]
  exact h

private def shortParameters (m : ℕ) (j : Fin (pairCount .positive))
    (t : CoefficientField m) : BlockParameters m .positive :=
  (fun i => if i = j then pairSolution m t else (fun _ => 0), fun _ _ => 0)

private def longParameters (m : ℕ) (j : Fin (quartetCount .positive))
    (t : CoefficientField m) : BlockParameters m .positive :=
  (fun _ _ => 0, fun i => if i = j then quartetSolution m 0 (halfFrobenius m t)
    else (fun _ => 0))

private theorem short_blockWord (B : RootBlocks .positive) (m : ℕ)
    (j : Fin (pairCount .positive)) (t : CoefficientField m) :
    B.blockWord m (shortParameters m j t) =
      pairWord m (fun s => (B.roots (.inl (j, s))).val) (pairSolution m t) := by
  fin_cases j <;>
    simp [RootBlocks.blockWord, shortParameters, pairCount, quartetCount, List.ofFn_succ,
      pairWord, quartetWord, root_zero]

private theorem long_blockWord (B : RootBlocks .positive) (m : ℕ)
    (j : Fin (quartetCount .positive)) (t : CoefficientField m) :
    B.blockWord m (longParameters m j t) =
      quartetWord m (fun s => (B.roots (.inr (j, s))).val)
        (quartetSolution m 0 (halfFrobenius m t)) := by
  fin_cases j <;>
    simp [RootBlocks.blockWord, longParameters, pairCount, quartetCount, List.ofFn_succ,
      pairWord, quartetWord, root_zero]

private theorem short_word_coordinates (m : ℕ) (j : Fin (pairCount .positive))
    (t : CoefficientField m) :
    positiveRootWordLayout.blocks.blockWord m (shortParameters m j t) =
      rootWord m (positiveRootWordLayout.pairIndex j) t := by
  rw [short_blockWord, ← positiveRootWordLayout.pair_rootWord]

private theorem long_word_coordinates (m : ℕ) (j : Fin (quartetCount .positive))
    (t : CoefficientField m) :
    positiveRootWordLayout.blocks.blockWord m (longParameters m j t) =
      centralWord m (positiveRootWordLayout.quartetIndex j) t := by
  rw [long_blockWord, ← positiveRootWordLayout.quartet_centralWord m (mixedRootCommutation m)]

theorem shortRootElement_injective (m : ℕ) : Function.Injective (shortRootElement m) := by
  intro t u h
  obtain ⟨j, hj⟩ := exists_pair_three
  have hw : rootWord m 3 t = rootWord m 3 u := congrArg Subtype.val h
  rw [← hj, ← short_word_coordinates, ← short_word_coordinates] at hw
  have hparams := positiveRootWordLayout.blocks.blockWord_injective m
    (RadicalCoordinates.wordInSubgroup_bijective m _) hw
  simpa [shortParameters, pairSolution] using
    congrArg (fun p : BlockParameters m .positive => p.1 j 0) hparams

theorem longRootElement_injective (m : ℕ) : Function.Injective (longRootElement m) := by
  intro t u h
  obtain ⟨j, hj⟩ := exists_quartet_four
  have hw : centralWord m 4 t = centralWord m 4 u := congrArg Subtype.val h
  rw [← hj, ← long_word_coordinates, ← long_word_coordinates] at hw
  have hparams := positiveRootWordLayout.blocks.blockWord_injective m
    (RadicalCoordinates.wordInSubgroup_bijective m _) hw
  have hf : halfFrobenius m t = halfFrobenius m u := by
    simpa [longParameters, quartetSolution] using
      congrArg (fun p : BlockParameters m .positive => p.2 j 2) hparams
  simpa only [titsEnd_halfFrobenius] using congrArg (titsEnd m) hf

@[simp] theorem longRootElement_eq_one_iff (m : ℕ) (t : CoefficientField m) :
    longRootElement m t = 1 ↔ t = 0 := by
  rw [← longRootElement_zero m, (longRootElement_injective m).eq_iff]
@[simp] theorem shortRootElement_eq_one_iff (m : ℕ) (t : CoefficientField m) :
    shortRootElement m t = 1 ↔ t = 0 := by
  rw [← shortRootElement_zero m, (shortRootElement_injective m).eq_iff]

theorem longRootElement_orderOf (m : ℕ) {t : CoefficientField m} (ht : t ≠ 0) :
    orderOf (longRootElement m t) = 2 := by
  exact orderOf_eq_prime_iff.mpr
    ⟨longRootElement_sq m t, by simpa using ht⟩

theorem shortRootElement_orderOf (m : ℕ) {t : CoefficientField m} (ht : t ≠ 0) :
    orderOf (shortRootElement m t) = 2 := by
  exact orderOf_eq_prime_iff.mpr
    ⟨shortRootElement_sq m t, by simpa using ht⟩

/-- The actual additive long-root curve, as a group homomorphism. -/
def longRootHom (m : ℕ) : Multiplicative (CoefficientField m) →* Model m where
  toFun t := longRootElement m t.toAdd
  map_one' := longRootElement_zero m
  map_mul' a b := longRootElement_add m a.toAdd b.toAdd

/-- The actual additive short-root curve, as a group homomorphism. -/
def shortRootHom (m : ℕ) : Multiplicative (CoefficientField m) →* Model m where
  toFun t := shortRootElement m t.toAdd
  map_one' := shortRootElement_zero m
  map_mul' a b := shortRootElement_add m a.toAdd b.toAdd

/-- The marked root subgroup, defined by its matrices rather than its order. -/
def longRootGroup (m : ℕ) : Subgroup (Model m) := (longRootHom m).range
/-- The other marked root subgroup. -/
def shortRootGroup (m : ℕ) : Subgroup (Model m) := (shortRootHom m).range

@[simp] theorem mem_longRootGroup (m : ℕ) (x : Model m) :
    x ∈ longRootGroup m ↔ ∃ t, longRootElement m t = x := Iff.rfl
@[simp] theorem mem_shortRootGroup (m : ℕ) (x : Model m) :
    x ∈ shortRootGroup m ↔ ∃ t, shortRootElement m t = x := Iff.rfl

theorem longRootGroup_le_unipotent (m : ℕ) : longRootGroup m ≤ unipotent m := by
  intro x hx
  obtain ⟨t, rfl⟩ := (mem_longRootGroup m x).mp hx
  exact longRootElement_mem_unipotent m t

theorem shortRootGroup_le_unipotent (m : ℕ) : shortRootGroup m ≤ unipotent m := by
  intro x hx
  obtain ⟨t, rfl⟩ := (mem_shortRootGroup m x).mp hx
  exact shortRootElement_mem_unipotent m t

/-- Conjugacy to a nonidentity element of the specified long-root curve. -/
def IsLongRootInvolution {m : ℕ} (x : Model m) : Prop :=
  ∃ t : CoefficientField m, t ≠ 0 ∧ IsConj (longRootElement m t) x
/-- Conjugacy to a nonidentity element of the specified short-root curve. -/
def IsShortRootInvolution {m : ℕ} (x : Model m) : Prop :=
  ∃ t : CoefficientField m, t ≠ 0 ∧ IsConj (shortRootElement m t) x

theorem orderOf_of_isLongRootInvolution {m : ℕ} {x : Model m}
    (hx : IsLongRootInvolution x) : orderOf x = 2 := by
  obtain ⟨t, ht, h⟩ := hx
  obtain ⟨g, rfl⟩ := isConj_iff.mp h
  exact ((MulAut.conj g).orderOf_eq _).trans (longRootElement_orderOf m ht)

theorem orderOf_of_isShortRootInvolution {m : ℕ} {x : Model m}
    (hx : IsShortRootInvolution x) : orderOf x = 2 := by
  obtain ⟨t, ht, h⟩ := hx
  obtain ⟨g, rfl⟩ := isConj_iff.mp h
  exact ((MulAut.conj g).orderOf_eq _).trans (shortRootElement_orderOf m ht)

/-- The source's 2-central condition: an involution in a Sylow center. -/
def IsTwoCentralInvolution {m : ℕ} (x : Model m) : Prop :=
  orderOf x = 2 ∧ ∃ S : Sylow 2 (Model m), x ∈ S ∧ ∀ y ∈ S, Commute x y

end ReeF4.EvenInvolutionGeometry

end
