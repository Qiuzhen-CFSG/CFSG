module

public import Theory.SpecificGroups.ReeF4.EvenInvolutionGeometry.Roots
public import Theory.SpecificGroups.ReeF4.NormalizedRootCentralizers.CenterExponent.Layout

/-!
# Positive coordinates for the Ree center exponent calculation

Every element of the actual positive fixed subgroup has four paired parameters
and four main/central B₂ parameter pairs. The order here is the proved positive
block layout: pairs 8, 2, 6, 4, then B₂ blocks 1, 5, 7, 3 in GLS numbering.
The central parameter is the parameter of `centralWord`, including its
high-root factor; it is not the third split coordinate of the B₂ block.

Split-coordinate uniqueness forces the twist equation separately in each
block. Solving those equations and using the B₂ factorization gives the
unique factorization below, with no extra coordinate or generation hypothesis.
We also transfer centrality in the actual model to all eight literal main
root words. These are the inputs to the separate coordinate eliminations.

Source: GLS3 Table 2.4 and 2.4.5(d), `refs/KGroup/GLS3/chapter2.tex`;
Aschbacher–Smith, proof of 13.6.6, printed p.927 of `refs/quasithin.pdf`.
-/

@[expose] public section
noncomputable section

namespace ReeF4.NormalizedRootCentralizers.CenterExponent

open Parabolics LargeLocalSeeds Parabolics.RadicalCoordinates
open Parabolics.RadicalCoordinates.FixedCoordinates
open Parabolics.OuterLocal.SuzukiCommutators.NormalGeneration

/-- The twelve free parameters of the fixed positive subgroup. -/
structure PositiveParameters (m : ℕ) where
  pair : Fin 4 → CoefficientField m
  main : Fin 4 → CoefficientField m
  central : Fin 4 → CoefficientField m

/-- The first coordinate elimination: GLS curves `x₈`, `x₂`, `x₁`, `x₇`,
and `y₁` have zero parameters. This is a scalar conclusion to be proved from
centrality, not part of the definition of the positive subgroup or its center. -/
structure OuterCoordinatesZero {m : ℕ} (p : PositiveParameters m) : Prop where
  pair_eighth : p.pair 0 = 0
  pair_second : p.pair 1 = 0
  main_first : p.main 0 = 0
  main_seventh : p.main 2 = 0
  central_first : p.central 0 = 0

/-- The literal ordered word in the split carrier, with the actual Ree curves. -/
def positiveWord (m : ℕ) (p : PositiveParameters m) : SplitGroup m :=
  (List.ofFn fun j => rootWord m (positiveRootWordLayout.pairIndex j) (p.pair j)).prod *
    (List.ofFn fun j => rootWord m (positiveRootWordLayout.quartetIndex j) (p.main j) *
      centralWord m (positiveRootWordLayout.quartetIndex j) (p.central j)).prod

private def splitParameters (m : ℕ) (p : PositiveParameters m) : BlockParameters m .positive :=
  (fun j => pairSolution m (p.pair j),
    fun j => quartetSolution m (p.main j)
      (p.main j * halfFrobenius m (p.main j) + halfFrobenius m (p.central j)))

private theorem splitParameters_fixed (m : ℕ) (p : PositiveParameters m) :
    blockTwist m (splitParameters m p) = splitParameters m p := by
  apply Prod.ext
  · funext j
    exact pairSolution_fixed m _
  · funext j
    exact quartetSolution_fixed m _ _

private theorem positiveWord_eq_blockWord (m : ℕ) (p : PositiveParameters m) :
    positiveWord m p = positiveRootWordLayout.blocks.blockWord m (splitParameters m p) := by
  rw [positiveRootWordLayout.blockWord_factorization m (mixedRootCommutation m) _
    (splitParameters_fixed m p)]
  have hs (a c : CoefficientField m) :
      titsEnd m (a * halfFrobenius m a + halfFrobenius m c) + a * titsEnd m a = c := by
    simp only [map_add, map_mul, titsEnd_halfFrobenius]
    rw [mul_comm (titsEnd m a) a, add_right_comm, CharTwo.add_self_eq_zero, zero_add]
  simp only [splitParameters, pairSolution, quartetSolution, Matrix.cons_val_zero,
    Matrix.cons_val, hs, positiveWord]

/-- Unique fixed parameters in the literal main/central word convention. -/
theorem positiveWord_injective (m : ℕ) : Function.Injective (positiveWord m) := by
  intro p q h
  have he : splitParameters m p = splitParameters m q := by
    apply positiveRootWordLayout.blocks.blockWord_injective m (wordInSubgroup_bijective m _)
    simpa only [← positiveWord_eq_blockWord] using h
  have hp : p.pair = q.pair := by
    funext j
    exact congrArg (fun t : BlockParameters m .positive => t.1 j 0) he
  have hm : p.main = q.main := by
    funext j
    exact congrArg (fun t : BlockParameters m .positive => t.2 j 0) he
  have hc : p.central = q.central := by
    funext j
    have hj := congrArg (fun t : BlockParameters m .positive => t.2 j 2) he
    change p.main j * halfFrobenius m (p.main j) + halfFrobenius m (p.central j) =
      q.main j * halfFrobenius m (q.main j) + halfFrobenius m (q.central j) at hj
    rw [hm] at hj
    have hh := congrArg (titsEnd m) (add_left_cancel hj)
    simpa only [titsEnd_halfFrobenius] using hh
  cases p
  cases q
  simp_all only

/-- Both families are twist-fixed and supported on the positive roots. -/
theorem positive_words_fixed_mem (m : ℕ) (i : Fin 8) (t : CoefficientField m) :
    (reeTwist m (rootWord m i t) = rootWord m i t ∧
      rootWord m i t ∈ splitUnipotent m) ∧
    (reeTwist m (centralWord m i t) = centralWord m i t ∧
      centralWord m i t ∈ splitUnipotent m) :=
  positiveRootWordLayout.words_fixed_mem m positiveRootWordLayout.positive_covers
    (mixedRootCommutation m) (b2RootSwap m) i t

/-- Each of the eight main curves as an element of the genuine fixed group. -/
def mainElement (m : ℕ) (i : Fin 8) (t : CoefficientField m) : Model m :=
  ⟨rootWord m i t, by
    simpa only [mem_fixedSubgroup, reeAutomorphism_apply]
      using (positive_words_fixed_mem m i t).1.1⟩

@[simp] theorem mainElement_coe (m : ℕ) (i : Fin 8) (t : CoefficientField m) :
    toSplitGroup m (mainElement m i t) = rootWord m i t := toSplitGroup_apply m _

theorem mainElement_mem_unipotent (m : ℕ) (i : Fin 8) (t : CoefficientField m) :
    mainElement m i t ∈ unipotent m := by
  change toSplitGroup m (mainElement m i t) ∈ splitUnipotent m
  rw [mainElement_coe]
  exact (positive_words_fixed_mem m i t).1.2

/-- Positive fixed coordinates, without any unproved factorization premise. -/
theorem exists_positiveWord (m : ℕ) (x : Model m) (hx : x ∈ unipotent m) :
    ∃ p : PositiveParameters m, toSplitGroup m x = positiveWord m p := by
  let L := positiveRootWordLayout
  have hs := wordInSubgroup_bijective m L.blocks.order
  obtain ⟨t, ht⟩ := hs.2 ⟨toSplitGroup m x, hx⟩
  have hw : word m L.blocks.order t = toSplitGroup m x := congrArg Subtype.val ht
  have hf : reeTwist m (toSplitGroup m x) = toSplitGroup m x := by
    simpa only [toSplitGroup_apply, mem_fixedSubgroup, reeAutomorphism_apply]
      using x.property
  have hfixed : blockTwist m (L.blocks.repack m t) = L.blocks.repack m t := by
    apply L.blocks.blockWord_injective m hs
    rw [← L.blocks.twist_blockWord m (mixedRootCommutation m) (b2RootSwap m),
      ← L.blocks.word_eq_blockWord, hw, hf]
  let q := L.blocks.repack m t
  refine ⟨⟨(fun j => q.1 j 0), (fun j => q.2 j 0),
    (fun j => titsEnd m (q.2 j 2) + q.2 j 0 * titsEnd m (q.2 j 0))⟩, ?_⟩
  exact hw.symm.trans ((L.blocks.word_eq_blockWord m t).trans
    (L.blockWord_factorization m (mixedRootCommutation m) q hfixed))

/-- The factorization is unique in the main/central parameter convention. -/
theorem existsUnique_positiveWord (m : ℕ) (x : Model m) (hx : x ∈ unipotent m) :
    ∃! p : PositiveParameters m, toSplitGroup m x = positiveWord m p := by
  obtain ⟨p, hp⟩ := exists_positiveWord m x hx
  refine ⟨p, hp, ?_⟩
  intro q hq
  exact positiveWord_injective m (hq.symm.trans hp)

/-- The center hypothesis in the model implies the literal split-word
commutations used by coordinate detection. -/
theorem positiveWord_commutes_of_central (m : ℕ) (x : Model m)
    (hc : ∀ u ∈ unipotent m, Commute x u)
    (p : PositiveParameters m) (hp : toSplitGroup m x = positiveWord m p) :
    ∀ i : Fin 8, ∀ t : CoefficientField m, Commute (positiveWord m p) (rootWord m i t) := by
  intro i t
  have h := congrArg (toSplitGroup m)
    (hc (mainElement m i t) (mainElement_mem_unipotent m i t)).eq
  change positiveWord m p * rootWord m i t = rootWord m i t * positiveWord m p
  simpa only [map_mul, hp, mainElement_coe] using h

end ReeF4.NormalizedRootCentralizers.CenterExponent
