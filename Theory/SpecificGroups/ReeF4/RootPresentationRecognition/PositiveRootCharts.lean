module
public import Theory.SpecificGroups.ReeF4.RootPresentationRecognition.PositiveTables
public import Theory.SpecificGroups.ReeF4.CentralCovers.TwoPrimary.TailRelations.BaseIntervals

-- Internal bridge for the hidden layout body; only its equations are exported.
import all Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.SuzukiCommutators.NormalGeneration.FixedRootFactorization.RootAlignment

/-!
# All eight positive Ree field charts and their whole root groups

The literal split words identify the pair and quartet charts of PositiveTables
with the existing angular root subgroups. Their field charts are bijective.
The multiplication law is additive for every pair and has the same Tits cocycle
for every quartet, including at field two. These bridges allow the angular
collector to use whole root groups while retaining the actual field parameters.

Source: GLS3 Table 2.4 and 2.4.5(d), `refs/KGroup/GLS3/chapter2.tex`.
The private layout equation intentionally reads the existing implementation
body in this extension, without changing its public boundary.
-/

@[expose] public noncomputable section
namespace ReeF4.RootPresentationRecognition.PositiveTables
open Parabolics RadicalCoordinates FixedCoordinates
open CentralCovers.TwoPrimary
open ElementaryTwoBound ElementaryTwoBound.RootCalculations
open NormalizedRootCentralizers.CenterExponent
open Parabolics.OuterLocal.SuzukiCommutators.NormalGeneration
open LocalBlockInput.PairRigidity.LocalIndices.SuzukiGaussData
variable {m : ℕ}

private theorem layout_blocks : positiveRootWordLayout.blocks = rootBlocks .positive := rfl
private theorem index_pair (i : Fin 4) : rootIndex (.inl i) = positiveRootWordLayout.pairIndex i := rfl
private theorem index_quartet (i : Fin 4) : rootIndex (.inr i) = positiveRootWordLayout.quartetIndex i := rfl
private theorem cancel_parameter (t u : CoefficientField m) :
    titsEnd m (t * halfFrobenius m t + halfFrobenius m u) + t * titsEnd m t = u := by
  rw [map_add, map_mul, titsEnd_halfFrobenius, titsEnd_halfFrobenius,
    mul_comm (titsEnd m t), add_right_comm, CharTwo.add_self_eq_zero, zero_add]

theorem pair_main (i : Fin 4) (t : CoefficientField m) :
    (pair m i t : Model m) = mainElement m (rootIndex (.inl i)) t := by
  apply toSplitGroup_injective m
  rw [pair_split, mainElement_coe]
  simpa only [layout_blocks, index_pair] using
    (positiveRootWordLayout.pair_rootWord m i t).symm

theorem quartet_blockPoint (i : Fin 4) (t u : CoefficientField m) :
    (quartet m i t u : Model m) = blockPoint m (rootIndex (.inr i)) t u := by
  apply toSplitGroup_injective m
  rw [quartet_split]
  have hs : quartetParameters t u =
      quartetSolution m t (t * halfFrobenius m t + halfFrobenius m u) := by
    ext j
    fin_cases j
    · rfl
    · rfl
    · rfl
    · exact (cancel_parameter t u).symm
  rw [hs]
  have hc := positiveRootWordLayout.quartet_factorization m (mixedRootCommutation m) i
    t (t * halfFrobenius m t + halfFrobenius m u)
  rw [cancel_parameter] at hc
  simpa only [blockPoint, map_mul, mainElement_coe, centralElement_coe,
    layout_blocks, index_quartet] using hc

/-- Each entire native relative root is covered by its one or two field coordinates. -/
def rootChart (i : Root) : Parameter m i → ElementaryTwoBound.X m (rootIndex i)
  | a => ⟨root m i a, by
      cases i with
      | inl j =>
        change (pair m j a : Model m) ∈ _
        rw [pair_main]
        exact mainElement_mem_X m _ _
      | inr j =>
        change (quartet m j a.1 a.2 : Model m) ∈ _
        rw [quartet_blockPoint]
        exact (mem_X_even m _ (positiveRootWordLayout.quartet_even j) _).mpr ⟨_,_,rfl⟩⟩

@[simp] theorem rootChart_coe (i : Root) (a : Parameter m i) :
    (rootChart i a : Model m) = (root m i a : Model m) := rfl

theorem root_injective (i : Root) : Function.Injective (root m i) := by
  intro a b hab
  have he : single i a = single i b := (product_bijective m).injective (by
    simpa only [product_single] using hab)
  cases i with
  | inl j => simpa [single] using congrArg (fun p : Parameters m => p.1 j) he
  | inr j =>
    apply Prod.ext
    · simpa [single] using congrArg (fun p : Parameters m => p.2 j 0) he
    · simpa [single] using congrArg (fun p : Parameters m => p.2 j 1) he

theorem rootChart_bijective (i : Root) : Function.Bijective (rootChart (m := m) i) := by
  refine ⟨?_, ?_⟩
  · intro a b hab
    apply root_injective i
    exact Subtype.ext (congrArg (fun z : ElementaryTwoBound.X m (rootIndex i) => (z : Model m)) hab)
  · intro a
    cases i with
    | inl j =>
      obtain ⟨t, ht⟩ := (mem_X_iff m _ (positiveRootWordLayout.pair_odd j) _).mp a.property
      exact ⟨t, Subtype.ext ((pair_main j t).trans ht)⟩
    | inr j =>
      obtain ⟨t, u, ht⟩ := (mem_X_even m _ (positiveRootWordLayout.quartet_even j) _).mp a.property
      exact ⟨(t,u), Subtype.ext ((quartet_blockPoint j t u).trans ht)⟩

def rootChartEquiv (m : ℕ) (i : Root) : Parameter m i ≃ ElementaryTwoBound.X m (rootIndex i) :=
  Equiv.ofBijective _ (rootChart_bijective i)

@[simp] theorem rootChartEquiv_apply (i : Root) (a : Parameter m i) :
    (rootChartEquiv m i a : Model m) = (root m i a : Model m) := rfl

theorem pair_mul (i : Fin 4) (a b : CoefficientField m) :
    pair m i a * pair m i b = pair m i (a+b) := by
  apply Subtype.ext
  simpa only [Subgroup.coe_mul, pair_main, index_pair] using
    (mainElement_add m _ (positiveRootWordLayout.pair_odd i) a b).symm

theorem quartet_mul (i : Fin 4) (t u v w : CoefficientField m) :
    quartet m i t u * quartet m i v w = quartet m i (t+v) (u+w+titsEnd m t*v) := by
  apply Subtype.ext
  simpa only [Subgroup.coe_mul, quartet_blockPoint, index_quartet, add_comm (titsEnd m t * v)] using
    blockPoint_mul m _ (positiveRootWordLayout.quartet_even i) t u v w

end ReeF4.RootPresentationRecognition.PositiveTables
