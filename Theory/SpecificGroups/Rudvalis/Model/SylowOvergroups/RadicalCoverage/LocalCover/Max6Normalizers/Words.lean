module

public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.Max6Normalizers.AlignmentData

/-!
# The recorded Rudvalis max6 conjugator

The word is exactly LocalCover/source/Conjugator.json, with letters a, b,
a⁻¹, b⁻¹ encoded by 0, 1, 2, 3. We invert its product when using MulAut.conj:
GAP z^g means g⁻¹ z g, whereas Lean's conjugation by k means k z k⁻¹.
The tenth power of the first max6 generator has order two and belongs to max6.
Its conjugate is proved equal to the marked generator of elementary 0.

All pointwise equations are kernel reductions on the original degree-4060
carrier. The checked caches in WordData avoid expanding the max4 words at
every occurrence. No normalizer bound or ambient order is inferred here.

Source: the preserved ATLAS words attributed in SylowOvergroups.Definitions;
the conjugator is the independently discovered word in Conjugator.json.
The intended local application is [Asc86b], as cited in Aschbacher--Smith,
printed p.511, and GLS3 Table 5.3r.
-/

namespace Rudvalis.SylowOvergroups.RadicalCoverage.LocalCover.Max6Certificate

set_option maxRecDepth 30000
set_option Elab.async false

/-- The recorded GAP word, with its signed letters translated without reordering. -/
@[expose] public def gapWord : List (Fin 4) :=
  [3, 2, 3, 3, 2, 1, 2, 3, 3, 2, 3, 3, 2, 1, 1, 0, 0, 0, 1, 0, 1, 0, 1, 2,
    3, 2, 3, 2, 3, 2, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 3, 0, 3,
    0, 3, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 1, 1, 1,
    1, 1, 0, 0, 0, 1, 0, 1, 2, 3, 2, 3, 3, 2, 3, 2, 3, 2, 3, 2, 1, 2, 3, 2,
    1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 1, 2, 3, 2, 3, 2, 3, 2, 1, 0, 1, 1, 0, 1,
    1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 0, 1, 2, 3,
    2, 3, 3, 2, 3, 2, 3, 2, 3, 2, 1, 1, 1, 0, 3, 0, 1, 1, 0, 1, 0, 1, 2, 1,
    2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 3, 0, 3,
    0, 3, 0, 3, 3, 2, 1, 2, 1, 2, 1, 2, 3, 3, 2, 3, 2, 3, 2, 3, 2]

/-- Evaluate the original recorded word on the preserved standard generators. -/
@[expose] public def gapConjugator : Model :=
  (gapWord.map (![a, b, a⁻¹, b⁻¹] : Fin 4 → Model)).prod

/-- The inverse word gives the same conjugation in Lean's left-action convention. -/
@[expose] public def conjugator : Model := gapConjugator⁻¹

/-- The explicit involution singled out by the max6 program.
Its full ambient centralizer bound is a separate certificate. -/
@[expose] public def centralInvolution : Model := max6Generators.1 ^ 10

public theorem centralInvolution_mem_max6 : centralInvolution ∈ max6 :=
  max6.pow_mem (Subgroup.subset_closure (Set.mem_insert _ _)) 10

private def blockPoint (b : ℕ) (j : Fin 1024) : Fin 4060 :=
  ⟨(1024 * b + j.val) % 4060, Nat.mod_lt _ (by decide)⟩

private def gapCorrect (b : ℕ) : Prop :=
  ∀ j : Fin 1024, gapConjugator.val (blockPoint b j) =
    AlignmentData.gapPerm (blockPoint b j)

private theorem gapCorrect0 : gapCorrect 0 := by
  unfold gapCorrect
  decide +kernel
private theorem gapCorrect1 : gapCorrect 1 := by
  unfold gapCorrect
  decide +kernel
private theorem gapCorrect2 : gapCorrect 2 := by
  unfold gapCorrect
  decide +kernel
private theorem gapCorrect3 : gapCorrect 3 := by
  unfold gapCorrect
  decide +kernel

/-- The recorded word has the checked point map, with four bounded kernel checks. -/
public theorem gapConjugator_val : gapConjugator.val = AlignmentData.gapPerm := by
  apply Equiv.ext
  intro i
  let j : Fin 1024 := ⟨i.val % 1024, Nat.mod_lt _ (by decide)⟩
  have hpoint : blockPoint (i.val / 1024) j = i := by
    apply Fin.ext
    simp only [blockPoint, j]
    rw [Nat.div_add_mod, Nat.mod_eq_of_lt i.isLt]
  have hcases : i.val / 1024 = 0 ∨ i.val / 1024 = 1 ∨
      i.val / 1024 = 2 ∨ i.val / 1024 = 3 := by omega
  have h : gapConjugator.val (blockPoint (i.val / 1024) j) =
      AlignmentData.gapPerm (blockPoint (i.val / 1024) j) := by
    rcases hcases with hi | hi | hi | hi
    · rw [hi]; exact gapCorrect0 j
    · rw [hi]; exact gapCorrect1 j
    · rw [hi]; exact gapCorrect2 j
    · rw [hi]; exact gapCorrect3 j
  exact hpoint ▸ h

/-- The involution table is certified against the original max6 word. -/
public theorem centralInvolution_val :
    centralInvolution.val = AlignmentData.involutionPerm := by
  apply Equiv.ext
  apply Rudvalis.Data.allFin
  decide +kernel

/-- The marked local generator table is certified through the checked word cache. -/
public theorem elementary_zero_val :
    (elementaryGenerator 0).val = AlignmentData.zeroPerm := by
  rw [WordData.elementaryGenerator_eq_cached]
  apply Equiv.ext
  apply Rudvalis.Data.allFin
  decide +kernel

public theorem centralInvolution_sq : centralInvolution ^ 2 = 1 := by
  apply Subtype.ext
  change centralInvolution.val ^ 2 = (1 : Equiv.Perm (Fin 4060))
  rw [centralInvolution_val]
  apply Equiv.ext
  apply Rudvalis.Data.allFin
  decide +kernel

public theorem centralInvolution_ne_one : centralInvolution ≠ 1 := by
  intro h
  have hn : centralInvolution • (0 : Fin 4060) ≠ 0 := by decide +kernel
  exact hn (congrArg (fun g : Model => g • (0 : Fin 4060)) h)

public theorem centralInvolution_order : orderOf centralInvolution = 2 :=
  orderOf_eq_prime centralInvolution_sq centralInvolution_ne_one

/-- Kernel-certified alignment of the recorded GAP word with the actual local word. -/
public theorem conjugator_alignment :
    MulAut.conj conjugator centralInvolution = elementaryGenerator 0 := by
  apply Subtype.ext
  change gapConjugator.val⁻¹ * centralInvolution.val * gapConjugator.val =
    (elementaryGenerator 0).val
  rw [gapConjugator_val, centralInvolution_val, elementary_zero_val]
  apply Equiv.ext
  apply Rudvalis.Data.allFin
  decide +kernel

public theorem elementary_zero_order : orderOf (elementaryGenerator 0) = 2 := by
  rw [← conjugator_alignment, MulEquiv.orderOf_eq, centralInvolution_order]

end Rudvalis.SylowOvergroups.RadicalCoverage.LocalCover.Max6Certificate
