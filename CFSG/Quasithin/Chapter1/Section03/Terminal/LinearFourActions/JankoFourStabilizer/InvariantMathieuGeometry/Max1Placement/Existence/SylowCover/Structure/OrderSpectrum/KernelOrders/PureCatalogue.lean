module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.KernelOrders.Candidates
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.KernelOrders.PureCatalogue.Finite
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.Mathieu.SylowCore.Transport.Coordinates
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Involutions.Max1Fusion.KernelOrbits.Coordinates
import Mathlib.Tactic.FinCases

/-!
# The six Sylow-invariant pure subgroups of the literal J₄ kernel

The binary evaluation intertwines the four prescribed Sylow generators with
left conjugation in the matrix model. In a normalized subgroup, conjugation
and multiplication therefore preserve membership. The checked finite
certificate forces a seed conjugate from every mask outside a set of twenty.
Inside that set, recovery expressions yield one of six cyclic invariant spans;
two incompatible pairs prevent combining the incomparable spans.

This proves exhaustion under the actual ambient-fusion exclusion. Independently,
XOR-span closure and injectivity of the eleven kernel coordinates give the exact
orders of the original `candidate` subgroups, with no change of carrier or rows.
No ambient simplicity, normalizer classification, or order-spectrum premise is
used. The result discharges the catalogue input of
`smallKernelClosureOrders_of_pure_certificates`; its owner retains the separate
exceptional-normalizer calculations.

Source context: Aschbacher--Smith A.3.12, printed pp.47--48; Aschbacher (1986),
no.343; Kleidman--Wilson (1988), pp.484--510. The concrete coordinate convention
and ATLAS provenance are documented in `Image.StarData` and the imported
`SylowCore.Transport.Coordinates`. Untrusted discovery and certificate
measurements are recorded in `PureCatalogue/source`.
-/

open Subgroup Janko4 Janko4.Cardinality Janko4.Cardinality.QuotientCount.Image
open Janko4.LocalStructure.SylowCore Janko4.LocalStructure.SylowCore.Transport
open Janko4.Simplicity.Max1Fusion.QuotientInvolutions
open Janko4.Simplicity.Max1Fusion.KernelOrbits
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.KernelOrders
namespace PureCertificate
attribute [local irreducible] modelGroup matrixA matrixB max1Subgroup localKernel

lemma element_zero : maskElement 0 = 1 :=
  congrArg (fun x : localKernel matrixA_mul_self matrixB_pow_four => (x : Model))
    (maskValue_zero matrixA_mul_self matrixB_pow_four)

lemma element_xor (m n : ℕ) : maskElement (m ^^^ n) = maskElement m * maskElement n :=
  congrArg (fun x : localKernel matrixA_mul_self matrixB_pow_four => (x : Model))
    (maskValue_xor matrixA_mul_self matrixB_pow_four m n)

lemma element_inv (m : ℕ) : (maskElement m)⁻¹ = maskElement m := by
  apply inv_eq_of_mul_eq_one_right
  rw [← element_xor, Nat.xor_self, element_zero]

lemma element_injective : Function.Injective (fun m : Fin 2048 => maskElement m.val) := by
  intro m n h
  apply maskEval_injective matrixA_mul_self matrixB_pow_four
  exact Subtype.ext (Subtype.ext h)

lemma element_surjective {x : Model} (hx : x ∈ orderSpectrumKernel) :
    ∃ m : Fin 2048, maskElement m.val = x := by
  obtain ⟨x, hx, rfl⟩ := hx
  obtain ⟨m, hm⟩ := (maskEquiv matrixA_mul_self matrixB_pow_four).surjective ⟨x, hx⟩
  exact ⟨m, congrArg (fun x : localKernel matrixA_mul_self matrixB_pow_four => (x : Model)) hm⟩

lemma rows_starMask (i : Fin 4) (m : ℕ) :
    maskImage (rows i) m = starMask (sylowGenerator i) m := by
  unfold starMask
  congr 1
  funext j
  exact rows_eq i j

lemma rows_lt (i : Fin 4) (m : ℕ) : maskImage (rows i) m < 2048 := by
  rw [rows_starMask]
  exact starMask_lt _ _

lemma element_action (i : Fin 4) (m : Fin 2048) :
    maskElement (maskImage (rows i) m.val) =
    (OuterReduction.OddIndex.localSylowLift i : Model) * maskElement m.val *
      (OuterReduction.OddIndex.localSylowLift i : Model)⁻¹ := by
  rw [rows_starMask]
  have he := maskEquiv_starMask matrixA_mul_self matrixB_pow_four
    (OuterReduction.OddIndex.localSylowLift i) m
  have hp : starProjection matrixA_mul_self matrixB_pow_four
      (OuterReduction.OddIndex.localSylowLift i) = sylowGenerator i :=
    OuterReduction.OddIndex.localProjection_lift i
  rw [hp] at he
  exact congrArg (fun x : localKernel matrixA_mul_self matrixB_pow_four => (x : Model)) he

lemma action_mem (A : Subgroup Model)
    (hS : OuterReduction.OddIndex.twoSubgroup ≤ normalizer (A : Set Model))
    (i : Fin 4) {m : ℕ} (hm : m < 2048) (h : maskElement m ∈ A) :
    maskElement (maskImage (rows i) m) ∈ A := by
  rw [element_action i ⟨m, hm⟩]
  exact (mem_normalizer_iff.mp (hS (OuterReduction.OddIndex.twoGenerator_mem
    (Sum.inr i))) _).mp h

lemma word_conjugate (w : List Bool) : IsConj (maskElement (wordMask w)) classSeed := by
  induction w with
  | nil =>
    have he : maskElement 1 = classSeed :=
      congrArg (fun x : max1Subgroup matrixA_mul_self matrixB_pow_four => (x : Model))
        (maskValue_one matrixA_mul_self matrixB_pow_four)
    change IsConj (maskElement 1) classSeed
    rw [he]
  | cons b w ih =>
    have hc : IsConj (maskElement (wordMask w)) (maskElement (wordMask (b :: w))) := by
      cases b
      · apply isConj_iff.mpr
        refine ⟨(localX matrixA_mul_self matrixB_pow_four : Model)⁻¹, ?_⟩
        simpa only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv, maskElement, maskValue,
          wordMask, Bool.false_eq_true, ↓reduceIte] using
          congrArg (fun x : max1Subgroup matrixA_mul_self matrixB_pow_four => (x : Model))
          (right_conj_mask_x matrixA_mul_self matrixB_pow_four (wordMask w))
      · apply isConj_iff.mpr
        refine ⟨(localY matrixA_mul_self matrixB_pow_four : Model)⁻¹, ?_⟩
        simpa only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv, maskElement, maskValue,
          wordMask, Bool.false_eq_true, ↓reduceIte] using
          congrArg (fun x : max1Subgroup matrixA_mul_self matrixB_pow_four => (x : Model))
          (right_conj_mask_y matrixA_mul_self matrixB_pow_four (wordMask w))
    exact hc.symm.trans ih

lemma seeds_conjugate {m : ℕ} (hm : m ∈ seeds) : IsConj (maskElement m) classSeed := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hm
  have hi' : i < 22 := hi
  rw [← seed_words ⟨i, hi'⟩]
  exact word_conjugate _

lemma step_lt (s : ℕ) {m : ℕ} (hm : m < 2048) : step s m < 2048 := by
  unfold step
  split
  · exact rows_lt _ _
  · split
    · exact Nat.xor_lt_two_pow (n := 11) hm (rows_lt _ _)
    · exact hm

lemma step_mem (A : Subgroup Model)
    (hS : OuterReduction.OddIndex.twoSubgroup ≤ normalizer (A : Set Model))
    (s : ℕ) {m : ℕ} (hm : m < 2048) (h : maskElement m ∈ A) :
    maskElement (step s m) ∈ A := by
  unfold step
  split
  · exact action_mem A hS _ hm h
  · split
    · rw [element_xor]
      exact A.mul_mem h (action_mem A hS _ hm h)
    · exact h

lemma allowed_of_mem (A : Subgroup Model)
    (hS : OuterReduction.OddIndex.twoSubgroup ≤ normalizer (A : Set Model))
    (hpure : ∀ u ∈ A, ¬ IsConj u classSeed)
    {m : ℕ} (hm : m < 2048) (h : maskElement m ∈ A) : m ∈ allowed := by
  let b : Fin 32 := ⟨m / 64, by omega⟩
  let i : Fin 64 := ⟨m % 64, Nat.mod_lt _ (by decide)⟩
  have he : 64 * b.val + i.val = m := by dsimp [b, i]; omega
  have hc := certificate b i
  change _ ∈ allowed ∨ _ ∈ seeds at hc
  rw [he] at hc
  rcases hc with hc | hc
  · exact hc
  · exact (hpure _ (step_mem A hS _ (step_lt _ hm) (step_mem A hS _ hm h))
      (seeds_conjugate hc)).elim

lemma evaluate_lt {m : ℕ} (hm : m < 2048) (e : Expression) : evaluate m e < 2048 := by
  induction e with
  | source => exact hm
  | xor e f he hf => exact Nat.xor_lt_two_pow (n := 11) he hf
  | act i e _ => exact rows_lt i _

lemma evaluate_mem (A : Subgroup Model)
    (hS : OuterReduction.OddIndex.twoSubgroup ≤ normalizer (A : Set Model))
    {m : ℕ} (hm : m < 2048) (h : maskElement m ∈ A) (e : Expression) :
    maskElement (evaluate m e) ∈ A := by
  induction e with
  | source => exact h
  | xor e f he hf =>
    change maskElement (evaluate m e ^^^ evaluate m f) ∈ A
    rw [element_xor]
    exact A.mul_mem he hf
  | act i e he => exact action_mem A hS i (evaluate_lt hm e) he

lemma representatives_lt : ∀ i, representatives i < 2048 := by decide +kernel

lemma rows_eq_candidates : basisRows = candidateRows := rfl

lemma candidate_le_of_representative (A : Subgroup Model)
    (hS : OuterReduction.OddIndex.twoSubgroup ≤ normalizer (A : Set Model))
    (i : Fin 6) (h : maskElement (representatives i) ∈ A) : candidate i ≤ A := by
  apply (closure_le _).mpr
  rintro _ ⟨m, hm, rfl⟩
  change m ∈ candidateRows i at hm
  rw [← rows_eq_candidates, ← lower_certificate i] at hm
  obtain ⟨e, _, rfl⟩ := List.mem_map.mp hm
  exact evaluate_mem A hS (representatives_lt i) h e

lemma xorSpan_mem (A : Subgroup Model) (rs : List ℕ)
    (hrs : ∀ m ∈ rs, maskElement m ∈ A) : ∀ m ∈ xorSpan rs, maskElement m ∈ A := by
  induction rs with
  | nil =>
    intro m hm
    obtain rfl : m = 0 := List.mem_singleton.mp hm
    rw [element_zero]
    exact A.one_mem
  | cons x xs ih =>
    intro m hm
    have hx := hrs x (by simp)
    have ht := ih (fun y hy => hrs y (by simp [hy]))
    rcases List.mem_append.mp hm with hm | hm
    · exact ht m hm
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hm
      rw [element_xor]
      exact A.mul_mem hx (ht y hy)

lemma span_mem_candidate (i : Fin 6) {m : ℕ} (hm : m ∈ spanMasks i) :
    maskElement m ∈ candidate i := by
  apply xorSpan_mem (candidate i) (basisRows i) _ m hm
  intro n hn
  apply Subgroup.subset_closure
  exact ⟨n, rows_eq_candidates ▸ hn, rfl⟩

lemma mem_candidate_iff (i : Fin 6) (x : Model) :
    x ∈ candidate i ↔ ∃ m ∈ spanMasks i, maskElement m = x := by
  constructor
  · intro hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨m, hm, rfl⟩ := hx
      exact ⟨m, span_rows i m (by simpa only [rows_eq_candidates, Set.mem_ofPred_eq] using hm), rfl⟩
    | one => exact ⟨0, span_zero i, element_zero⟩
    | mul x y _ _ hx hy =>
      obtain ⟨m, hm, rfl⟩ := hx
      obtain ⟨n, hn, rfl⟩ := hy
      exact ⟨m ^^^ n, span_xor i m hm n hn, element_xor m n⟩
    | inv x _ hx =>
      obtain ⟨m, hm, rfl⟩ := hx
      exact ⟨m, hm, (element_inv m).symm⟩
  · rintro ⟨m, hm, rfl⟩
    exact span_mem_candidate i hm

lemma candidate_card (i : Fin 6) : Nat.card (candidate i) = 2 ^ (candidateRows i).length := by
  let f : {m // m ∈ (spanMasks i).toFinset} → candidate i := fun m =>
    ⟨maskElement m.val, span_mem_candidate i (List.mem_toFinset.mp m.property)⟩
  have hf : Function.Bijective f := by
    constructor
    · intro m n h
      have he := congrArg Subtype.val h
      have hh : (⟨m.val, span_lt i _ (List.mem_toFinset.mp m.property)⟩ : Fin 2048) =
          ⟨n.val, span_lt i _ (List.mem_toFinset.mp n.property)⟩ := element_injective he
      exact Subtype.ext (congrArg Fin.val hh)
    · intro x
      obtain ⟨m, hm, he⟩ := (mem_candidate_iff i x.val).mp x.property
      exact ⟨⟨m, List.mem_toFinset.mpr hm⟩, Subtype.ext he⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_eq_fintype_card, Fintype.card_coe,
    span_card, rows_eq_candidates]

def below : Fin 6 → List (Fin 6) :=
  ![[0], [0, 1], [0, 1, 2], [0, 1, 2, 3], [0, 1, 2, 4], [0, 1, 2, 4, 5]]

lemma span_inclusion : ∀ i k, i ∈ below k → spanMasks i ⊆ spanMasks k := by
  decide +kernel

lemma select_span (P : ℕ → Prop) (h0 : P 0)
    (h35 : ¬ (P (representatives 3) ∧ P (representatives 5)))
    (h34 : ¬ (P (representatives 3) ∧ P (representatives 4))) :
    ∃ k : Fin 6, P (representatives k) ∧ ∀ i, P (representatives i) → i ∈ below k := by
  classical
  by_cases h5 : P (representatives 5)
  · refine ⟨5, h5, ?_⟩
    intro i hi
    fin_cases i <;> first | exact (h35 ⟨hi, h5⟩).elim | decide
  by_cases h3 : P (representatives 3)
  · refine ⟨3, h3, ?_⟩
    intro i hi
    fin_cases i <;> first | exact (h5 hi).elim | exact (h34 ⟨h3, hi⟩).elim | decide
  by_cases h4 : P (representatives 4)
  · refine ⟨4, h4, ?_⟩
    intro i hi
    fin_cases i <;> first | exact (h5 hi).elim | exact (h3 hi).elim | decide
  by_cases h2 : P (representatives 2)
  · refine ⟨2, h2, ?_⟩
    intro i hi
    fin_cases i <;> first
    | exact (h5 hi).elim
    | exact (h3 hi).elim
    | exact (h4 hi).elim
    | decide
  by_cases h1 : P (representatives 1)
  · refine ⟨1, h1, ?_⟩
    intro i hi
    fin_cases i <;> first
    | exact (h5 hi).elim
    | exact (h3 hi).elim
    | exact (h4 hi).elim
    | exact (h2 hi).elim
    | decide
  refine ⟨0, h0, ?_⟩
  intro i hi
  fin_cases i <;> first
  | exact (h5 hi).elim
  | exact (h3 hi).elim
  | exact (h4 hi).elim
  | exact (h2 hi).elim
  | exact (h1 hi).elim
  | decide

lemma recover_mem (A : Subgroup Model)
    (hS : OuterReduction.OddIndex.twoSubgroup ≤ normalizer (A : Set Model))
    {m : ℕ} (hm : m < 2048) (ha : m ∈ allowed) (h : maskElement m ∈ A) :
    ∃ i : Fin 6, maskElement (representatives i) ∈ A ∧ m ∈ spanMasks i := by
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp ha
  have hj' : j < 20 := hj
  have hc := recovery_certificate ⟨j, hj'⟩
  refine ⟨recoveryTag ⟨j, hj'⟩, ?_, hc.2⟩
  rw [← hc.1]
  exact evaluate_mem A hS hm h _

lemma exhaustion (A : Subgroup Model) (hAK : A ≤ orderSpectrumKernel)
    (hS : OuterReduction.OddIndex.twoSubgroup ≤ normalizer (A : Set Model))
    (hpure : ∀ u ∈ A, ¬ IsConj u classSeed) : ∃ i : Fin 6, A = candidate i := by
  have hs {m : ℕ} : m < 2048 → maskElement m ∈ A → m ∈ allowed :=
    allowed_of_mem A hS hpure
  have h35 : ¬ (maskElement (representatives 3) ∈ A ∧
      maskElement (representatives 5) ∈ A) := by
    rintro ⟨h3, h5⟩
    have hx : maskElement (571 ^^^ 370) ∈ A := by
      rw [element_xor]
      exact A.mul_mem h3 h5
    exact (by decide +kernel : 571 ^^^ 370 ∉ allowed) (hs (by decide) hx)
  have h34 : ¬ (maskElement (representatives 3) ∈ A ∧
      maskElement (representatives 4) ∈ A) := by
    rintro ⟨h3, h4⟩
    have hx : maskElement (571 ^^^ 821) ∈ A := by
      rw [element_xor]
      exact A.mul_mem h3 h4
    exact (by decide +kernel : 571 ^^^ 821 ∉ allowed) (hs (by decide) hx)
  obtain ⟨k, hk, hindices⟩ := select_span (fun m => maskElement m ∈ A)
    (by simpa only [element_zero] using A.one_mem) h35 h34
  refine ⟨k, le_antisymm ?_ (candidate_le_of_representative A hS k hk)⟩
  intro x hx
  obtain ⟨m, rfl⟩ := element_surjective (hAK hx)
  obtain ⟨i, hi, hm⟩ := recover_mem A hS m.isLt (hs m.isLt hx) hx
  exact span_mem_candidate k ((span_inclusion i k (hindices i hi)) hm)

end PureCertificate

/-- Exhaustion and orders for the six literal Sylow-invariant all-2A kernel subgroups. -/
public theorem pureKernelCatalogue : PureKernelCatalogue :=
  ⟨PureCertificate.exhaustion, PureCertificate.candidate_card⟩
end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.KernelOrders
