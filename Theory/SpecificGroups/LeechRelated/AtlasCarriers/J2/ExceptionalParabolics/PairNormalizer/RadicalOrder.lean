module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.PairNormalizer.RadicalData
public import Theory.PGroupCore
import Mathlib.Tactic.FinCases

/-!
# Order of the fixed second Hall--Janko radical

The 64 table permutations are compared with short words in the actual six
Seed generators. Checked transitions for generators and their inverses prove
coverage by subgroup induction. Evaluation at points 0 and 1 distinguishes the
64 words, giving an equivalence with `Fin 64` and the two-group property.

The witness generator is `source/enumerate.py`. Only the kernel-checked
identities below are used in the proof. Source: GLS3, Table 5.3g, for the
radical of the local normalizer in the degree-100 ATLAS `J2G1-p100B0` carrier.
-/

@[expose] public section
namespace Sporadic.LeechRelated.J2.ExceptionalParabolics.PairNormalizer
open Theory.GroupTheory GeneratorPair Seed RadicalData
open GeneratorPair.SecondOrbitCertificate

private theorem inclusion_localWord (w : List (Fin 3)) :
    inclusion (localWord w) = evalWord ![tableA, tableB, tableB⁻¹] w := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    change inclusion (![a, b, b⁻¹] i * localWord w) = _
    rw [map_mul, ih]
    congr 1
    fin_cases i <;> simp [a, b, inclusion, generatorA_eq_table, generatorB_eq_table]

set_option maxRecDepth 100000 in
private theorem qGen_word_check : ∀ i,
    evalWord ![tableA, tableB, tableB⁻¹] (q₂Words i) = qGenTable i := by
  apply allFin
  decide +kernel

/-- Comparison of the fixed radical generators with their checked tables. -/
theorem q₂Generator_inclusion (i : Fin 6) :
    inclusion (q₂Generator i) = qGenTable i := by
  exact (inclusion_localWord (q₂Words i)).trans (qGen_word_check i)

set_option maxRecDepth 100000 in
private theorem qTable_word_check : ∀ i, evalWord qGenTable (qWord i) = qTable i := by
  apply allFin
  decide +kernel

set_option maxRecDepth 100000 in
private theorem qTable_step_check : ∀ j i, qGenTable j * qTable i = qTable (qStep j i) := by
  apply allFin
  decide +kernel

set_option maxRecDepth 100000 in
private theorem qTable_invStep_check : ∀ j i,
    (qGenTable j)⁻¹ * qTable i = qTable (qInvStep j i) := by
  apply allFin
  decide +kernel

set_option maxRecDepth 100000 in
private theorem qKey_decode : ∀ i, qDecode (qKey i) = i := by
  apply allFin
  decide +kernel

/-- Enumerated elements are literal words in the fixed radical generators. -/
def qElement (i : Fin 64) : Carrier := evalWord q₂Generator (qWord i)

/-- The finite table attached to each actual radical element. -/
theorem qElement_inclusion (i : Fin 64) : inclusion (qElement i) = qTable i := by
  have hw (w : List (Fin 6)) : inclusion (evalWord q₂Generator w) = evalWord qGenTable w := by
    induction w with
    | nil => exact map_one inclusion
    | cons j w ih => rw [evalWord, map_mul, q₂Generator_inclusion, ih, evalWord]
  exact (hw (qWord i)).trans (qTable_word_check i)

/-- Every enumerated word belongs to the unchanged Seed subgroup. -/
theorem qElement_mem (i : Fin 64) : qElement i ∈ q₂ := by
  have hw (w : List (Fin 6)) : evalWord q₂Generator w ∈ q₂ := by
    induction w with
    | nil => exact q₂.one_mem
    | cons j w ih => exact q₂.mul_mem (Subgroup.subset_closure ⟨j, rfl⟩) ih
  exact hw (qWord i)

/-- The finite word list covers the radical. -/
theorem exists_qElement {x : Carrier} (hx : x ∈ q₂) : ∃ i, qElement i = x := by
  induction hx using Subgroup.closure_induction_left with
  | one => exact ⟨0, rfl⟩
  | mul_left x hx y hy ih =>
    obtain ⟨j, rfl⟩ := hx
    obtain ⟨i, rfl⟩ := ih
    refine ⟨qStep j i, inclusion_injective ?_⟩
    rw [map_mul, qElement_inclusion, qElement_inclusion, q₂Generator_inclusion]
    exact (qTable_step_check j i).symm
  | inv_mul_cancel x hx y hy ih =>
    obtain ⟨j, rfl⟩ := hx
    obtain ⟨i, rfl⟩ := ih
    refine ⟨qInvStep j i, inclusion_injective ?_⟩
    rw [map_mul, map_inv, qElement_inclusion, qElement_inclusion, q₂Generator_inclusion]
    exact (qTable_invStep_check j i).symm

/-- Distinct entries represent distinct actual group elements. -/
theorem qElement_injective : Function.Injective qElement := by
  intro i j hij
  have h := congrArg inclusion hij
  rw [qElement_inclusion, qElement_inclusion] at h
  have hk : qKey i = qKey j :=
    congrArg (fun p : Equiv.Perm (Fin 100) => 100 * (p 0).val + (p 1).val) h
  exact (qKey_decode i).symm.trans ((congrArg qDecode hk).trans (qKey_decode j))

/-- A certified enumeration of the radical candidate. -/
noncomputable def q₂EquivFin : q₂ ≃ Fin 64 :=
  (Equiv.ofBijective (fun i => (⟨qElement i, qElement_mem i⟩ : q₂))
    ⟨fun _ _ h => qElement_injective (congrArg Subtype.val h),
      fun x => by
        obtain ⟨i, hi⟩ := exists_qElement x.property
        exact ⟨i, Subtype.ext hi⟩⟩).symm

/-- The fixed radical candidate has order 64. -/
theorem card_q₂ : Nat.card q₂ = 64 := by
  simpa using Nat.card_congr q₂EquivFin

/-- In particular the fixed radical is a two-group. -/
theorem q₂_isPGroup : IsPGroup 2 q₂ :=
  IsPGroup.of_card (n := 6) card_q₂

end Sporadic.LeechRelated.J2.ExceptionalParabolics.PairNormalizer
