module

public import CFSG.Quasithin.ChapterB.Section03.Offenders.Defs
public import CFSG.Quasithin.ChapterB.Section03.Offenders.FixedTests
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Six.Representatives
import Mathlib.FieldTheory.Finiteness
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases

/-!
# Fixed dimensions of the degree-six representatives

We calculate the fixed spaces in the full, deleted, core, and natural binary
permutation modules for each representative in B.3.2. The quotient calculations
retain constant displacements; these give additional deleted fixed vectors for
the triple-transposition and twisted Klein-four groups.

Every vector modulo constants has a unique representative whose last coordinate
is zero. Normalization preserves the core because the degree is even. Explicit
bijections identify each fixed space with a subset of the 64 binary vectors.
Kernel-checked finite cardinality certificates, the cardinality formula for a
finite vector space, and rank-nullity give the dimensions and codimensions.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
1 March 2004 manuscript, printed pp. 83–85, B.3.2 and B.3.4.
-/

open BinaryPermutation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.Offenders.Six

private abbrev Vec := Full (Fin 6)
private abbrev F := ZMod 2
private def fullTest (T : Finset Perm) (v : Vec) : Prop :=
  ∀ g ∈ T, ∀ i, v (g.symm i) = v i
private def quotTest (T : Finset Perm) (v : Vec) : Prop :=
  ∀ g ∈ T, ∃ c : F, ∀ i, v (g.symm i) - v i = c
private instance (T : Finset Perm) (v : Vec) : Decidable (fullTest T v) :=
  Finset.decidableDforallFinset
private instance (T : Finset Perm) (v : Vec) : Decidable (quotTest T v) :=
  Finset.decidableDforallFinset

private theorem full_test (T : Finset Perm) (v : Vec) :
    v ∈ fixedSpace (representation (Fin 6)) (Subgroup.closure (T : Set Perm)) ↔
      fullTest T v := by
  simp only [mem_fixedSpace_closure_iff, fullTest, funext_iff, representation_apply,
    Finset.mem_coe]

private theorem deleted_test (T : Finset Perm) (v : Vec) :
    (constants (Fin 6)).mkQ v ∈
      fixedSpace (deletedRepresentation (Fin 6)) (Subgroup.closure (T : Set Perm)) ↔
      quotTest T v := by
  simp only [mem_fixedSpace_closure_iff, deleted_fixed_iff, quotTest, Finset.mem_coe]

private theorem normalized_injective (v w : Vec) (hv : v 5 = 0) (hw : w 5 = 0)
    (h : (constants (Fin 6)).mkQ v = (constants (Fin 6)).mkQ w) : v = w := by
  obtain ⟨c, hc⟩ := (mem_constants_iff (v - w)).mp ((Submodule.Quotient.eq _).mp h)
  have hc0 : c = 0 := by simpa [hv, hw] using (hc 5).symm
  funext i
  exact sub_eq_zero.mp ((hc i).trans hc0)

private def normalize (v : Vec) : Vec := v - v 5 • allOne (Fin 6)
private theorem normalize_last (v : Vec) : normalize v 5 = 0 := by
  simp [normalize, allOne]
private theorem normalize_mk (v : Vec) :
    (constants (Fin 6)).mkQ (normalize v) = (constants (Fin 6)).mkQ v := by
  apply (Submodule.Quotient.eq _).mpr
  change v - v 5 • allOne (Fin 6) - v ∈ constants (Fin 6)
  rw [sub_sub_cancel_left]
  exact Submodule.neg_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
private theorem normalize_core (v : Vec) (hv : v ∈ core (Fin 6)) :
    normalize v ∈ core (Fin 6) := by
  apply Submodule.sub_mem _ hv
  apply ((constants_le_core_iff (Fin 6)).mpr (by decide))
  exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))

private noncomputable def fullEquiv (T : Finset Perm) :
    {v : Vec // fullTest T v} ≃
      fixedSpace (representation (Fin 6)) (Subgroup.closure (T : Set Perm)) :=
  Equiv.subtypeEquivRight (fun v => (full_test T v).symm)

private noncomputable def coreEquiv (T : Finset Perm) :
    {v : Vec // (∑ i, v i) = 0 ∧ fullTest T v} ≃
      fixedSpace (coreRepresentation (Fin 6)) (Subgroup.closure (T : Set Perm)) where
  toFun v := ⟨⟨v.val, v.property.1⟩, by
    rw [mem_core_fixedSpace_iff, ← mem_full_fixedSpace_iff, full_test]
    exact v.property.2⟩
  invFun v := ⟨v.val.val, v.val.property, by
    rw [← full_test, mem_full_fixedSpace_iff, ← mem_core_fixedSpace_iff]
    exact v.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

private noncomputable def deletedEquiv (T : Finset Perm) :
    {v : Vec // v 5 = 0 ∧ quotTest T v} ≃
      fixedSpace (deletedRepresentation (Fin 6)) (Subgroup.closure (T : Set Perm)) := by
  let f : {v : Vec // v 5 = 0 ∧ quotTest T v} →
      fixedSpace (deletedRepresentation (Fin 6)) (Subgroup.closure (T : Set Perm)) :=
    fun v => ⟨(constants (Fin 6)).mkQ v.val, (deleted_test T v.val).mpr v.property.2⟩
  apply Equiv.ofBijective f
  constructor
  · intro v w h
    apply Subtype.ext
    exact normalized_injective _ _ v.property.1 w.property.1 (congrArg Subtype.val h)
  · intro q
    obtain ⟨v, hv⟩ := (constants (Fin 6)).mkQ_surjective q.val
    refine ⟨⟨normalize v, normalize_last v, ?_⟩, ?_⟩
    · rw [← deleted_test, normalize_mk, hv]
      exact q.property
    · apply Subtype.ext
      exact (normalize_mk v).trans hv

private noncomputable def naturalEquiv (T : Finset Perm) :
    {v : Vec // v 5 = 0 ∧ (∑ i, v i) = 0 ∧ quotTest T v} ≃
      fixedSpace (naturalRepresentation (Fin 6)) (Subgroup.closure (T : Set Perm)) := by
  let f : {v : Vec // v 5 = 0 ∧ (∑ i, v i) = 0 ∧ quotTest T v} →
      fixedSpace (naturalRepresentation (Fin 6)) (Subgroup.closure (T : Set Perm)) :=
    fun v => ⟨⟨(constants (Fin 6)).mkQ v.val, ⟨v.val, v.property.2.1, rfl⟩⟩, by
      rw [mem_fixedSpace_iff]
      intro g hg
      apply Subtype.ext
      exact (mem_fixedSpace_iff _ _ _).mp ((deleted_test T v.val).mpr v.property.2.2) g hg⟩
  apply Equiv.ofBijective f
  constructor
  · intro v w h
    apply Subtype.ext
    exact normalized_injective _ _ v.property.1 w.property.1
      (congrArg (fun x => x.val.val) h)
  · intro q
    obtain ⟨v, hv, he⟩ := q.val.property
    refine ⟨⟨normalize v, normalize_last v, normalize_core v hv, ?_⟩, ?_⟩
    · rw [← deleted_test, normalize_mk, he, mem_fixedSpace_iff]
      intro g hg
      exact congrArg Subtype.val ((mem_fixedSpace_iff _ _ _).mp q.property g hg)
    · apply Subtype.ext
      apply Subtype.ext
      exact (normalize_mk v).trans he

private theorem finrank_of_count {V : Type*} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] {P : Vec → Prop} [DecidablePred P]
    (e : {v // P v} ≃ V) (d : ℕ) (h : Fintype.card {v // P v} = 2 ^ d) :
    Module.finrank F V = d := by
  have hc := Module.natCard_eq_pow_finrank (K := F) (V := V)
  have he := Nat.card_congr e
  rw [Nat.card_eq_fintype_card, h] at he
  rw [hc] at he
  norm_num [F] at he
  exact he.symm

private def HasDimensions (A : Subgroup Perm) (a b c d : ℕ) : Prop :=
    Module.finrank F (fixedSpace (representation (Fin 6)) A) = a ∧
    Module.finrank F (fixedSpace (deletedRepresentation (Fin 6)) A) = b ∧
    Module.finrank F (fixedSpace (coreRepresentation (Fin 6)) A) = c ∧
    Module.finrank F (fixedSpace (naturalRepresentation (Fin 6)) A) = d

private theorem dimensions (T : Finset Perm) (a b c d : ℕ)
    (hfull : Fintype.card {v : Vec // fullTest T v} = 2 ^ a)
    (hdeleted : Fintype.card {v : Vec // v 5 = 0 ∧ quotTest T v} = 2 ^ b)
    (hcore : Fintype.card {v : Vec // (∑ i, v i) = 0 ∧ fullTest T v} = 2 ^ c)
    (hnatural : Fintype.card {v : Vec // v 5 = 0 ∧ (∑ i, v i) = 0 ∧ quotTest T v} = 2 ^ d) :
    HasDimensions (Subgroup.closure (T : Set Perm)) a b c d :=
  ⟨finrank_of_count (fullEquiv T) a hfull, finrank_of_count (deletedEquiv T) b hdeleted,
   finrank_of_count (coreEquiv T) c hcore, finrank_of_count (naturalEquiv T) d hnatural⟩

private def initialGenerators (m : ℕ) : Finset Perm :=
  (Finset.univ.filter (fun i : Fin 3 => i.val < m)).image (pairSwap 6)

private theorem initial_closure (m : ℕ) :
    disjointTranspositions 6 m = Subgroup.closure (initialGenerators m : Set Perm) := by
  unfold disjointTranspositions
  congr 1
  ext g
  simp only [initialGenerators, Finset.mem_coe, Finset.mem_image, Finset.mem_filter,
    Finset.mem_univ, true_and, Set.mem_ofPred_eq]
  exact exists_congr (fun i => and_congr_right (fun _ => eq_comm))

private theorem exceptional_closure :
    exceptional 6 (by decide) =
      Subgroup.closure (↑({kleinFirst 6 (by decide), kleinSecond 6 (by decide),
        pairSwap 6 2} : Finset Perm) : Set Perm) := by
  unfold exceptional
  congr 1
  ext g
  simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff,
    Set.mem_ofPred_eq, Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ((h | h) | ⟨i, hi, h⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · have : i = 2 := by apply Fin.ext; have := i.isLt; dsimp at *; omega
      subst i
      exact Or.inr (Or.inr h)
  · rintro (h | h | h)
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr ⟨2, le_rfl, h⟩

private theorem evenPart_closure :
    evenPart 6 = Subgroup.closure
      (↑({pairSwap 6 0 * pairSwap 6 1, pairSwap 6 0 * pairSwap 6 2} : Finset Perm) : Set Perm) := by
  let a := pairSwap 6 0 * pairSwap 6 1
  let b := pairSwap 6 0 * pairSwap 6 2
  have ha : a ∈ evenPart 6 := by
    refine ⟨Subgroup.mul_mem _ (pairSwap_mem 0 (by decide)) (pairSwap_mem 1 (by decide)), ?_⟩
    change Equiv.Perm.sign (pairSwap 6 0 * pairSwap 6 1) = 1
    decide
  have hb : b ∈ evenPart 6 := by
    refine ⟨Subgroup.mul_mem _ (pairSwap_mem 0 (by decide)) (pairSwap_mem 2 (by decide)), ?_⟩
    change Equiv.Perm.sign (pairSwap 6 0 * pairSwap 6 2) = 1
    decide
  apply le_antisymm
  · intro g hg
    obtain ⟨i, rfl⟩ := (mem_disjointTranspositions_iff (3 : Fin 4) g).mp hg.1
    have he : ∀ i : Fin 8, initialWords 3 i ∈ alternatingGroup (Fin 6) →
        initialWords 3 i = 1 ∨ initialWords 3 i = a ∨
        initialWords 3 i = b ∨ initialWords 3 i = a * b := by
      change ∀ i : Fin 8, Equiv.Perm.sign (initialWords 3 i) = 1 → _
      decide
    rcases he i hg.2 with h | h | h | h
    · rw [h]; exact Subgroup.one_mem _
    · rw [h]; exact Subgroup.subset_closure (by simp [a])
    · rw [h]; exact Subgroup.subset_closure (by simp [b])
    · rw [h]; exact Subgroup.mul_mem _
        (Subgroup.subset_closure (by simp [a])) (Subgroup.subset_closure (by simp [b]))
  · apply (Subgroup.closure_le _).mpr
    intro g hg
    simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hg
    rcases hg with rfl | rfl
    · exact ha
    · exact hb

private def bitEquiv : Fin 64 ≃ Vec := (finFunctionFinEquiv (m := 2) (n := 6)).symm
private theorem count_bits (P : Vec → Prop) [DecidablePred P] :
    Fintype.card {v : Vec // P v} = Fintype.card {i : Fin 64 // P (bitEquiv i)} :=
  (Fintype.card_congr (Equiv.subtypeEquiv bitEquiv (fun _ => Iff.rfl))).symm

private theorem codimensions (A : Subgroup Perm) (a b c d : ℕ)
    (h : Module.finrank (ZMod 2) (fixedSpace (representation (Fin 6)) (A)) = a ∧
    Module.finrank (ZMod 2) (fixedSpace (deletedRepresentation (Fin 6)) (A)) = b ∧
    Module.finrank (ZMod 2) (fixedSpace (coreRepresentation (Fin 6)) (A)) = c ∧
    Module.finrank (ZMod 2) (fixedSpace (naturalRepresentation (Fin 6)) (A)) = d) :
    fixedCodim (representation (Fin 6)) (A) = 6 - a ∧
    fixedCodim (deletedRepresentation (Fin 6)) (A) = 5 - b ∧
    fixedCodim (coreRepresentation (Fin 6)) (A) = 5 - c ∧
    fixedCodim (naturalRepresentation (Fin 6)) (A) = 4 - d := by
  have hf := fixedCodim_add_finrank (representation (Fin 6)) A
  have hd := fixedCodim_add_finrank (deletedRepresentation (Fin 6)) A
  have hc := fixedCodim_add_finrank (coreRepresentation (Fin 6)) A
  have hn := fixedCodim_add_finrank (naturalRepresentation (Fin 6)) A
  rw [finrank_full, Fintype.card_fin] at hf
  rw [finrank_deleted, Fintype.card_fin] at hd
  rw [finrank_core, Fintype.card_fin] at hc
  rw [finrank_natural_even _ (by decide), Fintype.card_fin] at hn
  omega

set_option maxRecDepth 4096 in
/-- Fixed-space dimensions in the order full, deleted, core, natural. -/
public theorem finrank_fixedSpace_A1 :
    Module.finrank (ZMod 2) (fixedSpace (representation (Fin 6)) (disjointTranspositions 6 1)) = 5 ∧
    Module.finrank (ZMod 2) (fixedSpace (deletedRepresentation (Fin 6)) (disjointTranspositions 6 1)) = 4 ∧
    Module.finrank (ZMod 2) (fixedSpace (coreRepresentation (Fin 6)) (disjointTranspositions 6 1)) = 4 ∧
    Module.finrank (ZMod 2) (fixedSpace (naturalRepresentation (Fin 6)) (disjointTranspositions 6 1)) = 3 := by
  change HasDimensions (disjointTranspositions 6 1) 5 4 4 3
  have h := dimensions (initialGenerators 1) 5 4 4 3
    (by rw [count_bits]; decide +kernel) (by rw [count_bits]; decide +kernel)
    (by rw [count_bits]; decide +kernel) (by rw [count_bits]; decide +kernel)
  simpa only [D, initial_closure] using h

/-- Fixed codimensions in the order full, deleted, core, natural. -/
public theorem fixedCodim_A1 :
    fixedCodim (representation (Fin 6)) (disjointTranspositions 6 1) = 1 ∧
    fixedCodim (deletedRepresentation (Fin 6)) (disjointTranspositions 6 1) = 1 ∧
    fixedCodim (coreRepresentation (Fin 6)) (disjointTranspositions 6 1) = 1 ∧
    fixedCodim (naturalRepresentation (Fin 6)) (disjointTranspositions 6 1) = 1 := by
  exact codimensions _ 5 4 4 3 finrank_fixedSpace_A1

set_option maxRecDepth 4096 in
/-- Fixed-space dimensions in the order full, deleted, core, natural. -/
public theorem finrank_fixedSpace_A2 :
    Module.finrank (ZMod 2) (fixedSpace (representation (Fin 6)) (disjointTranspositions 6 2)) = 4 ∧
    Module.finrank (ZMod 2) (fixedSpace (deletedRepresentation (Fin 6)) (disjointTranspositions 6 2)) = 3 ∧
    Module.finrank (ZMod 2) (fixedSpace (coreRepresentation (Fin 6)) (disjointTranspositions 6 2)) = 3 ∧
    Module.finrank (ZMod 2) (fixedSpace (naturalRepresentation (Fin 6)) (disjointTranspositions 6 2)) = 2 := by
  change HasDimensions (disjointTranspositions 6 2) 4 3 3 2
  have h := dimensions (initialGenerators 2) 4 3 3 2
    (by rw [count_bits]; decide +kernel) (by rw [count_bits]; decide +kernel)
    (by rw [count_bits]; decide +kernel) (by rw [count_bits]; decide +kernel)
  simpa only [D, initial_closure] using h

/-- Fixed codimensions in the order full, deleted, core, natural. -/
public theorem fixedCodim_A2 :
    fixedCodim (representation (Fin 6)) (disjointTranspositions 6 2) = 2 ∧
    fixedCodim (deletedRepresentation (Fin 6)) (disjointTranspositions 6 2) = 2 ∧
    fixedCodim (coreRepresentation (Fin 6)) (disjointTranspositions 6 2) = 2 ∧
    fixedCodim (naturalRepresentation (Fin 6)) (disjointTranspositions 6 2) = 2 := by
  exact codimensions _ 4 3 3 2 finrank_fixedSpace_A2

set_option maxRecDepth 4096 in
/-- Fixed-space dimensions in the order full, deleted, core, natural. -/
public theorem finrank_fixedSpace_D :
    Module.finrank (ZMod 2) (fixedSpace (representation (Fin 6)) (D 6)) = 3 ∧
    Module.finrank (ZMod 2) (fixedSpace (deletedRepresentation (Fin 6)) (D 6)) = 2 ∧
    Module.finrank (ZMod 2) (fixedSpace (coreRepresentation (Fin 6)) (D 6)) = 3 ∧
    Module.finrank (ZMod 2) (fixedSpace (naturalRepresentation (Fin 6)) (D 6)) = 2 := by
  change HasDimensions (D 6) 3 2 3 2
  have h := dimensions (initialGenerators 3) 3 2 3 2
    (by rw [count_bits]; decide +kernel) (by rw [count_bits]; decide +kernel)
    (by rw [count_bits]; decide +kernel) (by rw [count_bits]; decide +kernel)
  simpa only [D, initial_closure] using h

/-- Fixed codimensions in the order full, deleted, core, natural. -/
public theorem fixedCodim_D :
    fixedCodim (representation (Fin 6)) (D 6) = 3 ∧
    fixedCodim (deletedRepresentation (Fin 6)) (D 6) = 3 ∧
    fixedCodim (coreRepresentation (Fin 6)) (D 6) = 2 ∧
    fixedCodim (naturalRepresentation (Fin 6)) (D 6) = 2 := by
  exact codimensions _ 3 2 3 2 finrank_fixedSpace_D

set_option maxRecDepth 4096 in
/-- Fixed-space dimensions in the order full, deleted, core, natural. -/
public theorem finrank_fixedSpace_exceptional :
    Module.finrank (ZMod 2) (fixedSpace (representation (Fin 6)) (exceptional 6 (by decide))) = 2 ∧
    Module.finrank (ZMod 2) (fixedSpace (deletedRepresentation (Fin 6)) (exceptional 6 (by decide))) = 1 ∧
    Module.finrank (ZMod 2) (fixedSpace (coreRepresentation (Fin 6)) (exceptional 6 (by decide))) = 2 ∧
    Module.finrank (ZMod 2) (fixedSpace (naturalRepresentation (Fin 6)) (exceptional 6 (by decide))) = 1 := by
  change HasDimensions (exceptional 6 (by decide)) 2 1 2 1
  have h := dimensions ({kleinFirst 6 (by decide), kleinSecond 6 (by decide), pairSwap 6 2}) 2 1 2 1
    (by rw [count_bits]; decide +kernel) (by rw [count_bits]; decide +kernel)
    (by rw [count_bits]; decide +kernel) (by rw [count_bits]; decide +kernel)
  simpa only [exceptional_closure, D] using h

/-- Fixed codimensions in the order full, deleted, core, natural. -/
public theorem fixedCodim_exceptional :
    fixedCodim (representation (Fin 6)) (exceptional 6 (by decide)) = 4 ∧
    fixedCodim (deletedRepresentation (Fin 6)) (exceptional 6 (by decide)) = 4 ∧
    fixedCodim (coreRepresentation (Fin 6)) (exceptional 6 (by decide)) = 3 ∧
    fixedCodim (naturalRepresentation (Fin 6)) (exceptional 6 (by decide)) = 3 := by
  exact codimensions _ 2 1 2 1 finrank_fixedSpace_exceptional

set_option maxRecDepth 4096 in
/-- Fixed-space dimensions in the order full, deleted, core, natural. -/
public theorem finrank_fixedSpace_evenPart :
    Module.finrank (ZMod 2) (fixedSpace (representation (Fin 6)) (evenPart 6)) = 3 ∧
    Module.finrank (ZMod 2) (fixedSpace (deletedRepresentation (Fin 6)) (evenPart 6)) = 2 ∧
    Module.finrank (ZMod 2) (fixedSpace (coreRepresentation (Fin 6)) (evenPart 6)) = 3 ∧
    Module.finrank (ZMod 2) (fixedSpace (naturalRepresentation (Fin 6)) (evenPart 6)) = 2 := by
  change HasDimensions (evenPart 6) 3 2 3 2
  have h := dimensions ({pairSwap 6 0 * pairSwap 6 1, pairSwap 6 0 * pairSwap 6 2}) 3 2 3 2
    (by rw [count_bits]; decide +kernel) (by rw [count_bits]; decide +kernel)
    (by rw [count_bits]; decide +kernel) (by rw [count_bits]; decide +kernel)
  simpa only [evenPart_closure, D] using h

/-- Fixed codimensions in the order full, deleted, core, natural. -/
public theorem fixedCodim_evenPart :
    fixedCodim (representation (Fin 6)) (evenPart 6) = 3 ∧
    fixedCodim (deletedRepresentation (Fin 6)) (evenPart 6) = 3 ∧
    fixedCodim (coreRepresentation (Fin 6)) (evenPart 6) = 2 ∧
    fixedCodim (naturalRepresentation (Fin 6)) (evenPart 6) = 2 := by
  exact codimensions _ 3 2 3 2 finrank_fixedSpace_evenPart

set_option maxRecDepth 4096 in
/-- Fixed-space dimensions in the order full, deleted, core, natural. -/
public theorem finrank_fixedSpace_plus :
    Module.finrank (ZMod 2) (fixedSpace (representation (Fin 6)) (plus)) = 3 ∧
    Module.finrank (ZMod 2) (fixedSpace (deletedRepresentation (Fin 6)) (plus)) = 2 ∧
    Module.finrank (ZMod 2) (fixedSpace (coreRepresentation (Fin 6)) (plus)) = 3 ∧
    Module.finrank (ZMod 2) (fixedSpace (naturalRepresentation (Fin 6)) (plus)) = 2 := by
  change HasDimensions (plus) 3 2 3 2
  have h := dimensions ({kleinFirst 6 (by decide), pairSwap 6 2}) 3 2 3 2
    (by rw [count_bits]; decide +kernel) (by rw [count_bits]; decide +kernel)
    (by rw [count_bits]; decide +kernel) (by rw [count_bits]; decide +kernel)
  simpa only [plus, Finset.coe_insert, Finset.coe_singleton] using h

/-- Fixed codimensions in the order full, deleted, core, natural. -/
public theorem fixedCodim_plus :
    fixedCodim (representation (Fin 6)) (plus) = 3 ∧
    fixedCodim (deletedRepresentation (Fin 6)) (plus) = 3 ∧
    fixedCodim (coreRepresentation (Fin 6)) (plus) = 2 ∧
    fixedCodim (naturalRepresentation (Fin 6)) (plus) = 2 := by
  exact codimensions _ 3 2 3 2 finrank_fixedSpace_plus

set_option maxRecDepth 4096 in
/-- Fixed-space dimensions in the order full, deleted, core, natural. -/
public theorem finrank_fixedSpace_double :
    Module.finrank (ZMod 2) (fixedSpace (representation (Fin 6)) (double)) = 4 ∧
    Module.finrank (ZMod 2) (fixedSpace (deletedRepresentation (Fin 6)) (double)) = 3 ∧
    Module.finrank (ZMod 2) (fixedSpace (coreRepresentation (Fin 6)) (double)) = 3 ∧
    Module.finrank (ZMod 2) (fixedSpace (naturalRepresentation (Fin 6)) (double)) = 2 := by
  change HasDimensions (double) 4 3 3 2
  have h := dimensions ({kleinFirst 6 (by decide)}) 4 3 3 2
    (by rw [count_bits]; decide +kernel) (by rw [count_bits]; decide +kernel)
    (by rw [count_bits]; decide +kernel) (by rw [count_bits]; decide +kernel)
  simpa only [double, Finset.coe_insert, Finset.coe_singleton] using h

/-- Fixed codimensions in the order full, deleted, core, natural. -/
public theorem fixedCodim_double :
    fixedCodim (representation (Fin 6)) (double) = 2 ∧
    fixedCodim (deletedRepresentation (Fin 6)) (double) = 2 ∧
    fixedCodim (coreRepresentation (Fin 6)) (double) = 2 ∧
    fixedCodim (naturalRepresentation (Fin 6)) (double) = 2 := by
  exact codimensions _ 4 3 3 2 finrank_fixedSpace_double

set_option maxRecDepth 4096 in
/-- Fixed-space dimensions in the order full, deleted, core, natural. -/
public theorem finrank_fixedSpace_triple :
    Module.finrank (ZMod 2) (fixedSpace (representation (Fin 6)) (triple)) = 3 ∧
    Module.finrank (ZMod 2) (fixedSpace (deletedRepresentation (Fin 6)) (triple)) = 3 ∧
    Module.finrank (ZMod 2) (fixedSpace (coreRepresentation (Fin 6)) (triple)) = 3 ∧
    Module.finrank (ZMod 2) (fixedSpace (naturalRepresentation (Fin 6)) (triple)) = 2 := by
  change HasDimensions (triple) 3 3 3 2
  have h := dimensions ({kleinFirst 6 (by decide) * pairSwap 6 2}) 3 3 3 2
    (by rw [count_bits]; decide +kernel) (by rw [count_bits]; decide +kernel)
    (by rw [count_bits]; decide +kernel) (by rw [count_bits]; decide +kernel)
  simpa only [triple, Finset.coe_insert, Finset.coe_singleton] using h

/-- Fixed codimensions in the order full, deleted, core, natural. -/
public theorem fixedCodim_triple :
    fixedCodim (representation (Fin 6)) (triple) = 3 ∧
    fixedCodim (deletedRepresentation (Fin 6)) (triple) = 2 ∧
    fixedCodim (coreRepresentation (Fin 6)) (triple) = 2 ∧
    fixedCodim (naturalRepresentation (Fin 6)) (triple) = 2 := by
  exact codimensions _ 3 3 3 2 finrank_fixedSpace_triple

set_option maxRecDepth 4096 in
/-- Fixed-space dimensions in the order full, deleted, core, natural. -/
public theorem finrank_fixedSpace_klein :
    Module.finrank (ZMod 2) (fixedSpace (representation (Fin 6)) (klein)) = 3 ∧
    Module.finrank (ZMod 2) (fixedSpace (deletedRepresentation (Fin 6)) (klein)) = 2 ∧
    Module.finrank (ZMod 2) (fixedSpace (coreRepresentation (Fin 6)) (klein)) = 2 ∧
    Module.finrank (ZMod 2) (fixedSpace (naturalRepresentation (Fin 6)) (klein)) = 1 := by
  change HasDimensions (klein) 3 2 2 1
  have h := dimensions ({kleinFirst 6 (by decide), kleinSecond 6 (by decide)}) 3 2 2 1
    (by rw [count_bits]; decide +kernel) (by rw [count_bits]; decide +kernel)
    (by rw [count_bits]; decide +kernel) (by rw [count_bits]; decide +kernel)
  simpa only [klein, Finset.coe_insert, Finset.coe_singleton] using h

/-- Fixed codimensions in the order full, deleted, core, natural. -/
public theorem fixedCodim_klein :
    fixedCodim (representation (Fin 6)) (klein) = 3 ∧
    fixedCodim (deletedRepresentation (Fin 6)) (klein) = 3 ∧
    fixedCodim (coreRepresentation (Fin 6)) (klein) = 3 ∧
    fixedCodim (naturalRepresentation (Fin 6)) (klein) = 3 := by
  exact codimensions _ 3 2 2 1 finrank_fixedSpace_klein

set_option maxRecDepth 4096 in
/-- Fixed-space dimensions in the order full, deleted, core, natural. -/
public theorem finrank_fixedSpace_twisted :
    Module.finrank (ZMod 2) (fixedSpace (representation (Fin 6)) (twisted)) = 2 ∧
    Module.finrank (ZMod 2) (fixedSpace (deletedRepresentation (Fin 6)) (twisted)) = 2 ∧
    Module.finrank (ZMod 2) (fixedSpace (coreRepresentation (Fin 6)) (twisted)) = 2 ∧
    Module.finrank (ZMod 2) (fixedSpace (naturalRepresentation (Fin 6)) (twisted)) = 1 := by
  change HasDimensions (twisted) 2 2 2 1
  have h := dimensions ({kleinFirst 6 (by decide), kleinSecond 6 (by decide) * pairSwap 6 2}) 2 2 2 1
    (by rw [count_bits]; decide +kernel) (by rw [count_bits]; decide +kernel)
    (by rw [count_bits]; decide +kernel) (by rw [count_bits]; decide +kernel)
  simpa only [twisted, Finset.coe_insert, Finset.coe_singleton] using h

/-- Fixed codimensions in the order full, deleted, core, natural. -/
public theorem fixedCodim_twisted :
    fixedCodim (representation (Fin 6)) (twisted) = 4 ∧
    fixedCodim (deletedRepresentation (Fin 6)) (twisted) = 3 ∧
    fixedCodim (coreRepresentation (Fin 6)) (twisted) = 3 ∧
    fixedCodim (naturalRepresentation (Fin 6)) (twisted) = 3 := by
  exact codimensions _ 2 2 2 1 finrank_fixedSpace_twisted

set_option maxRecDepth 4096 in
/-- Fixed-space dimensions in the order full, deleted, core, natural. -/
public theorem finrank_fixedSpace_last :
    Module.finrank (ZMod 2) (fixedSpace (representation (Fin 6)) (last)) = 5 ∧
    Module.finrank (ZMod 2) (fixedSpace (deletedRepresentation (Fin 6)) (last)) = 4 ∧
    Module.finrank (ZMod 2) (fixedSpace (coreRepresentation (Fin 6)) (last)) = 4 ∧
    Module.finrank (ZMod 2) (fixedSpace (naturalRepresentation (Fin 6)) (last)) = 3 := by
  change HasDimensions (last) 5 4 4 3
  have h := dimensions ({pairSwap 6 2}) 5 4 4 3
    (by rw [count_bits]; decide +kernel) (by rw [count_bits]; decide +kernel)
    (by rw [count_bits]; decide +kernel) (by rw [count_bits]; decide +kernel)
  simpa only [last, Finset.coe_insert, Finset.coe_singleton] using h

/-- Fixed codimensions in the order full, deleted, core, natural. -/
public theorem fixedCodim_last :
    fixedCodim (representation (Fin 6)) (last) = 1 ∧
    fixedCodim (deletedRepresentation (Fin 6)) (last) = 1 ∧
    fixedCodim (coreRepresentation (Fin 6)) (last) = 1 ∧
    fixedCodim (naturalRepresentation (Fin 6)) (last) = 1 := by
  exact codimensions _ 5 4 4 3 finrank_fixedSpace_last

set_option maxRecDepth 4096 in
/-- Fixed-space dimensions in the order full, deleted, core, natural. -/
public theorem finrank_fixedSpace_tailTwo :
    Module.finrank (ZMod 2) (fixedSpace (representation (Fin 6)) (tailTwo)) = 4 ∧
    Module.finrank (ZMod 2) (fixedSpace (deletedRepresentation (Fin 6)) (tailTwo)) = 3 ∧
    Module.finrank (ZMod 2) (fixedSpace (coreRepresentation (Fin 6)) (tailTwo)) = 3 ∧
    Module.finrank (ZMod 2) (fixedSpace (naturalRepresentation (Fin 6)) (tailTwo)) = 2 := by
  change HasDimensions (tailTwo) 4 3 3 2
  have h := dimensions ({pairSwap 6 1, pairSwap 6 2}) 4 3 3 2
    (by rw [count_bits]; decide +kernel) (by rw [count_bits]; decide +kernel)
    (by rw [count_bits]; decide +kernel) (by rw [count_bits]; decide +kernel)
  simpa only [tailTwo, Finset.coe_insert, Finset.coe_singleton] using h

/-- Fixed codimensions in the order full, deleted, core, natural. -/
public theorem fixedCodim_tailTwo :
    fixedCodim (representation (Fin 6)) (tailTwo) = 2 ∧
    fixedCodim (deletedRepresentation (Fin 6)) (tailTwo) = 2 ∧
    fixedCodim (coreRepresentation (Fin 6)) (tailTwo) = 2 ∧
    fixedCodim (naturalRepresentation (Fin 6)) (tailTwo) = 2 := by
  exact codimensions _ 4 3 3 2 finrank_fixedSpace_tailTwo

end CFSG.Quasithin.ChapterB.Offenders.Six
