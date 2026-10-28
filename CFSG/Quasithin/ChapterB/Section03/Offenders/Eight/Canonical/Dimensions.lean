module

public import CFSG.Quasithin.ChapterB.Section03.Offenders.Eight.Canonical.Representatives
import Mathlib.FieldTheory.Finiteness
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases

/-!
# Fixed-space calculations for degree-eight canonical groups

Normalize a quotient representative at the last coordinate. The quotient fixed
condition is constant displacement, which retains every additional fixed vector.
Counting the resulting subsets of the 256 binary vectors gives the dimensions
by the finite vector-space cardinality formula. This adapts the degree-six
normalization proof in `Offenders.Six.Dimensions` to degree eight.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Proposition B.3.2(1),(2), printed pp. 83–84.
-/

@[expose] public section
open BinaryPermutation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.Offenders.Eight

abbrev Vec := Full (Fin 8)
abbrev F := ZMod 2
def fullTest (T : Finset Perm) (v : Vec) : Prop :=
  ∀ g ∈ T, ∀ i, v (g.symm i) = v i
def quotTest (T : Finset Perm) (v : Vec) : Prop :=
  ∀ g ∈ T, ∃ c : F, ∀ i, v (g.symm i) - v i = c
instance (T : Finset Perm) (v : Vec) : Decidable (fullTest T v) :=
  Finset.decidableDforallFinset
instance (T : Finset Perm) (v : Vec) : Decidable (quotTest T v) :=
  Finset.decidableDforallFinset

private theorem full_test (T : Finset Perm) (v : Vec) :
    v ∈ fixedSpace (representation (Fin 8)) (Subgroup.closure (T : Set Perm)) ↔
      fullTest T v := by
  simp only [mem_fixedSpace_closure_iff, fullTest, funext_iff, representation_apply,
    Finset.mem_coe]

private theorem deleted_test (T : Finset Perm) (v : Vec) :
    (constants (Fin 8)).mkQ v ∈
      fixedSpace (deletedRepresentation (Fin 8)) (Subgroup.closure (T : Set Perm)) ↔
      quotTest T v := by
  simp only [mem_fixedSpace_closure_iff, deleted_fixed_iff, quotTest, Finset.mem_coe]

private theorem normalized_injective (v w : Vec) (hv : v 7 = 0) (hw : w 7 = 0)
    (h : (constants (Fin 8)).mkQ v = (constants (Fin 8)).mkQ w) : v = w := by
  obtain ⟨c, hc⟩ := (mem_constants_iff (v - w)).mp ((Submodule.Quotient.eq _).mp h)
  have hc0 : c = 0 := by simpa [hv, hw] using (hc 7).symm
  funext i
  exact sub_eq_zero.mp ((hc i).trans hc0)

private def normalize (v : Vec) : Vec := v - v 7 • allOne (Fin 8)
private theorem normalize_last (v : Vec) : normalize v 7 = 0 := by
  simp [normalize, allOne]
private theorem normalize_mk (v : Vec) :
    (constants (Fin 8)).mkQ (normalize v) = (constants (Fin 8)).mkQ v := by
  apply (Submodule.Quotient.eq _).mpr
  change v - v 7 • allOne (Fin 8) - v ∈ constants (Fin 8)
  rw [sub_sub_cancel_left]
  exact Submodule.neg_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
private theorem normalize_core (v : Vec) (hv : v ∈ core (Fin 8)) :
    normalize v ∈ core (Fin 8) := by
  apply Submodule.sub_mem _ hv
  apply ((constants_le_core_iff (Fin 8)).mpr (by decide))
  exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))

private noncomputable def fullEquiv (T : Finset Perm) :
    {v : Vec // fullTest T v} ≃
      fixedSpace (representation (Fin 8)) (Subgroup.closure (T : Set Perm)) :=
  Equiv.subtypeEquivRight (fun v => (full_test T v).symm)

private noncomputable def coreEquiv (T : Finset Perm) :
    {v : Vec // (∑ i, v i) = 0 ∧ fullTest T v} ≃
      fixedSpace (coreRepresentation (Fin 8)) (Subgroup.closure (T : Set Perm)) where
  toFun v := ⟨⟨v.val, v.property.1⟩, by
    rw [mem_core_fixedSpace_iff, ← mem_full_fixedSpace_iff, full_test]
    exact v.property.2⟩
  invFun v := ⟨v.val.val, v.val.property, by
    rw [← full_test, mem_full_fixedSpace_iff, ← mem_core_fixedSpace_iff]
    exact v.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

private noncomputable def deletedEquiv (T : Finset Perm) :
    {v : Vec // v 7 = 0 ∧ quotTest T v} ≃
      fixedSpace (deletedRepresentation (Fin 8)) (Subgroup.closure (T : Set Perm)) := by
  let f : {v : Vec // v 7 = 0 ∧ quotTest T v} →
      fixedSpace (deletedRepresentation (Fin 8)) (Subgroup.closure (T : Set Perm)) :=
    fun v => ⟨(constants (Fin 8)).mkQ v.val, (deleted_test T v.val).mpr v.property.2⟩
  apply Equiv.ofBijective f
  constructor
  · intro v w h
    apply Subtype.ext
    exact normalized_injective _ _ v.property.1 w.property.1 (congrArg Subtype.val h)
  · intro q
    obtain ⟨v, hv⟩ := (constants (Fin 8)).mkQ_surjective q.val
    refine ⟨⟨normalize v, normalize_last v, ?_⟩, ?_⟩
    · rw [← deleted_test, normalize_mk, hv]
      exact q.property
    · apply Subtype.ext
      exact (normalize_mk v).trans hv

private noncomputable def naturalEquiv (T : Finset Perm) :
    {v : Vec // v 7 = 0 ∧ (∑ i, v i) = 0 ∧ quotTest T v} ≃
      fixedSpace (naturalRepresentation (Fin 8)) (Subgroup.closure (T : Set Perm)) := by
  let f : {v : Vec // v 7 = 0 ∧ (∑ i, v i) = 0 ∧ quotTest T v} →
      fixedSpace (naturalRepresentation (Fin 8)) (Subgroup.closure (T : Set Perm)) :=
    fun v => ⟨⟨(constants (Fin 8)).mkQ v.val, ⟨v.val, v.property.2.1, rfl⟩⟩, by
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

def HasDimensions (A : Subgroup Perm) (a b c d : ℕ) : Prop :=
    Module.finrank F (fixedSpace (representation (Fin 8)) A) = a ∧
    Module.finrank F (fixedSpace (deletedRepresentation (Fin 8)) A) = b ∧
    Module.finrank F (fixedSpace (coreRepresentation (Fin 8)) A) = c ∧
    Module.finrank F (fixedSpace (naturalRepresentation (Fin 8)) A) = d

theorem dimensions (T : Finset Perm) (a b c d : ℕ)
    (hfull : Fintype.card {v : Vec // fullTest T v} = 2 ^ a)
    (hdeleted : Fintype.card {v : Vec // v 7 = 0 ∧ quotTest T v} = 2 ^ b)
    (hcore : Fintype.card {v : Vec // (∑ i, v i) = 0 ∧ fullTest T v} = 2 ^ c)
    (hnatural : Fintype.card {v : Vec // v 7 = 0 ∧ (∑ i, v i) = 0 ∧ quotTest T v} = 2 ^ d) :
    HasDimensions (Subgroup.closure (T : Set Perm)) a b c d :=
  ⟨finrank_of_count (fullEquiv T) a hfull, finrank_of_count (deletedEquiv T) b hdeleted,
   finrank_of_count (coreEquiv T) c hcore, finrank_of_count (naturalEquiv T) d hnatural⟩

def initialGenerators (m : ℕ) : Finset Perm :=
  (Finset.univ.filter (fun i : Fin 4 => i.val < m)).image (pairSwap 8)

theorem initial_closure (m : ℕ) :
    disjointTranspositions 8 m = Subgroup.closure (initialGenerators m : Set Perm) := by
  unfold disjointTranspositions
  congr 1
  ext g
  simp only [initialGenerators, Finset.mem_coe, Finset.mem_image, Finset.mem_filter,
    Finset.mem_univ, true_and, Set.mem_ofPred_eq]
  exact exists_congr (fun i => and_congr_right (fun _ => eq_comm))

theorem exceptional_closure :
    exceptional 8 (by decide) =
      Subgroup.closure (↑({kleinFirst 8 (by decide), kleinSecond 8 (by decide),
        pairSwap 8 2, pairSwap 8 3} : Finset Perm) : Set Perm) := by
  unfold exceptional
  congr 1
  ext g
  simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff,
    Set.mem_ofPred_eq, Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ((h | h) | ⟨i, hi, h⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · have : i = 2 ∨ i = 3 := by
        have := i.isLt
        fin_cases i <;> simp_all
      rcases this with rfl | rfl
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h))
  · rintro (h | h | h | h)
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr ⟨2, le_rfl, h⟩
    · exact Or.inr ⟨3, by decide, h⟩

def bitEquiv : Fin 256 ≃ Vec := (finFunctionFinEquiv (m := 2) (n := 8)).symm
theorem count_bits (P : Vec → Prop) [DecidablePred P] :
    Fintype.card {v : Vec // P v} = Fintype.card {i : Fin 256 // P (bitEquiv i)} :=
  (Fintype.card_congr (Equiv.subtypeEquiv bitEquiv (fun _ => Iff.rfl))).symm

theorem codimensions (A : Subgroup Perm) (a b c d : ℕ)
    (h : Module.finrank (ZMod 2) (fixedSpace (representation (Fin 8)) (A)) = a ∧
    Module.finrank (ZMod 2) (fixedSpace (deletedRepresentation (Fin 8)) (A)) = b ∧
    Module.finrank (ZMod 2) (fixedSpace (coreRepresentation (Fin 8)) (A)) = c ∧
    Module.finrank (ZMod 2) (fixedSpace (naturalRepresentation (Fin 8)) (A)) = d) :
    fixedCodim (representation (Fin 8)) (A) = 8 - a ∧
    fixedCodim (deletedRepresentation (Fin 8)) (A) = 7 - b ∧
    fixedCodim (coreRepresentation (Fin 8)) (A) = 7 - c ∧
    fixedCodim (naturalRepresentation (Fin 8)) (A) = 6 - d := by
  have hf := fixedCodim_add_finrank (representation (Fin 8)) A
  have hd := fixedCodim_add_finrank (deletedRepresentation (Fin 8)) A
  have hc := fixedCodim_add_finrank (coreRepresentation (Fin 8)) A
  have hn := fixedCodim_add_finrank (naturalRepresentation (Fin 8)) A
  rw [finrank_full, Fintype.card_fin] at hf
  rw [finrank_deleted, Fintype.card_fin] at hd
  rw [finrank_core, Fintype.card_fin] at hc
  rw [finrank_natural_even _ (by decide), Fintype.card_fin] at hn
  omega

set_option maxRecDepth 4096 in
/-- Fixed dimensions, in the order full, deleted, core, natural. -/
theorem finrank_fixedSpace_A1 : HasDimensions (disjointTranspositions 8 1) 7 6 6 5 := by
  have h := dimensions (initialGenerators 1) 7 6 6 5
    (by rw [count_bits]; decide +kernel) (by rw [count_bits]; decide +kernel)
    (by rw [count_bits]; decide +kernel) (by rw [count_bits]; decide +kernel)
  simpa only [D, initial_closure, exceptional_closure] using h

/-- Fixed codimensions, in the order full, deleted, core, natural. -/
theorem fixedCodim_A1 :
    fixedCodim (representation (Fin 8)) (disjointTranspositions 8 1) = 1 ∧
    fixedCodim (deletedRepresentation (Fin 8)) (disjointTranspositions 8 1) = 1 ∧
    fixedCodim (coreRepresentation (Fin 8)) (disjointTranspositions 8 1) = 1 ∧
    fixedCodim (naturalRepresentation (Fin 8)) (disjointTranspositions 8 1) = 1 := by
  exact codimensions _ 7 6 6 5 finrank_fixedSpace_A1

set_option maxRecDepth 4096 in
/-- Fixed dimensions, in the order full, deleted, core, natural. -/
theorem finrank_fixedSpace_A2 : HasDimensions (disjointTranspositions 8 2) 6 5 5 4 := by
  have h := dimensions (initialGenerators 2) 6 5 5 4
    (by rw [count_bits]; decide +kernel) (by rw [count_bits]; decide +kernel)
    (by rw [count_bits]; decide +kernel) (by rw [count_bits]; decide +kernel)
  simpa only [D, initial_closure, exceptional_closure] using h

/-- Fixed codimensions, in the order full, deleted, core, natural. -/
theorem fixedCodim_A2 :
    fixedCodim (representation (Fin 8)) (disjointTranspositions 8 2) = 2 ∧
    fixedCodim (deletedRepresentation (Fin 8)) (disjointTranspositions 8 2) = 2 ∧
    fixedCodim (coreRepresentation (Fin 8)) (disjointTranspositions 8 2) = 2 ∧
    fixedCodim (naturalRepresentation (Fin 8)) (disjointTranspositions 8 2) = 2 := by
  exact codimensions _ 6 5 5 4 finrank_fixedSpace_A2

set_option maxRecDepth 4096 in
/-- Fixed dimensions, in the order full, deleted, core, natural. -/
theorem finrank_fixedSpace_A3 : HasDimensions (disjointTranspositions 8 3) 5 4 4 3 := by
  have h := dimensions (initialGenerators 3) 5 4 4 3
    (by rw [count_bits]; decide +kernel) (by rw [count_bits]; decide +kernel)
    (by rw [count_bits]; decide +kernel) (by rw [count_bits]; decide +kernel)
  simpa only [D, initial_closure, exceptional_closure] using h

/-- Fixed codimensions, in the order full, deleted, core, natural. -/
theorem fixedCodim_A3 :
    fixedCodim (representation (Fin 8)) (disjointTranspositions 8 3) = 3 ∧
    fixedCodim (deletedRepresentation (Fin 8)) (disjointTranspositions 8 3) = 3 ∧
    fixedCodim (coreRepresentation (Fin 8)) (disjointTranspositions 8 3) = 3 ∧
    fixedCodim (naturalRepresentation (Fin 8)) (disjointTranspositions 8 3) = 3 := by
  exact codimensions _ 5 4 4 3 finrank_fixedSpace_A3

set_option maxRecDepth 4096 in
/-- Fixed dimensions, in the order full, deleted, core, natural. -/
theorem finrank_fixedSpace_D : HasDimensions (D 8) 4 3 4 3 := by
  have h := dimensions (initialGenerators 4) 4 3 4 3
    (by rw [count_bits]; decide +kernel) (by rw [count_bits]; decide +kernel)
    (by rw [count_bits]; decide +kernel) (by rw [count_bits]; decide +kernel)
  simpa only [D, initial_closure, exceptional_closure] using h

/-- Fixed codimensions, in the order full, deleted, core, natural. -/
theorem fixedCodim_D :
    fixedCodim (representation (Fin 8)) (D 8) = 4 ∧
    fixedCodim (deletedRepresentation (Fin 8)) (D 8) = 4 ∧
    fixedCodim (coreRepresentation (Fin 8)) (D 8) = 3 ∧
    fixedCodim (naturalRepresentation (Fin 8)) (D 8) = 3 := by
  exact codimensions _ 4 3 4 3 finrank_fixedSpace_D

set_option maxRecDepth 4096 in
/-- Fixed dimensions, in the order full, deleted, core, natural. -/
theorem finrank_fixedSpace_exceptional : HasDimensions (exceptional 8 (by decide)) 3 2 3 2 := by
  have h := dimensions (({kleinFirst 8 (by decide), kleinSecond 8 (by decide), pairSwap 8 2, pairSwap 8 3} : Finset Perm)) 3 2 3 2
    (by rw [count_bits]; decide +kernel) (by rw [count_bits]; decide +kernel)
    (by rw [count_bits]; decide +kernel) (by rw [count_bits]; decide +kernel)
  simpa only [D, initial_closure, exceptional_closure] using h

/-- Fixed codimensions, in the order full, deleted, core, natural. -/
theorem fixedCodim_exceptional :
    fixedCodim (representation (Fin 8)) (exceptional 8 (by decide)) = 5 ∧
    fixedCodim (deletedRepresentation (Fin 8)) (exceptional 8 (by decide)) = 5 ∧
    fixedCodim (coreRepresentation (Fin 8)) (exceptional 8 (by decide)) = 4 ∧
    fixedCodim (naturalRepresentation (Fin 8)) (exceptional 8 (by decide)) = 4 := by
  exact codimensions _ 3 2 3 2 finrank_fixedSpace_exceptional

end CFSG.Quasithin.ChapterB.Offenders.Eight
