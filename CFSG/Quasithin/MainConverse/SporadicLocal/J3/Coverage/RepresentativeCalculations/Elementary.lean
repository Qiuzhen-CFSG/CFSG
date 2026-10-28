module

public import CFSG.Quasithin.MainConverse.SporadicLocal.J3.Coverage.Fusion.Table
public import CFSG.Quasithin.MainConverse.SporadicLocal.J3.Coverage.LocalReduction
import Mathlib.Tactic.FinCases

/-!
# The sixteen elements of the fixed J₃ elementary candidate

The four unchanged elementary generators give sixteen binary words. Their
products are computed in the already certified Sylow table, using the allowed
order-128 premise. The resulting xor identities prove that these words form
an abelian subgroup of order sixteen, and the generating definitions identify
it with `elementaryCandidate`. The masks 1, 3, 5, 14, 15 identify all five
published representatives, giving exact finite membership tests for later
normalizer and centralizer calculations.

Source: the concrete computational route to the three two-locals in GLS,
Number 3, Table 5.3h, printed p.269. The table itself does not specify these
representatives. All finite arithmetic below is checked by the Lean kernel;
no local-action or ambient-normalizer description is assumed.
-/

namespace CFSG.Quasithin.MainConverse.SporadicLocal.J3Coverage.RepresentativeCalculations
open Subgroup Sporadic.Janko3 Sporadic.Janko3.TwoLocal Theory.GroupTheory
open Fusion
set_option Elab.async false

/-- The binary word uses the j-th generator precisely when bit j is set. -/
@[expose] public def elementaryWord (i : Fin 16) : List (Fin 4) :=
  (List.finRange 4).filter (fun j => i.val.testBit j.val)

/-- A word in the four fixed model generators, indexed by its binary mask. -/
@[expose] public def elementaryElement (i : Fin 16) : Model :=
  evalWord elementaryGenerator (elementaryWord i)

/-- The same word evaluated in the certified Sylow multiplication table. -/
@[expose] public def elementaryIndex (i : Fin 16) : Fin 128 :=
  (elementaryWord i).foldr (fun j k => mulIndex (elementaryGeneratorIndex j) k) 0

/-- Agreement with the actual model element at the computed Sylow index. -/
public theorem elementaryElement_eq_element (hS : Nat.card sylowCandidate = 128) (i : Fin 16) :
    elementaryElement i = element (elementaryIndex i) := by
  have h (w : List (Fin 4)) : evalWord elementaryGenerator w =
      element (w.foldr (fun j k => mulIndex (elementaryGeneratorIndex j) k) 0) := by
    induction w with
    | nil => exact element_zero.symm
    | cons j w ih =>
      simp only [evalWord, List.foldr_cons, element_mul hS, ih]
      rw [elementaryGenerator_eq_sylowEnumeration]
      rfl
  exact h _

/-- Addition of the four binary coordinates. -/
@[expose] public def xorIndex (i j : Fin 16) : Fin 16 :=
  ⟨(i.val ^^^ j.val) % 16, Nat.mod_lt _ (by decide)⟩

public theorem elementaryElement_zero : elementaryElement 0 = 1 := rfl

/-- Binary-coordinate addition is actual multiplication in the model. -/
public theorem elementaryElement_mul (hS : Nat.card sylowCandidate = 128) (i j : Fin 16) :
    elementaryElement (xorIndex i j) = elementaryElement i * elementaryElement j := by
  have ht : ∀ i j : Fin 16, elementaryIndex (xorIndex i j) =
      mulIndex (elementaryIndex i) (elementaryIndex j) := by decide +kernel
  simp only [elementaryElement_eq_element hS, ht, element_mul hS]

/-- The sixteen words are distinct model elements. -/
public theorem elementaryElement_injective (hS : Nat.card sylowCandidate = 128) :
    Function.Injective elementaryElement := by
  have ht : Function.Injective elementaryIndex := by decide +kernel
  intro i j hij
  simp only [elementaryElement_eq_element hS] at hij
  exact ht (element_injective hij)

/-- Every binary word is an involution or the identity. -/
public theorem elementaryElement_sq (hS : Nat.card sylowCandidate = 128) (i : Fin 16) :
    elementaryElement i * elementaryElement i = 1 := by
  have ht : ∀ i : Fin 16, xorIndex i i = 0 := by decide +kernel
  rw [← elementaryElement_mul hS, ht, elementaryElement_zero]

public theorem elementaryElement_inv (hS : Nat.card sylowCandidate = 128) (i : Fin 16) :
    (elementaryElement i)⁻¹ = elementaryElement i :=
  (eq_inv_of_mul_eq_one_right (elementaryElement_sq hS i)).symm

/-- The masks of the four original generators, in their original order. -/
@[expose] public def basisMask : Fin 4 → Fin 16 := ![1, 2, 4, 8]

public theorem elementaryElement_basis (i : Fin 4) :
    elementaryElement (basisMask i) = elementaryGenerator i := by
  fin_cases i <;> change elementaryGenerator _ * 1 = _ <;> exact mul_one _

/-- The selected coordinates of i are contained in those of m. -/
@[expose] public def supported (m i : Fin 16) : Prop := i.val &&& m.val = i.val
public instance supportedDecidable (m i : Fin 16) : Decidable (supported m i) :=
  inferInstanceAs (Decidable (_ = _))

/-- The subgroup on the selected binary coordinates. -/
@[expose] public def elementarySpan (hS : Nat.card sylowCandidate = 128) (m : Fin 16) : Subgroup Model where
  carrier := {x | ∃ i : Fin 16, supported m i ∧ elementaryElement i = x}
  one_mem' := ⟨0, by simp [supported], elementaryElement_zero⟩
  mul_mem' := by
    rintro x y ⟨i, hi, rfl⟩ ⟨j, hj, rfl⟩
    have ht : ∀ m i j : Fin 16, supported m i → supported m j →
        supported m (xorIndex i j) := by decide +kernel
    exact ⟨xorIndex i j, ht m i j hi hj, elementaryElement_mul hS i j⟩
  inv_mem' := by
    rintro x ⟨i, hi, rfl⟩
    exact ⟨i, hi, (elementaryElement_inv hS i).symm⟩

public theorem elementaryWord_mem (H : Subgroup Model) (w : List (Fin 4))
    (hw : ∀ j ∈ w, elementaryGenerator j ∈ H) : evalWord elementaryGenerator w ∈ H := by
  induction w with
  | nil => exact H.one_mem
  | cons j w ih =>
    exact H.mul_mem (hw j (List.mem_cons_self ..))
      (ih (fun k hk => hw k (List.mem_cons_of_mem _ hk)))

/-- An overgroup containing the selected generators contains their binary span. -/
public theorem elementarySpan_le (hS : Nat.card sylowCandidate = 128) (m : Fin 16)
    (H : Subgroup Model) (h : ∀ j : Fin 4, m.val.testBit j.val = true →
      elementaryGenerator j ∈ H) : elementarySpan hS m ≤ H := by
  rintro x ⟨i, hi, rfl⟩
  apply elementaryWord_mem
  intro j hj
  have ht : ∀ m i : Fin 16, supported m i → ∀ j ∈ elementaryWord i,
      m.val.testBit j.val = true := by decide +kernel
  exact h j (ht m i hi j hj)

public theorem generator_mem_elementarySpan (hS : Nat.card sylowCandidate = 128)
    (m : Fin 16) (j : Fin 4) (hj : m.val.testBit j.val = true) :
    elementaryGenerator j ∈ elementarySpan hS m := by
  have ht : ∀ m : Fin 16, ∀ j : Fin 4, m.val.testBit j.val = true →
      supported m (basisMask j) := by decide +kernel
  exact ⟨basisMask j, ht m j hj, elementaryElement_basis j⟩

/-- All four coordinates generate exactly the unchanged elementary candidate. -/
public theorem elementarySpan_full (hS : Nat.card sylowCandidate = 128) :
    elementarySpan hS 15 = elementaryCandidate := by
  apply le_antisymm
  · exact elementarySpan_le hS _ _ (fun j _ => elementaryGenerator_mem j)
  · apply (closure_le _).mpr
    rintro _ ⟨j, rfl⟩
    apply generator_mem_elementarySpan hS
    fin_cases j <;> decide

/-- Exhaustion of the elementary candidate by the sixteen explicit words. -/
public theorem mem_elementaryCandidate_iff (hS : Nat.card sylowCandidate = 128) (x : Model) :
    x ∈ elementaryCandidate ↔ ∃ i : Fin 16, elementaryElement i = x := by
  rw [← elementarySpan_full hS]
  change (∃ i : Fin 16, supported 15 i ∧ elementaryElement i = x) ↔ _
  have ht : ∀ i : Fin 16, supported 15 i := by decide +kernel
  exact ⟨fun ⟨i, _, hi⟩ => ⟨i, hi⟩, fun ⟨i, hi⟩ => ⟨i, ht i, hi⟩⟩

/-- The fixed elementary candidate centralizes itself in the ambient model. -/
public theorem elementaryCandidate_commutative (hS : Nat.card sylowCandidate = 128) :
    elementaryCandidate ≤ centralizer (elementaryCandidate : Set Model) := by
  intro x hx y hy
  obtain ⟨i, rfl⟩ := (mem_elementaryCandidate_iff hS x).mp hx
  obtain ⟨j, rfl⟩ := (mem_elementaryCandidate_iff hS y).mp hy
  have ht : ∀ i j : Fin 16, xorIndex i j = xorIndex j i := by decide +kernel
  rw [← elementaryElement_mul hS, ← elementaryElement_mul hS, ht]

/-- The published representatives use coordinate masks 1, 3, 5, 14, and 15. -/
@[expose] public def representativeMask : Fin 5 → Fin 16 := ![1, 3, 5, 14, 15]

/-- The binary spans are exactly the five published subgroups. -/
public theorem elementarySpan_representative (hS : Nat.card sylowCandidate = 128) (i : Fin 5) :
    elementarySpan hS (representativeMask i) = elementaryRepresentative i := by
  have hgen (m : Fin 16) (j : Fin 4) (hj : m.val.testBit j.val = true) :=
    generator_mem_elementarySpan hS m j hj
  fin_cases i
  · apply le_antisymm
    · apply elementarySpan_le
      intro j hj
      fin_cases j
      · change elementaryGenerator 0 ∈ zpowers a
        rw [elementaryGenerator_zero]
        exact mem_zpowers a
      all_goals contradiction
    · apply zpowers_le.mpr
      rw [← elementaryGenerator_zero]
      exact hgen 1 0 (by decide)
  · apply le_antisymm
    · apply elementarySpan_le
      intro j hj
      fin_cases j
      · exact mem_sup_left (mem_zpowers _)
      · exact mem_sup_right (mem_zpowers _)
      all_goals contradiction
    · exact sup_le (zpowers_le.mpr (hgen 3 0 (by decide)))
        (zpowers_le.mpr (hgen 3 1 (by decide)))
  · apply le_antisymm
    · apply elementarySpan_le
      intro j hj
      fin_cases j
      · exact mem_sup_left (mem_zpowers _)
      · contradiction
      · exact mem_sup_right (mem_zpowers _)
      · contradiction
    · exact sup_le (zpowers_le.mpr (hgen 5 0 (by decide)))
        (zpowers_le.mpr (hgen 5 2 (by decide)))
  · apply le_antisymm
    · apply elementarySpan_le
      intro j hj
      fin_cases j
      · contradiction
      · exact mem_sup_left (mem_sup_left (mem_zpowers _))
      · exact mem_sup_left (mem_sup_right (mem_zpowers _))
      · exact mem_sup_right (mem_zpowers _)
    · exact sup_le (sup_le (zpowers_le.mpr (hgen 14 1 (by decide)))
        (zpowers_le.mpr (hgen 14 2 (by decide)))) (zpowers_le.mpr (hgen 14 3 (by decide)))
  · exact elementarySpan_full hS

/-- Exact membership in every published representative. -/
public theorem mem_elementaryRepresentative_iff (hS : Nat.card sylowCandidate = 128)
    (i : Fin 5) (x : Model) : x ∈ elementaryRepresentative i ↔
      ∃ j : Fin 16, supported (representativeMask i) j ∧ elementaryElement j = x := by
  rw [← elementarySpan_representative hS]
  rfl

public theorem elementaryElement_mem (hS : Nat.card sylowCandidate = 128) (i : Fin 16) :
    elementaryElement i ∈ elementaryCandidate :=
  (mem_elementaryCandidate_iff hS _).mpr ⟨i, rfl⟩

/-- The first four affine generators are the four elementary generators in
reverse order, so the fixed elementary candidate lies in the affine candidate. -/
public theorem elementaryCandidate_le_affineCandidate :
    elementaryCandidate ≤ affineCandidate := by
  apply (closure_le _).mpr
  rintro _ ⟨j, rfl⟩
  fin_cases j
  · exact affineGenerator_mem 3
  · exact affineGenerator_mem 2
  · exact affineGenerator_mem 1
  · exact affineGenerator_mem 0

/-- The allowed ambient involution-centralizer bound places every element of E
in the fixed centralizer candidate. This also permits point-separation checks
between centralizer words and elementary words. -/
public theorem elementaryCandidate_le_localFamily_zero
    (hS : Nat.card sylowCandidate = 128)
    (hC : centralizer ({a} : Set Model) ≤ localFamily 0) :
    elementaryCandidate ≤ localFamily 0 := by
  have ha : a ∈ elementaryCandidate := by
    simpa only [elementaryGenerator_zero] using elementaryGenerator_mem 0
  exact (elementaryCandidate_commutative hS).trans
    ((centralizer_le (Set.singleton_subset_iff.mpr ha)).trans hC)

/-- The fixed elementary candidate has order sixteen. -/
public theorem elementaryCandidate_card (hS : Nat.card sylowCandidate = 128) :
    Nat.card elementaryCandidate = 16 := by
  let f : Fin 16 → elementaryCandidate := fun i => ⟨elementaryElement i, elementaryElement_mem hS i⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i j h
      exact elementaryElement_injective hS (congrArg Subtype.val h)
    · intro x
      obtain ⟨i, hi⟩ := (mem_elementaryCandidate_iff hS x).mp x.property
      exact ⟨i, Subtype.ext hi⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_fin]

end CFSG.Quasithin.MainConverse.SporadicLocal.J3Coverage.RepresentativeCalculations
