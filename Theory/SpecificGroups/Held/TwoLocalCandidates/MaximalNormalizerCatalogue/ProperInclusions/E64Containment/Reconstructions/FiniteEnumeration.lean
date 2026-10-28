module
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ElementaryWords
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.CentralWord
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ProperInclusions.E64Containment.Signatures
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ProperInclusions.WordTests
public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.Calculations.TwoGroup.Tables

/-!
# Finite enumeration tools for Held signature reconstruction

A finite list of literal row products exhausts a row once it contains every
published generator and is closed under multiplication and inversion. An
injective enumeration then transports the translation-overlap count to its
finite index set. These lemmas also reduce equality of a signature span to
checked products in the smaller row and generation in the opposite direction.

Sources: ATLAS HeG1-p2058B0 and the unchanged catalogue words; GLS3 Table 5.3p.
-/

public section
namespace Held.TwoLocalCandidates.MaximalNormalizerCatalogue.E64Containment.Reconstructions
open Subgroup ProperInclusions LocalPairs.SylowGeometry.Calculations
open LocalPairs.SylowGeometry.Calculations.TwoGroup.Tables

@[expose] def tableGen : Fin 4 → Equiv.Perm (Fin 2058)
 | 0 => g0 | 1 => g1 | 2 => g2 | _ => g3
@[expose] def tableWord (w : List ℤ) : Equiv.Perm (Fin 2058) :=
 (w.map (fun k => if k < 0 then (tableGen (Fin.ofNat 4 (k.natAbs - 1)))⁻¹
   else tableGen (Fin.ofNat 4 (k.natAbs - 1)))).prod

theorem tableGen_eq (i : Fin 4) : tableGen i = representation (generator i) := by
  fin_cases i
  · exact g0_eq
  · exact g1_eq
  · exact g2_eq
  · exact g3_eq

theorem tableWord_eq (w : List ℤ) : tableWord w = representation (word w : He) := by
  change tableWord w = (representation.comp representative.subtype) (word w)
  simp only [tableWord, word, map_list_prod, List.map_map, Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro n _
  simp only [letter]
  split_ifs <;> simp only [map_inv, MonoidHom.coe_comp, Function.comp_apply,
    tableGen_eq] <;> rfl

@[expose] def permProduct (j : Fin 22) (is : List ℕ) : Equiv.Perm (Fin 2058) :=
  (is.map (fun i => tableWord ((generatorWords j)[i]?.getD []))).prod

theorem permProduct_eq (j : Fin 22) (is : List ℕ) :
    permProduct j is = representation (rowProduct j is) := by
  simp only [permProduct, rowProduct, rowElement, map_list_prod, List.map_map,
    Function.comp_def, tableWord_eq]

theorem fixedPointCount_eq (x : He) (p : Equiv.Perm (Fin 2058))
    (hp : p = representation x) :
    fixedPointCount x = (List.finRange 2058).countP (fun v => decide (p v = v)) := by
  rw [fixedPointCount, Fintype.card_subtype, ← List.toFinset_finRange 2058,
    (List.nodup_finRange 2058).card_eq_countP, hp]

/-- Multiplication and inversion closure certify exhaustion of the literal row. -/
theorem enumeration {N : ℕ} (j : Fin 22) (e : Fin N → He)
    (emem : ∀ i, e i ∈ ambient j)
    (one : ∃ i, e i = 1)
    (mul : ∀ i k, ∃ l, e i * e k = e l)
    (inv : ∀ i, ∃ k, (e i)⁻¹ = e k)
    (gens : ∀ w ∈ generatorWords j, ∃ i, e i = (word w : He)) :
    ∀ x, x ∈ ambient j ↔ ∃ i, e i = x := by
  let K : Subgroup He := {
    carrier := Set.range e
    one_mem' := one
    mul_mem' := by
      rintro _ _ ⟨i, rfl⟩ ⟨k, rfl⟩
      obtain ⟨l, hl⟩ := mul i k
      exact ⟨l, hl.symm⟩
    inv_mem' := by
      rintro _ ⟨i, rfl⟩
      obtain ⟨k, hk⟩ := inv i
      exact ⟨k, hk.symm⟩ }
  have hle : ambient j ≤ K := (ambient_le_iff j K).mpr gens
  intro x
  exact ⟨fun hx => hle hx, fun ⟨i, hi⟩ => hi ▸ emem i⟩

/-- Transport the overlap count across an exhaustive, injective row enumeration. -/
theorem overlapCount_eq {N : ℕ} (j : Fin 22) (e : Fin N → He)
    (emem : ∀ i, e i ∈ ambient j)
    (inj : Function.Injective e)
    (cover : ∀ x ∈ ambient j, ∃ i, e i = x)
    (c : Fin N → ℕ) (hc : ∀ i, fixedPointCount (e i) = c i)
    (m : Fin N → Fin N → Fin N) (hm : ∀ i k, e i * e k = e (m i k))
    (i : Fin N) : overlapCount (ambient j) (e i) =
      (List.finRange N).countP (fun k => decide (c k = 154 ∧ c (m i k) = 154)) := by
  let f : Fin N ≃ ambient j := Equiv.ofBijective (fun k => ⟨e k, emem k⟩)
    ⟨fun a b h => inj (congrArg Subtype.val h), fun x => by
      obtain ⟨k, hk⟩ := cover x.val x.property
      exact ⟨k, Subtype.ext hk⟩⟩
  have he : {k : Fin N // c k = 154 ∧ c (m i k) = 154} ≃
      {y : ambient j // fixedPointCount y.val = 154 ∧
        fixedPointCount (e i * y.val) = 154} :=
    Equiv.subtypeEquiv f (fun k => by
      change (_ ∧ _) ↔ (fixedPointCount (e k) = 154 ∧ fixedPointCount (e i * e k) = 154)
      rw [hm, hc, hc])
  unfold overlapCount
  rw [← Nat.card_congr he, Nat.card_eq_fintype_card, Fintype.card_subtype,
    ← List.toFinset_finRange N, (List.nodup_finRange N).card_eq_countP]

/-- Both containments for a signature span, using an exhaustive enumeration. -/
theorem span_eq {N : ℕ} (j k : Fin 22) (e : Fin N → He)
    (cover : ∀ x ∈ ambient j, ∃ i, e i = x)
    (s : He → Prop) (p : Fin N → Prop) (hp : ∀ i, s (e i) ↔ p i)
    (upper : ∀ i, p i → e i ∈ ambient k)
    (lower : ∀ w ∈ generatorWords k,
      (word w : He) ∈ closure {x | x ∈ ambient j ∧ s x}) :
    closure {x | x ∈ ambient j ∧ s x} = ambient k := by
  apply le_antisymm
  · apply (closure_le _).mpr
    rintro x ⟨hx, hs⟩
    obtain ⟨i, rfl⟩ := cover x hx
    exact upper i ((hp i).mp hs)
  · exact (ambient_le_iff k _).mpr lower

end Held.TwoLocalCandidates.MaximalNormalizerCatalogue.E64Containment.Reconstructions
