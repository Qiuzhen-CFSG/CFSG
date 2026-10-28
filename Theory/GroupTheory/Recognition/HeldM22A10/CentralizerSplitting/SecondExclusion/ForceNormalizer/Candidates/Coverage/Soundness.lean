module

public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.SecondExclusion.ForceNormalizer.Candidates.Descent
public import Theory.GroupTheory.SubgroupEnumerationBinary
public import Theory.GroupTheory.SubgroupClosureWords

/-!
# Soundness of finite certificates for the Held candidate census

Binary Schreier generators recover every maximal subgroup of each parent.
Word equations certify the generating families and conjugacies. Noncentric
branches have an actual commuting element outside a finite set closed under
right multiplication by every generator and its inverse; closure induction
proves nonmembership. No radicality condition is used.

Source: Schreier's lemma and elementary closure induction, for the intermediate
calculation in Huppert--Blackburn III, XII.1.18(b), printed p.314. The binary
indexing follows the existing `ReeTwo.SmallEvenMaximalBranchCertificates`.
-/

@[expose] public section
namespace Theory.GroupTheory.HeldM22A10.SecondExclusion.ForceNormalizer.Candidates.CoverageCertificate
open Subgroup SubgroupEnumeration

abbrev S := Model.sylowSubgroup

def signatureIndex {n : Nat} (σ : Fin n → Bool) : Nat :=
  (List.ofFn σ).foldr (fun b v => b.toNat + 2 * v) 0

def schreier {n : Nat} (s : Fin n → S) (σ : Fin n → Bool) (j : Fin n) :
    Fin (n + n) → S :=
  Fin.addCases (fun k => binarySchreierGenerator s (s j) σ (false, k))
    (fun k => binarySchreierGenerator s (s j) σ (true, k))

theorem range_schreier {n : Nat} (s : Fin n → S) (σ : Fin n → Bool) (j : Fin n) :
    Set.range (schreier s σ j) = Set.range (binarySchreierGenerator s (s j) σ) := by
  ext x
  constructor
  · rintro ⟨k, rfl⟩
    refine Fin.addCases (fun k => ?_) (fun k => ?_) k
    · exact ⟨(false, k), by simp only [schreier, Fin.addCases_left]⟩
    · exact ⟨(true, k), by simp only [schreier, Fin.addCases_right]⟩
  · rintro ⟨⟨b, k⟩, rfl⟩
    cases b
    · exact ⟨k.castAdd n, by simp only [schreier, Fin.addCases_left]⟩
    · exact ⟨k.natAdd n, by simp only [schreier, Fin.addCases_right]⟩

/-- A finite set containing the generated subgroup, with checked transitions. -/
structure RangeTable (n : Nat) where
  size : Nat
  index : Fin size → Fin 128
  base : Fin size
  next : Fin size → Fin n → Fin size
  prev : Fin size → Fin n → Fin size

def RangeTable.Valid {n : Nat} (d : RangeTable n) (s : Fin n → S) : Prop :=
  Model.sylowElement (d.index d.base) = 1 ∧
    (∀ a k, Model.sylowElement (d.index (d.next a k)) =
      Model.sylowElement (d.index a) * s k) ∧
    ∀ a k, d.next (d.prev a k) k = a

instance instDecidableRangeTableValid {n : Nat} (d : RangeTable n) (s : Fin n → S) : Decidable (d.Valid s) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

theorem RangeTable.sound {n : Nat} (d : RangeTable n) (s : Fin n → S)
    (h : d.Valid s) {x : S} (hx : x ∈ closure (Set.range s)) :
    ∃ a, Model.sylowElement (d.index a) = x := by
  induction hx using Subgroup.closure_induction_right with
  | one => exact ⟨d.base, h.1⟩
  | mul_right x hx y hy ih =>
    obtain ⟨a, rfl⟩ := ih
    obtain ⟨k, rfl⟩ := hy
    exact ⟨d.next a k, h.2.1 a k⟩
  | mul_inv_cancel x hx y hy ih =>
    obtain ⟨a, rfl⟩ := ih
    obtain ⟨k, rfl⟩ := hy
    refine ⟨d.prev a k, ?_⟩
    apply (eq_mul_inv_iff_mul_eq).mpr
    have he := h.2.1 (d.prev a k) k
    rw [h.2.2 a k] at he
    exact he.symm

/-- Every finite branch is either pruned by eligibility or represented. -/
def Classified (H : Subgroup S) : Prop :=
  H ≤ kernel ∨ (∃ c, c ∈ centralizer (H : Set S) ∧ c ∉ H) ∨
    Represented representative H

inductive BranchData (n : Nat) where
  | inside
  | represented (index : Fin 45) (conjugator : Fin 128) (words : ClosureWords (n + n) 7)
  | noncentric (witness : Fin 128) (table : RangeTable (n + n))

def BranchData.Valid {n : Nat} (d : BranchData n) (s : Fin n → S)
    (σ : Fin n → Bool) (j : Fin n) : Prop :=
  let a := schreier s σ j
  match d with
  | .inside => ∀ k, (a k : NonsplitModels.Second) ∈ Model.transferSubgroup
  | .represented i c w =>
      w.Valid a (generator i) (MulAut.conj (Model.sylowElement c)).toMonoidHom
  | .noncentric c t => t.Valid a ∧ (∀ k, t.index k ≠ c) ∧
      ∀ k, a k * Model.sylowElement c = Model.sylowElement c * a k

instance instDecidableBranchValid {n : Nat} (d : BranchData n) (s : Fin n → S)
    (σ : Fin n → Bool) (j : Fin n) : Decidable (d.Valid s σ j) := by
  cases d <;> unfold BranchData.Valid <;> infer_instance

theorem BranchData.sound {n : Nat} (d : BranchData n) (s : Fin n → S)
    (σ : Fin n → Bool) (j : Fin n) (h : d.Valid s σ j) :
    Classified (closure (Set.range (schreier s σ j))) := by
  cases d with
  | inside =>
    left
    rw [closure_le]
    rintro _ ⟨k, rfl⟩
    exact h k
  | represented i c w =>
    right; right
    refine ⟨i, Model.sylowElement c, ?_⟩
    rw [representative_eq_closure]
    exact w.sound _ _ _ h
  | noncentric c t =>
    right; left
    refine ⟨Model.sylowElement c, ?_, ?_⟩
    · rw [centralizer_closure, mem_centralizer_iff]
      rintro _ ⟨k, rfl⟩
      exact h.2.2 k
    · intro hx
      obtain ⟨a, ha⟩ := t.sound _ h.1 hx
      exact h.2.1 a (Model.sylowElement_bijective.1 ha)

/-- Word equations identify a reduced generating family with the fixed entry. -/
theorem generated_of_words {n : Nat} (i : Fin 45) (s : Fin n → S)
    (w : ClosureWords n 7) (h : w.Valid s (generator i) (MonoidHom.id S)) :
    closure (Set.range s) = representative i := by
  rw [representative_eq_closure]
  simpa only [Subgroup.map_id] using w.sound _ _ _ h

/-- Every actual maximal subgroup has the membership signature used by a branch. -/
theorem classify_of_checks {n : Nat} (i : Fin 45) (s : Fin n → S)
    (hs : closure (Set.range s) = representative i)
    (pivot : (Fin n → Bool) → Fin n) (data : (Fin n → Bool) → BranchData n)
    (hp : ∀ σ : Fin n → Bool, (∃ k, σ k = true) → σ (pivot σ) = true)
    (hd : ∀ σ : Fin n → Bool, (∃ k, σ k = true) → (data σ).Valid s σ (pivot σ))
    (H : Subgroup S) (hH : H ⋖ representative i) : Classified H := by
  classical
  let σ : Fin n → Bool := fun k => decide (s k ∉ H)
  have hex : ∃ k, σ k = true := by
    by_contra hh
    have hle : representative i ≤ H := by
      rw [← hs, closure_le]
      rintro _ ⟨k, rfl⟩
      by_contra hk
      change s k ∉ H at hk
      exact hh ⟨k, by simpa only [σ, decide_eq_true_eq] using hk⟩
    exact hH.lt.not_ge hle
  have hout : s (pivot σ) ∉ H := by simpa only [σ, decide_eq_true_eq] using hp σ hex
  have hL := binarySchreier_eq_relative hH.le
    (relIndex_two_of_covBy (IsPGroup.of_card (n := 7) Model.sylowSubgroup_card) hH) s hs
    (s (pivot σ)) (hs ▸ subset_closure ⟨pivot σ, rfl⟩) hout σ
    (fun k => by simp only [σ, decide_eq_true_eq])
  have hc := (data σ).sound s σ (pivot σ) (hd σ hex)
  rwa [range_schreier, hL] at hc

end Theory.GroupTheory.HeldM22A10.SecondExclusion.ForceNormalizer.Candidates.CoverageCertificate
