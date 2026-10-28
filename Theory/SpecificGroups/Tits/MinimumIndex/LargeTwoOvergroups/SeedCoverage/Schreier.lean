module

public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedCoverage.Nodes

/-!
# Soundness of the binary descent certificates

Every maximal subgroup of a finite two-group has index two. Its membership
signature on the parent generators gives a Schreier generating family. Word
certificates in both directions identify the conjugated family with a child
node. All conjugators are actual elements of the marked Sylow subgroup.

Source: Schreier's lemma, via `SubgroupEnumerationBinary`, applied to the
Parrott (1972), §5 generators. No exhaustive discovery output is assumed.
-/

@[expose] public section
namespace Tits.MinimumIndex.LargeTwoOvergroups.SeedCoverage
open Theory.GroupTheory Theory.GroupTheory.SubgroupEnumeration

variable {G : Type*} [Group G]

def schreier {n : Nat} (s : Fin n → G) (σ : Fin n → Bool) (j : Fin n) :
    Fin (n + n) → G :=
  Fin.addCases (fun k => binarySchreierGenerator s (s j) σ (false, k))
    (fun k => binarySchreierGenerator s (s j) σ (true, k))

theorem range_schreier {n : Nat} (s : Fin n → G) (σ : Fin n → Bool) (j : Fin n) :
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

theorem pointHom_schreier {n : Nat} (s : Fin n → S) (σ : Fin n → Bool) (j : Fin n) :
    (fun k => pointHom (schreier s σ j k)) = schreier (fun k => pointHom (s k)) σ j := by
  funext k
  refine Fin.addCases (fun k => ?_) (fun k => ?_) k <;>
    simp only [schreier, Fin.addCases_left, Fin.addCases_right, binarySchreierGenerator] <;>
    split <;> simp only [map_mul, map_inv]

def signatureIndex {n : Nat} (σ : Fin n → Bool) : Nat :=
  (List.ofFn σ).foldr (fun b v => b.toNat + 2 * v) 0

structure BranchData (l n : Nat) where
  target : Fin (nodeCount (l + 1))
  conjugator : Fin 2048
  words : ClosureWords (n + n) (nodeIndices (l + 1) target).length

def BranchData.Valid {l n : Nat} (d : BranchData l n)
    (s : Fin n → Equiv.Perm (Fin 1600)) (σ : Fin n → Bool) (j : Fin n) : Prop :=
  PointValid d.words (schreier s σ j) (fastGenerator (l + 1) d.target) (perm d.conjugator)

instance {l n : Nat} (d : BranchData l n)
    (s : Fin n → Equiv.Perm (Fin 1600)) (σ : Fin n → Bool) (j : Fin n) :
    Decidable (d.Valid s σ j) := inferInstanceAs (Decidable (PointValid _ _ _ _))

theorem BranchData.sound {l n : Nat} (d : BranchData l n)
    (s : Fin n → S) (σ : Fin n → Bool) (j : Fin n)
    (h : d.Valid (fun k => pointHom (s k)) σ j) :
    Represented (node (l + 1)) (Subgroup.closure (Set.range (schreier s σ j))) := by
  refine ⟨d.target, element d.conjugator, ?_⟩
  apply PointValid.sound
  simpa only [BranchData.Valid, pointHom_schreier, pointHom_generator, pointHom_element] using h

def Step (l : Nat) (i : Fin (nodeCount l)) : Prop :=
  ∀ H : Subgroup S, H ⋖ node l i → Represented (node (l + 1)) H

/-- Checking all binary signatures proves coverage of actual maximal subgroups. -/
theorem step_of_checks (l : Nat) (i : Fin (nodeCount l))
    (pivot : (Fin (nodeIndices l i).length → Bool) → Fin (nodeIndices l i).length)
    (data : (Fin (nodeIndices l i).length → Bool) → BranchData l (nodeIndices l i).length)
    (hcheck : ∀ σ, (∃ k, σ k = true) →
      σ (pivot σ) = true ∧ (data σ).Valid (fastGenerator l i) σ (pivot σ)) : Step l i := by
  classical
  intro H hH
  let s := generator l i
  let σ : Fin (nodeIndices l i).length → Bool := fun k => decide (s k ∉ H)
  have hex : ∃ k, σ k = true := by
    by_contra hh
    have hle : node l i ≤ H := by
      apply (Subgroup.closure_le _).mpr
      rintro _ ⟨k, rfl⟩
      by_contra hk
      change s k ∉ H at hk
      exact hh ⟨k, by simpa only [σ, decide_eq_true_eq] using hk⟩
    exact hH.lt.not_ge hle
  obtain ⟨hp, hd⟩ := hcheck σ hex
  have hout : s (pivot σ) ∉ H := by simpa only [σ, decide_eq_true_eq] using hp
  have he := binarySchreier_eq_relative hH.le
    (relIndex_two_of_covBy (IsPGroup.of_card (n := 11) atlas1600SylowTwoSubgroup_card) hH)
    s rfl (s (pivot σ)) (Subgroup.subset_closure ⟨pivot σ, rfl⟩) hout σ
    (fun k => by simp only [σ, decide_eq_true_eq])
  rw [← he, ← range_schreier]
  apply (data σ).sound
  simpa only [s, pointHom_generator] using hd

end Tits.MinimumIndex.LargeTwoOvergroups.SeedCoverage
end
