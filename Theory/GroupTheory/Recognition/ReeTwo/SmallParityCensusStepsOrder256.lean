module

public import Theory.GroupTheory.Recognition.ReeTwo.SmallParityCensusNodes
public import Theory.GroupTheory.SubgroupEnumerationBinary
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
/-!
# Maximal parity census steps at nodes 29–60

A maximal subgroup has relative index two. Its actual membership signature
on a small generating family determines binary Schreier generators, using the
first outside generator as pivot. Every nonzero signature is checked: the
Schreier subgroup is contained in parity, has an outside centralizer element,
or is conjugate to a prescribed census node.

Positive word identities prove both directions of every generator change and
conjugacy. For noncentric branches, a finite table contains the identity and
is closed under right multiplication by each Schreier generator and inverse;
closure induction therefore proves that the witness is outside the subgroup.
Commutation is checked separately on the Schreier generators. None of these
arguments assumes the diagnostic parent order or a Frattini-survival property.

Source: Shinoda (1975), (2.3), pp. 81–82, via the verified root multiplication
and the fixed words of `SmallParityCensusNodes`. GAP selects the words and
tables; every identity and finite check below is verified by Lean's kernel.
The coordinate encoding uses bits 0–9 for the core and bits 10–11 for the
cyclic-four coordinate. Conjugators act as `g * x * g⁻¹`.
-/

open Theory.GroupTheory Theory.GroupTheory.SubgroupEnumeration
set_option maxRecDepth 100000
namespace ReeTwo.SylowModel
set_option maxHeartbeats 1600000 in
private theorem closure_le_words {n m : ℕ} (s : Fin n → SylowModel)
    (t : Fin m → SylowModel) (w : Fin n → List (Fin m))
    (hw : ∀ i, s i = evalWord t (w i)) :
    Subgroup.closure (Set.range s) ≤ Subgroup.closure (Set.range t) := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨i, rfl⟩
  rw [hw i]
  exact evalWord_mem t (Subgroup.closure (Set.range t)) (fun j => Subgroup.subset_closure ⟨j, rfl⟩) _

set_option maxHeartbeats 1600000 in
private theorem closure_eq_words {n m : ℕ} (s : Fin n → SylowModel)
    (t : Fin m → SylowModel) (w : Fin n → List (Fin m))
    (v : Fin m → List (Fin n))
    (hw : ∀ i, s i = evalWord t (w i)) (hv : ∀ i, t i = evalWord s (v i)) :
    Subgroup.closure (Set.range s) = Subgroup.closure (Set.range t) :=
  le_antisymm (closure_le_words s t w hw) (closure_le_words t s v hv)

set_option maxHeartbeats 1600000 in
private theorem outside_of_table {ι : Type} {r : ℕ} (s : ι → SylowModel)
    (a : Fin r → SylowModel) (base : Fin r) (next prev : Fin r → ι → Fin r)
    (hone : a base = 1)
    (hmul : ∀ k j, a k * s j = a (next k j))
    (hinv : ∀ k j, a k * (s j)⁻¹ = a (prev k j))
    (c : SylowModel) (hc : ∀ k, a k ≠ c) :
    c ∉ Subgroup.closure (Set.range s) := by
  intro h
  have hr : c ∈ Set.range a := by
    clear hc
    induction h using Subgroup.closure_induction_right with
    | one => exact ⟨base, hone⟩
    | mul_right x hx y hy ih =>
      obtain ⟨k, rfl⟩ := ih
      obtain ⟨j, rfl⟩ := hy
      exact ⟨next k j, (hmul k j).symm⟩
    | mul_inv_cancel x hx y hy ih =>
      obtain ⟨k, rfl⟩ := ih
      obtain ⟨j, rfl⟩ := hy
      exact ⟨prev k j, (hinv k j).symm⟩
  obtain ⟨k, hk⟩ := hr
  exact hc k hk

set_option maxHeartbeats 1600000 in
private theorem centralizes_generators {ι : Type} (s : ι → SylowModel)
    (c : SylowModel) (hc : ∀ j, s j * c = c * s j) :
    c ∈ Subgroup.centralizer (Subgroup.closure (Set.range s) : Set SylowModel) := by
  rw [Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
  rintro _ ⟨j, rfl⟩
  exact hc j

private def binaryFamily {n : ℕ} (s : Fin n → SylowModel) (t : SylowModel)
    (σ : Fin n → Bool) : Fin (n+n) → SylowModel :=
  Fin.addCases (fun i => binarySchreierGenerator s t σ (false, i))
    (fun i => binarySchreierGenerator s t σ (true, i))
set_option maxHeartbeats 1600000 in
private theorem binaryFamily_range {n : ℕ} (s : Fin n → SylowModel) (t : SylowModel)
    (σ : Fin n → Bool) : Set.range (binaryFamily s t σ) =
    Set.range (binarySchreierGenerator s t σ) := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    induction i using Fin.addCases with
    | left i => exact ⟨(false, i), by simp only [binaryFamily, Fin.addCases_left]⟩
    | right i => exact ⟨(true, i), by simp only [binaryFamily, Fin.addCases_right]⟩
  · rintro ⟨⟨b, i⟩, rfl⟩
    cases b
    · exact ⟨Fin.castAdd n i, by simp only [binaryFamily, Fin.addCases_left]⟩
    · exact ⟨Fin.natAdd n i, by simp only [binaryFamily, Fin.addCases_right]⟩

set_option maxHeartbeats 1600000 in
private theorem step_first {n : ℕ} (i : Fin 131) (s : Fin n → SylowModel)
    (hs : Subgroup.closure (Set.range s) = smallParityCensusNode i)
    (pivot : (Fin n → Bool) → Fin n)
    (hpivot : ∀ (σ : Fin n → Bool), (∃ j, σ j = true) → σ (pivot σ) = true)
    (check : ∀ (σ : Fin n → Bool), (∃ j, σ j = true) →
      let L := Subgroup.closure (Set.range (binaryFamily s (s (pivot σ)) σ))
      L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨
      Represented smallParityCensusNode L)
    (H : Subgroup SylowModel) (hmax : H ⋖ smallParityCensusNode i)
    (hcent : Subgroup.centralizer (H : Set SylowModel) ≤ H)
    (hpar : ¬ H ≤ character.ker) : Represented smallParityCensusNode H := by
  classical
  let σ : Fin n → Bool := fun j => decide (s j ∉ H)
  have hσ : ∀ j, σ j = true ↔ s j ∉ H := fun j => by simp [σ]
  have hn : ∃ j, σ j = true := by
    by_contra h
    have hh : smallParityCensusNode i ≤ H := by
      rw [← hs, Subgroup.closure_le]
      rintro _ ⟨j, rfl⟩
      by_contra hj
      exact h ⟨j, (hσ j).mpr hj⟩
    exact hmax.lt.not_ge hh
  have he := binarySchreier_eq_relative hmax.le
    (relIndex_two_of_covBy (IsPGroup.of_card (p := 2) (n := 12) card) hmax)
    s hs (s (pivot σ)) (hs ▸ Subgroup.subset_closure ⟨pivot σ, rfl⟩)
    ((hσ _).mp (hpivot σ hn)) σ hσ
  have hc := check σ hn
  dsimp only at hc
  rw [binaryFamily_range, he] at hc
  rcases hc with hp | ⟨c, hc, hnc⟩ | hr
  · exact (hpar hp).elim
  · exact (hnc (hcent hc)).elim
  · exact hr
private def decode (x : ℕ) : SylowModel :=
  ⟨⟨((x / 1 : ℕ) : ZMod 2), ((x / 2 : ℕ) : ZMod 2), ((x / 4 : ℕ) : ZMod 2), ((x / 8 : ℕ) : ZMod 2), ((x / 16 : ℕ) : ZMod 2), ((x / 32 : ℕ) : ZMod 2), ((x / 64 : ℕ) : ZMod 2), ((x / 128 : ℕ) : ZMod 2), ((x / 256 : ℕ) : ZMod 2), ((x / 512 : ℕ) : ZMod 2)⟩, Multiplicative.ofAdd ((x / 1024 : ℕ) : ZMod 4)⟩

private def o29 : Fin 8 → SylowModel := ![rootOne ^ 3, root 5 * root 8, rootOne ^ 2, root 4 * root 8, root 6 * root 7 * root 8, root 7 * root 8 * root 9, root 9, root 8]
set_option maxHeartbeats 1600000 in
private theorem node29 : smallParityCensusNode 29 = Subgroup.closure (Set.range o29) := by
  change Subgroup.closure ({rootOne ^ 3, root 5 * root 8, rootOne ^ 2, root 4 * root 8, root 6 * root 7 * root 8, root 7 * root 8 * root 9, root 9, root 8} : Set SylowModel) = _
  congr 1
  simp only [o29, Matrix.range_cons, Matrix.range_empty, Set.singleton_union, Set.union_empty]

private def o30 : Fin 8 → SylowModel := ![rootOne ^ 3, root 2 * root 3 * root 4 * root 7, rootOne ^ 2, root 4 * root 8, root 6 * root 7 * root 8, root 7 * root 8 * root 9, root 9, root 8]
set_option maxHeartbeats 1600000 in
private theorem node30 : smallParityCensusNode 30 = Subgroup.closure (Set.range o30) := by
  change Subgroup.closure ({rootOne ^ 3, root 2 * root 3 * root 4 * root 7, rootOne ^ 2, root 4 * root 8, root 6 * root 7 * root 8, root 7 * root 8 * root 9, root 9, root 8} : Set SylowModel) = _
  congr 1
  simp only [o30, Matrix.range_cons, Matrix.range_empty, Set.singleton_union, Set.union_empty]

private def o31 : Fin 8 → SylowModel := ![rootOne ^ 3, root 2 * root 3 * root 4 * root 5 * root 7 * root 8 * root 9, rootOne ^ 2, root 4 * root 8, root 6 * root 7 * root 8, root 7 * root 8 * root 9, root 9, root 8]
set_option maxHeartbeats 1600000 in
private theorem node31 : smallParityCensusNode 31 = Subgroup.closure (Set.range o31) := by
  change Subgroup.closure ({rootOne ^ 3, root 2 * root 3 * root 4 * root 5 * root 7 * root 8 * root 9, rootOne ^ 2, root 4 * root 8, root 6 * root 7 * root 8, root 7 * root 8 * root 9, root 9, root 8} : Set SylowModel) = _
  congr 1
  simp only [o31, Matrix.range_cons, Matrix.range_empty, Set.singleton_union, Set.union_empty]

private def o32 : Fin 8 → SylowModel := ![rootOne ^ 3 * root 5 * root 8, root 2 * root 3 * root 4 * root 7, rootOne ^ 2, root 4 * root 8, root 6 * root 7 * root 8, root 7 * root 8 * root 9, root 9, root 8]
set_option maxHeartbeats 1600000 in
private theorem node32 : smallParityCensusNode 32 = Subgroup.closure (Set.range o32) := by
  change Subgroup.closure ({rootOne ^ 3 * root 5 * root 8, root 2 * root 3 * root 4 * root 7, rootOne ^ 2, root 4 * root 8, root 6 * root 7 * root 8, root 7 * root 8 * root 9, root 9, root 8} : Set SylowModel) = _
  congr 1
  simp only [o32, Matrix.range_cons, Matrix.range_empty, Set.singleton_union, Set.union_empty]

private def o33 : Fin 8 → SylowModel := ![rootOne * root 0 * root 1 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2 * root 1 * root 3 * root 6 * root 7 * root 8 * root 9, root 4 * root 7, root 4 * root 5 * root 7 * root 9, root 6 * root 8 * root 9, root 7 * root 8, root 8 * root 9, root 9]
set_option maxHeartbeats 1600000 in
private theorem node33 : smallParityCensusNode 33 = Subgroup.closure (Set.range o33) := by
  change Subgroup.closure ({rootOne * root 0 * root 1 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2 * root 1 * root 3 * root 6 * root 7 * root 8 * root 9, root 4 * root 7, root 4 * root 5 * root 7 * root 9, root 6 * root 8 * root 9, root 7 * root 8, root 8 * root 9, root 9} : Set SylowModel) = _
  congr 1
  simp only [o33, Matrix.range_cons, Matrix.range_empty, Set.singleton_union, Set.union_empty]

private def o34 : Fin 8 → SylowModel := ![rootOne * root 0 * root 1 * root 6 * root 7 * root 9, rootOne ^ 2 * root 1 * root 3 * root 5 * root 7, root 4 * root 7 * root 9, root 4 * root 5, root 6, root 7 * root 8 * root 9, root 8 * root 9, root 9]
set_option maxHeartbeats 1600000 in
private theorem node34 : smallParityCensusNode 34 = Subgroup.closure (Set.range o34) := by
  change Subgroup.closure ({rootOne * root 0 * root 1 * root 6 * root 7 * root 9, rootOne ^ 2 * root 1 * root 3 * root 5 * root 7, root 4 * root 7 * root 9, root 4 * root 5, root 6, root 7 * root 8 * root 9, root 8 * root 9, root 9} : Set SylowModel) = _
  congr 1
  simp only [o34, Matrix.range_cons, Matrix.range_empty, Set.singleton_union, Set.union_empty]

private def o35 : Fin 8 → SylowModel := ![rootOne ^ 3 * root 3 * root 4, root 5 * root 8, rootOne ^ 2 * root 4 * root 8, root 4 * root 7, root 6 * root 7 * root 8, root 7 * root 8, root 9, root 8]
set_option maxHeartbeats 1600000 in
private theorem node35 : smallParityCensusNode 35 = Subgroup.closure (Set.range o35) := by
  change Subgroup.closure ({rootOne ^ 3 * root 3 * root 4, root 5 * root 8, rootOne ^ 2 * root 4 * root 8, root 4 * root 7, root 6 * root 7 * root 8, root 7 * root 8, root 9, root 8} : Set SylowModel) = _
  congr 1
  simp only [o35, Matrix.range_cons, Matrix.range_empty, Set.singleton_union, Set.union_empty]

private def o36 : Fin 8 → SylowModel := ![rootOne ^ 3 * root 3 * root 4, root 2 * root 3 * root 4 * root 7 * root 9, rootOne ^ 2 * root 4 * root 8, root 4 * root 7, root 6 * root 7 * root 8, root 7 * root 8, root 9, root 8]
set_option maxHeartbeats 1600000 in
private theorem node36 : smallParityCensusNode 36 = Subgroup.closure (Set.range o36) := by
  change Subgroup.closure ({rootOne ^ 3 * root 3 * root 4, root 2 * root 3 * root 4 * root 7 * root 9, rootOne ^ 2 * root 4 * root 8, root 4 * root 7, root 6 * root 7 * root 8, root 7 * root 8, root 9, root 8} : Set SylowModel) = _
  congr 1
  simp only [o36, Matrix.range_cons, Matrix.range_empty, Set.singleton_union, Set.union_empty]

private def o37 : Fin 8 → SylowModel := ![rootOne ^ 3 * root 3 * root 4, root 2 * root 3 * root 4 * root 5 * root 7 * root 8, rootOne ^ 2 * root 4 * root 8, root 4 * root 7, root 6 * root 7 * root 8, root 7 * root 8, root 9, root 8]
set_option maxHeartbeats 1600000 in
private theorem node37 : smallParityCensusNode 37 = Subgroup.closure (Set.range o37) := by
  change Subgroup.closure ({rootOne ^ 3 * root 3 * root 4, root 2 * root 3 * root 4 * root 5 * root 7 * root 8, rootOne ^ 2 * root 4 * root 8, root 4 * root 7, root 6 * root 7 * root 8, root 7 * root 8, root 9, root 8} : Set SylowModel) = _
  congr 1
  simp only [o37, Matrix.range_cons, Matrix.range_empty, Set.singleton_union, Set.union_empty]

private def o38 : Fin 8 → SylowModel := ![rootOne ^ 3 * root 3 * root 4 * root 5 * root 8, root 2 * root 3 * root 4 * root 7 * root 9, rootOne ^ 2 * root 4 * root 8, root 4 * root 7, root 6 * root 7 * root 8, root 7 * root 8, root 9, root 8]
set_option maxHeartbeats 1600000 in
private theorem node38 : smallParityCensusNode 38 = Subgroup.closure (Set.range o38) := by
  change Subgroup.closure ({rootOne ^ 3 * root 3 * root 4 * root 5 * root 8, root 2 * root 3 * root 4 * root 7 * root 9, rootOne ^ 2 * root 4 * root 8, root 4 * root 7, root 6 * root 7 * root 8, root 7 * root 8, root 9, root 8} : Set SylowModel) = _
  congr 1
  simp only [o38, Matrix.range_cons, Matrix.range_empty, Set.singleton_union, Set.union_empty]

private def o39 : Fin 8 → SylowModel := ![root 3, rootOne ^ 3, rootOne ^ 2, root 4, root 6 * root 7 * root 8, root 7 * root 8 * root 9, root 9, root 8]
set_option maxHeartbeats 1600000 in
private theorem node39 : smallParityCensusNode 39 = Subgroup.closure (Set.range o39) := by
  change Subgroup.closure ({root 3, rootOne ^ 3, rootOne ^ 2, root 4, root 6 * root 7 * root 8, root 7 * root 8 * root 9, root 9, root 8} : Set SylowModel) = _
  congr 1
  simp only [o39, Matrix.range_cons, Matrix.range_empty, Set.singleton_union, Set.union_empty]

private def o40 : Fin 8 → SylowModel := ![root 3, rootOne ^ 3 * root 5 * root 8, rootOne ^ 2, root 4, root 6 * root 7 * root 8, root 7 * root 8 * root 9, root 9, root 8]
set_option maxHeartbeats 1600000 in
private theorem node40 : smallParityCensusNode 40 = Subgroup.closure (Set.range o40) := by
  change Subgroup.closure ({root 3, rootOne ^ 3 * root 5 * root 8, rootOne ^ 2, root 4, root 6 * root 7 * root 8, root 7 * root 8 * root 9, root 9, root 8} : Set SylowModel) = _
  congr 1
  simp only [o40, Matrix.range_cons, Matrix.range_empty, Set.singleton_union, Set.union_empty]

private def o41 : Fin 8 → SylowModel := ![root 3 * root 5 * root 8, rootOne ^ 3, rootOne ^ 2, root 4, root 6 * root 7 * root 8, root 7 * root 8 * root 9, root 9, root 8]
set_option maxHeartbeats 1600000 in
private theorem node41 : smallParityCensusNode 41 = Subgroup.closure (Set.range o41) := by
  change Subgroup.closure ({root 3 * root 5 * root 8, rootOne ^ 3, rootOne ^ 2, root 4, root 6 * root 7 * root 8, root 7 * root 8 * root 9, root 9, root 8} : Set SylowModel) = _
  congr 1
  simp only [o41, Matrix.range_cons, Matrix.range_empty, Set.singleton_union, Set.union_empty]

private def o42 : Fin 8 → SylowModel := ![root 3 * root 5 * root 8, rootOne ^ 3 * root 5 * root 8, rootOne ^ 2, root 4, root 6 * root 7 * root 8, root 7 * root 8 * root 9, root 9, root 8]
set_option maxHeartbeats 1600000 in
private theorem node42 : smallParityCensusNode 42 = Subgroup.closure (Set.range o42) := by
  change Subgroup.closure ({root 3 * root 5 * root 8, rootOne ^ 3 * root 5 * root 8, rootOne ^ 2, root 4, root 6 * root 7 * root 8, root 7 * root 8 * root 9, root 9, root 8} : Set SylowModel) = _
  congr 1
  simp only [o42, Matrix.range_cons, Matrix.range_empty, Set.singleton_union, Set.union_empty]

private def o43 : Fin 8 → SylowModel := ![root 3, rootOne ^ 3, root 2 * root 3 * root 4 * root 7, rootOne ^ 2, root 4, root 7, root 9, root 8]
set_option maxHeartbeats 1600000 in
private theorem node43 : smallParityCensusNode 43 = Subgroup.closure (Set.range o43) := by
  change Subgroup.closure ({root 3, rootOne ^ 3, root 2 * root 3 * root 4 * root 7, rootOne ^ 2, root 4, root 7, root 9, root 8} : Set SylowModel) = _
  congr 1
  simp only [o43, Matrix.range_cons, Matrix.range_empty, Set.singleton_union, Set.union_empty]

private def o44 : Fin 8 → SylowModel := ![root 3 * root 6 * root 7 * root 8, rootOne ^ 3, root 2 * root 3 * root 4 * root 7, rootOne ^ 2, root 4, root 7, root 9, root 8]
set_option maxHeartbeats 1600000 in
private theorem node44 : smallParityCensusNode 44 = Subgroup.closure (Set.range o44) := by
  change Subgroup.closure ({root 3 * root 6 * root 7 * root 8, rootOne ^ 3, root 2 * root 3 * root 4 * root 7, rootOne ^ 2, root 4, root 7, root 9, root 8} : Set SylowModel) = _
  congr 1
  simp only [o44, Matrix.range_cons, Matrix.range_empty, Set.singleton_union, Set.union_empty]

private def o45 : Fin 8 → SylowModel := ![root 2 * root 4 * root 8, rootOne ^ 3, root 6 * root 7 * root 8, rootOne ^ 2, root 4, root 7, root 9, root 8]
set_option maxHeartbeats 1600000 in
private theorem node45 : smallParityCensusNode 45 = Subgroup.closure (Set.range o45) := by
  change Subgroup.closure ({root 2 * root 4 * root 8, rootOne ^ 3, root 6 * root 7 * root 8, rootOne ^ 2, root 4, root 7, root 9, root 8} : Set SylowModel) = _
  congr 1
  simp only [o45, Matrix.range_cons, Matrix.range_empty, Set.singleton_union, Set.union_empty]

private def o46 : Fin 8 → SylowModel := ![root 2 * root 4 * root 5 * root 9, rootOne ^ 3, rootOne ^ 2, root 4, root 6 * root 7 * root 8, root 7 * root 8 * root 9, root 9, root 8]
set_option maxHeartbeats 1600000 in
private theorem node46 : smallParityCensusNode 46 = Subgroup.closure (Set.range o46) := by
  change Subgroup.closure ({root 2 * root 4 * root 5 * root 9, rootOne ^ 3, rootOne ^ 2, root 4, root 6 * root 7 * root 8, root 7 * root 8 * root 9, root 9, root 8} : Set SylowModel) = _
  congr 1
  simp only [o46, Matrix.range_cons, Matrix.range_empty, Set.singleton_union, Set.union_empty]

private def o47 : Fin 8 → SylowModel := ![root 2 * root 4 * root 5 * root 9, rootOne ^ 3 * root 2 * root 3 * root 4 * root 5 * root 7 * root 8 * root 9, rootOne ^ 2, root 4, root 6 * root 7 * root 8, root 7 * root 8 * root 9, root 9, root 8]
set_option maxHeartbeats 1600000 in
private theorem node47 : smallParityCensusNode 47 = Subgroup.closure (Set.range o47) := by
  change Subgroup.closure ({root 2 * root 4 * root 5 * root 9, rootOne ^ 3 * root 2 * root 3 * root 4 * root 5 * root 7 * root 8 * root 9, rootOne ^ 2, root 4, root 6 * root 7 * root 8, root 7 * root 8 * root 9, root 9, root 8} : Set SylowModel) = _
  congr 1
  simp only [o47, Matrix.range_cons, Matrix.range_empty, Set.singleton_union, Set.union_empty]

private def o48 : Fin 8 → SylowModel := ![root 3, rootOne ^ 3 * root 5 * root 8, root 2 * root 3 * root 4 * root 7, rootOne ^ 2 * root 6 * root 7 * root 8, root 4 * root 9, root 7, root 9, root 8]
set_option maxHeartbeats 1600000 in
private theorem node48 : smallParityCensusNode 48 = Subgroup.closure (Set.range o48) := by
  change Subgroup.closure ({root 3, rootOne ^ 3 * root 5 * root 8, root 2 * root 3 * root 4 * root 7, rootOne ^ 2 * root 6 * root 7 * root 8, root 4 * root 9, root 7, root 9, root 8} : Set SylowModel) = _
  congr 1
  simp only [o48, Matrix.range_cons, Matrix.range_empty, Set.singleton_union, Set.union_empty]

private def o49 : Fin 8 → SylowModel := ![root 3 * root 6 * root 7 * root 8, rootOne ^ 3 * root 5 * root 8, root 2 * root 3 * root 4 * root 7, rootOne ^ 2 * root 6 * root 7 * root 8, root 4 * root 9, root 7, root 9, root 8]
set_option maxHeartbeats 1600000 in
private theorem node49 : smallParityCensusNode 49 = Subgroup.closure (Set.range o49) := by
  change Subgroup.closure ({root 3 * root 6 * root 7 * root 8, rootOne ^ 3 * root 5 * root 8, root 2 * root 3 * root 4 * root 7, rootOne ^ 2 * root 6 * root 7 * root 8, root 4 * root 9, root 7, root 9, root 8} : Set SylowModel) = _
  congr 1
  simp only [o49, Matrix.range_cons, Matrix.range_empty, Set.singleton_union, Set.union_empty]

private def o50 : Fin 8 → SylowModel := ![root 2 * root 4 * root 8, rootOne ^ 3 * root 5 * root 8, root 6 * root 7 * root 8, rootOne ^ 2 * root 6 * root 7 * root 8, root 4 * root 9, root 7, root 9, root 8]
set_option maxHeartbeats 1600000 in
private theorem node50 : smallParityCensusNode 50 = Subgroup.closure (Set.range o50) := by
  change Subgroup.closure ({root 2 * root 4 * root 8, rootOne ^ 3 * root 5 * root 8, root 6 * root 7 * root 8, rootOne ^ 2 * root 6 * root 7 * root 8, root 4 * root 9, root 7, root 9, root 8} : Set SylowModel) = _
  congr 1
  simp only [o50, Matrix.range_cons, Matrix.range_empty, Set.singleton_union, Set.union_empty]

private def o51 : Fin 8 → SylowModel := ![root 2 * root 4 * root 8, rootOne ^ 3, root 5 * root 8, rootOne ^ 2, root 6 * root 7 * root 8, root 8 * root 9, root 7 * root 8 * root 9, root 8]
set_option maxHeartbeats 1600000 in
private theorem node51 : smallParityCensusNode 51 = Subgroup.closure (Set.range o51) := by
  change Subgroup.closure ({root 2 * root 4 * root 8, rootOne ^ 3, root 5 * root 8, rootOne ^ 2, root 6 * root 7 * root 8, root 8 * root 9, root 7 * root 8 * root 9, root 8} : Set SylowModel) = _
  congr 1
  simp only [o51, Matrix.range_cons, Matrix.range_empty, Set.singleton_union, Set.union_empty]

private def o52 : Fin 8 → SylowModel := ![root 2 * root 4 * root 8, rootOne ^ 3, root 4 * root 5 * root 8 * root 9, rootOne ^ 2, root 6 * root 7 * root 8, root 8 * root 9, root 7 * root 8 * root 9, root 8]
set_option maxHeartbeats 1600000 in
private theorem node52 : smallParityCensusNode 52 = Subgroup.closure (Set.range o52) := by
  change Subgroup.closure ({root 2 * root 4 * root 8, rootOne ^ 3, root 4 * root 5 * root 8 * root 9, rootOne ^ 2, root 6 * root 7 * root 8, root 8 * root 9, root 7 * root 8 * root 9, root 8} : Set SylowModel) = _
  congr 1
  simp only [o52, Matrix.range_cons, Matrix.range_empty, Set.singleton_union, Set.union_empty]

private def o53 : Fin 8 → SylowModel := ![root 2 * root 8, rootOne ^ 3, root 5 * root 8, rootOne ^ 2, root 6 * root 7 * root 8, root 8 * root 9, root 7 * root 8 * root 9, root 8]
set_option maxHeartbeats 1600000 in
private theorem node53 : smallParityCensusNode 53 = Subgroup.closure (Set.range o53) := by
  change Subgroup.closure ({root 2 * root 8, rootOne ^ 3, root 5 * root 8, rootOne ^ 2, root 6 * root 7 * root 8, root 8 * root 9, root 7 * root 8 * root 9, root 8} : Set SylowModel) = _
  congr 1
  simp only [o53, Matrix.range_cons, Matrix.range_empty, Set.singleton_union, Set.union_empty]

private def o54 : Fin 8 → SylowModel := ![root 2 * root 8, rootOne ^ 3, root 4 * root 5 * root 8 * root 9, rootOne ^ 2, root 6 * root 7 * root 8, root 8 * root 9, root 7 * root 8 * root 9, root 8]
set_option maxHeartbeats 1600000 in
private theorem node54 : smallParityCensusNode 54 = Subgroup.closure (Set.range o54) := by
  change Subgroup.closure ({root 2 * root 8, rootOne ^ 3, root 4 * root 5 * root 8 * root 9, rootOne ^ 2, root 6 * root 7 * root 8, root 8 * root 9, root 7 * root 8 * root 9, root 8} : Set SylowModel) = _
  congr 1
  simp only [o54, Matrix.range_cons, Matrix.range_empty, Set.singleton_union, Set.union_empty]

private def o55 : Fin 8 → SylowModel := ![root 2 * root 4 * root 8, rootOne ^ 3, root 2 * root 3 * root 4 * root 5 * root 7 * root 8 * root 9, rootOne ^ 2, root 4 * root 6 * root 7 * root 9, root 8 * root 9, root 7 * root 8 * root 9, root 8]
set_option maxHeartbeats 1600000 in
private theorem node55 : smallParityCensusNode 55 = Subgroup.closure (Set.range o55) := by
  change Subgroup.closure ({root 2 * root 4 * root 8, rootOne ^ 3, root 2 * root 3 * root 4 * root 5 * root 7 * root 8 * root 9, rootOne ^ 2, root 4 * root 6 * root 7 * root 9, root 8 * root 9, root 7 * root 8 * root 9, root 8} : Set SylowModel) = _
  congr 1
  simp only [o55, Matrix.range_cons, Matrix.range_empty, Set.singleton_union, Set.union_empty]

private def o56 : Fin 8 → SylowModel := ![root 2 * root 4 * root 8, rootOne ^ 3, root 2 * root 3 * root 4 * root 5 * root 6 * root 9, rootOne ^ 2, root 4 * root 6 * root 7 * root 9, root 8 * root 9, root 7 * root 8 * root 9, root 8]
set_option maxHeartbeats 1600000 in
private theorem node56 : smallParityCensusNode 56 = Subgroup.closure (Set.range o56) := by
  change Subgroup.closure ({root 2 * root 4 * root 8, rootOne ^ 3, root 2 * root 3 * root 4 * root 5 * root 6 * root 9, rootOne ^ 2, root 4 * root 6 * root 7 * root 9, root 8 * root 9, root 7 * root 8 * root 9, root 8} : Set SylowModel) = _
  congr 1
  simp only [o56, Matrix.range_cons, Matrix.range_empty, Set.singleton_union, Set.union_empty]

private def o57 : Fin 8 → SylowModel := ![root 2 * root 4 * root 6 * root 7, rootOne ^ 3, root 2 * root 3 * root 4 * root 5 * root 7 * root 8 * root 9, rootOne ^ 2, root 4 * root 6 * root 7 * root 9, root 8 * root 9, root 7 * root 8 * root 9, root 8]
set_option maxHeartbeats 1600000 in
private theorem node57 : smallParityCensusNode 57 = Subgroup.closure (Set.range o57) := by
  change Subgroup.closure ({root 2 * root 4 * root 6 * root 7, rootOne ^ 3, root 2 * root 3 * root 4 * root 5 * root 7 * root 8 * root 9, rootOne ^ 2, root 4 * root 6 * root 7 * root 9, root 8 * root 9, root 7 * root 8 * root 9, root 8} : Set SylowModel) = _
  congr 1
  simp only [o57, Matrix.range_cons, Matrix.range_empty, Set.singleton_union, Set.union_empty]

private def o58 : Fin 8 → SylowModel := ![root 2 * root 4 * root 6 * root 7, rootOne ^ 3, root 2 * root 3 * root 4 * root 5 * root 6 * root 9, rootOne ^ 2, root 4 * root 6 * root 7 * root 9, root 8 * root 9, root 7 * root 8 * root 9, root 8]
set_option maxHeartbeats 1600000 in
private theorem node58 : smallParityCensusNode 58 = Subgroup.closure (Set.range o58) := by
  change Subgroup.closure ({root 2 * root 4 * root 6 * root 7, rootOne ^ 3, root 2 * root 3 * root 4 * root 5 * root 6 * root 9, rootOne ^ 2, root 4 * root 6 * root 7 * root 9, root 8 * root 9, root 7 * root 8 * root 9, root 8} : Set SylowModel) = _
  congr 1
  simp only [o58, Matrix.range_cons, Matrix.range_empty, Set.singleton_union, Set.union_empty]

private def o59 : Fin 8 → SylowModel := ![rootOne * root 0 * root 1 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8 * root 9, rootOne * root 0 * root 1 * root 2 * root 3 * root 4 * root 6 * root 8 * root 9, rootOne ^ 2 * root 1 * root 3 * root 6 * root 7 * root 8 * root 9, root 6, root 4 * root 5 * root 7 * root 9, root 7 * root 8, root 8 * root 9, root 9]
set_option maxHeartbeats 1600000 in
private theorem node59 : smallParityCensusNode 59 = Subgroup.closure (Set.range o59) := by
  change Subgroup.closure ({rootOne * root 0 * root 1 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8 * root 9, rootOne * root 0 * root 1 * root 2 * root 3 * root 4 * root 6 * root 8 * root 9, rootOne ^ 2 * root 1 * root 3 * root 6 * root 7 * root 8 * root 9, root 6, root 4 * root 5 * root 7 * root 9, root 7 * root 8, root 8 * root 9, root 9} : Set SylowModel) = _
  congr 1
  simp only [o59, Matrix.range_cons, Matrix.range_empty, Set.singleton_union, Set.union_empty]

private def o60 : Fin 8 → SylowModel := ![rootOne * root 0 * root 1 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8 * root 9, rootOne * root 0 * root 1 * root 2 * root 3 * root 7 * root 8 * root 9, rootOne ^ 2 * root 1 * root 3 * root 6 * root 7 * root 8 * root 9, root 6, root 4 * root 5 * root 7 * root 9, root 7 * root 8, root 8 * root 9, root 9]
set_option maxHeartbeats 1600000 in
private theorem node60 : smallParityCensusNode 60 = Subgroup.closure (Set.range o60) := by
  change Subgroup.closure ({rootOne * root 0 * root 1 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8 * root 9, rootOne * root 0 * root 1 * root 2 * root 3 * root 7 * root 8 * root 9, rootOne ^ 2 * root 1 * root 3 * root 6 * root 7 * root 8 * root 9, root 6, root 4 * root 5 * root 7 * root 9, root 7 * root 8, root 8 * root 9, root 9} : Set SylowModel) = _
  congr 1
  simp only [o60, Matrix.range_cons, Matrix.range_empty, Set.singleton_union, Set.union_empty]

private def o61 : Fin 7 → SylowModel := ![rootOne ^ 3, root 4 * root 8, rootOne ^ 2, root 6 * root 7 * root 8, root 9, root 7 * root 8 * root 9, root 8]
set_option maxHeartbeats 1600000 in
private theorem node61 : smallParityCensusNode 61 = Subgroup.closure (Set.range o61) := by
  change Subgroup.closure ({rootOne ^ 3, root 4 * root 8, rootOne ^ 2, root 6 * root 7 * root 8, root 9, root 7 * root 8 * root 9, root 8} : Set SylowModel) = _
  congr 1
  simp only [o61, Matrix.range_cons, Matrix.range_empty, Set.singleton_union, Set.union_empty]

private def o62 : Fin 7 → SylowModel := ![rootOne ^ 3, root 4 * root 5 * root 9, rootOne ^ 2, root 6 * root 7 * root 8, root 9, root 7 * root 8 * root 9, root 8]
set_option maxHeartbeats 1600000 in
private theorem node62 : smallParityCensusNode 62 = Subgroup.closure (Set.range o62) := by
  change Subgroup.closure ({rootOne ^ 3, root 4 * root 5 * root 9, rootOne ^ 2, root 6 * root 7 * root 8, root 9, root 7 * root 8 * root 9, root 8} : Set SylowModel) = _
  congr 1
  simp only [o62, Matrix.range_cons, Matrix.range_empty, Set.singleton_union, Set.union_empty]

private def o63 : Fin 7 → SylowModel := ![rootOne ^ 3 * root 5 * root 8, root 4 * root 8, rootOne ^ 2, root 6 * root 7 * root 8, root 9, root 7 * root 8 * root 9, root 8]
set_option maxHeartbeats 1600000 in
private theorem node63 : smallParityCensusNode 63 = Subgroup.closure (Set.range o63) := by
  change Subgroup.closure ({rootOne ^ 3 * root 5 * root 8, root 4 * root 8, rootOne ^ 2, root 6 * root 7 * root 8, root 9, root 7 * root 8 * root 9, root 8} : Set SylowModel) = _
  congr 1
  simp only [o63, Matrix.range_cons, Matrix.range_empty, Set.singleton_union, Set.union_empty]

private def o64 : Fin 7 → SylowModel := ![rootOne ^ 3, root 2 * root 3 * root 4 * root 7, rootOne ^ 2, root 4 * root 8, root 7 * root 9, root 9, root 8]
set_option maxHeartbeats 1600000 in
private theorem node64 : smallParityCensusNode 64 = Subgroup.closure (Set.range o64) := by
  change Subgroup.closure ({rootOne ^ 3, root 2 * root 3 * root 4 * root 7, rootOne ^ 2, root 4 * root 8, root 7 * root 9, root 9, root 8} : Set SylowModel) = _
  congr 1
  simp only [o64, Matrix.range_cons, Matrix.range_empty, Set.singleton_union, Set.union_empty]

private def o65 : Fin 7 → SylowModel := ![rootOne ^ 3, root 2 * root 3 * root 4 * root 5 * root 7 * root 8 * root 9, rootOne ^ 2, root 4 * root 6 * root 7 * root 9, root 8 * root 9, root 7 * root 8 * root 9, root 8]
set_option maxHeartbeats 1600000 in
private theorem node65 : smallParityCensusNode 65 = Subgroup.closure (Set.range o65) := by
  change Subgroup.closure ({rootOne ^ 3, root 2 * root 3 * root 4 * root 5 * root 7 * root 8 * root 9, rootOne ^ 2, root 4 * root 6 * root 7 * root 9, root 8 * root 9, root 7 * root 8 * root 9, root 8} : Set SylowModel) = _
  congr 1
  simp only [o65, Matrix.range_cons, Matrix.range_empty, Set.singleton_union, Set.union_empty]

private def o66 : Fin 7 → SylowModel := ![rootOne ^ 3 * root 5 * root 8, root 2 * root 3 * root 4 * root 7, rootOne ^ 2 * root 6 * root 7 * root 8, root 4 * root 8, root 7 * root 9, root 9, root 8]
set_option maxHeartbeats 1600000 in
private theorem node66 : smallParityCensusNode 66 = Subgroup.closure (Set.range o66) := by
  change Subgroup.closure ({rootOne ^ 3 * root 5 * root 8, root 2 * root 3 * root 4 * root 7, rootOne ^ 2 * root 6 * root 7 * root 8, root 4 * root 8, root 7 * root 9, root 9, root 8} : Set SylowModel) = _
  congr 1
  simp only [o66, Matrix.range_cons, Matrix.range_empty, Set.singleton_union, Set.union_empty]

private def o67 : Fin 7 → SylowModel := ![rootOne * root 0 * root 1 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2 * root 1 * root 3 * root 6 * root 7 * root 8 * root 9, root 6 * root 8 * root 9, root 4 * root 5 * root 7 * root 9, root 7 * root 8, root 8 * root 9, root 9]
set_option maxHeartbeats 1600000 in
private theorem node67 : smallParityCensusNode 67 = Subgroup.closure (Set.range o67) := by
  change Subgroup.closure ({rootOne * root 0 * root 1 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2 * root 1 * root 3 * root 6 * root 7 * root 8 * root 9, root 6 * root 8 * root 9, root 4 * root 5 * root 7 * root 9, root 7 * root 8, root 8 * root 9, root 9} : Set SylowModel) = _
  congr 1
  simp only [o67, Matrix.range_cons, Matrix.range_empty, Set.singleton_union, Set.union_empty]

private def o68 : Fin 7 → SylowModel := ![rootOne * root 0 * root 1 * root 6 * root 7 * root 9, rootOne ^ 2 * root 1 * root 3 * root 5 * root 7, root 6, root 4 * root 5, root 7 * root 8 * root 9, root 8 * root 9, root 9]
set_option maxHeartbeats 1600000 in
private theorem node68 : smallParityCensusNode 68 = Subgroup.closure (Set.range o68) := by
  change Subgroup.closure ({rootOne * root 0 * root 1 * root 6 * root 7 * root 9, rootOne ^ 2 * root 1 * root 3 * root 5 * root 7, root 6, root 4 * root 5, root 7 * root 8 * root 9, root 8 * root 9, root 9} : Set SylowModel) = _
  congr 1
  simp only [o68, Matrix.range_cons, Matrix.range_empty, Set.singleton_union, Set.union_empty]

private def o69 : Fin 7 → SylowModel := ![rootOne ^ 3 * root 3 * root 4, root 4 * root 7, rootOne ^ 2 * root 4 * root 8, root 6 * root 7 * root 8, root 9, root 7 * root 8, root 8]
set_option maxHeartbeats 1600000 in
private theorem node69 : smallParityCensusNode 69 = Subgroup.closure (Set.range o69) := by
  change Subgroup.closure ({rootOne ^ 3 * root 3 * root 4, root 4 * root 7, rootOne ^ 2 * root 4 * root 8, root 6 * root 7 * root 8, root 9, root 7 * root 8, root 8} : Set SylowModel) = _
  congr 1
  simp only [o69, Matrix.range_cons, Matrix.range_empty, Set.singleton_union, Set.union_empty]

private def o70 : Fin 7 → SylowModel := ![rootOne ^ 3 * root 3 * root 4, root 4 * root 5 * root 7 * root 8 * root 9, rootOne ^ 2 * root 4 * root 8, root 6 * root 7 * root 8, root 9, root 7 * root 8, root 8]
set_option maxHeartbeats 1600000 in
private theorem node70 : smallParityCensusNode 70 = Subgroup.closure (Set.range o70) := by
  change Subgroup.closure ({rootOne ^ 3 * root 3 * root 4, root 4 * root 5 * root 7 * root 8 * root 9, rootOne ^ 2 * root 4 * root 8, root 6 * root 7 * root 8, root 9, root 7 * root 8, root 8} : Set SylowModel) = _
  congr 1
  simp only [o70, Matrix.range_cons, Matrix.range_empty, Set.singleton_union, Set.union_empty]

private def o71 : Fin 7 → SylowModel := ![rootOne ^ 3 * root 3 * root 4 * root 5 * root 8, root 4 * root 7, rootOne ^ 2 * root 4 * root 8, root 6 * root 7 * root 8, root 9, root 7 * root 8, root 8]
set_option maxHeartbeats 1600000 in
private theorem node71 : smallParityCensusNode 71 = Subgroup.closure (Set.range o71) := by
  change Subgroup.closure ({rootOne ^ 3 * root 3 * root 4 * root 5 * root 8, root 4 * root 7, rootOne ^ 2 * root 4 * root 8, root 6 * root 7 * root 8, root 9, root 7 * root 8, root 8} : Set SylowModel) = _
  congr 1
  simp only [o71, Matrix.range_cons, Matrix.range_empty, Set.singleton_union, Set.union_empty]

private def o72 : Fin 7 → SylowModel := ![rootOne ^ 3 * root 3 * root 4, root 2 * root 3 * root 4 * root 7 * root 9, rootOne ^ 2 * root 4 * root 8, root 4 * root 7, root 7 * root 9, root 8 * root 9, root 8]
set_option maxHeartbeats 1600000 in
private theorem node72 : smallParityCensusNode 72 = Subgroup.closure (Set.range o72) := by
  change Subgroup.closure ({rootOne ^ 3 * root 3 * root 4, root 2 * root 3 * root 4 * root 7 * root 9, rootOne ^ 2 * root 4 * root 8, root 4 * root 7, root 7 * root 9, root 8 * root 9, root 8} : Set SylowModel) = _
  congr 1
  simp only [o72, Matrix.range_cons, Matrix.range_empty, Set.singleton_union, Set.union_empty]

private def o73 : Fin 7 → SylowModel := ![rootOne ^ 3 * root 3 * root 4, root 2 * root 3 * root 4 * root 5 * root 6, rootOne ^ 2 * root 4 * root 8, root 4 * root 6 * root 8 * root 9, root 9, root 7, root 8]
set_option maxHeartbeats 1600000 in
private theorem node73 : smallParityCensusNode 73 = Subgroup.closure (Set.range o73) := by
  change Subgroup.closure ({rootOne ^ 3 * root 3 * root 4, root 2 * root 3 * root 4 * root 5 * root 6, rootOne ^ 2 * root 4 * root 8, root 4 * root 6 * root 8 * root 9, root 9, root 7, root 8} : Set SylowModel) = _
  congr 1
  simp only [o73, Matrix.range_cons, Matrix.range_empty, Set.singleton_union, Set.union_empty]

private def o74 : Fin 7 → SylowModel := ![rootOne ^ 3 * root 3 * root 4 * root 5 * root 8, root 2 * root 3 * root 4 * root 7 * root 9, rootOne ^ 2 * root 4 * root 6 * root 7, root 4 * root 7, root 7 * root 9, root 8 * root 9, root 8]
set_option maxHeartbeats 1600000 in
private theorem node74 : smallParityCensusNode 74 = Subgroup.closure (Set.range o74) := by
  change Subgroup.closure ({rootOne ^ 3 * root 3 * root 4 * root 5 * root 8, root 2 * root 3 * root 4 * root 7 * root 9, rootOne ^ 2 * root 4 * root 6 * root 7, root 4 * root 7, root 7 * root 9, root 8 * root 9, root 8} : Set SylowModel) = _
  congr 1
  simp only [o74, Matrix.range_cons, Matrix.range_empty, Set.singleton_union, Set.union_empty]

private def o75 : Fin 7 → SylowModel := ![root 3, rootOne ^ 3, rootOne ^ 2, root 4, root 7 * root 8 * root 9, root 9, root 8]
set_option maxHeartbeats 1600000 in
private theorem node75 : smallParityCensusNode 75 = Subgroup.closure (Set.range o75) := by
  change Subgroup.closure ({root 3, rootOne ^ 3, rootOne ^ 2, root 4, root 7 * root 8 * root 9, root 9, root 8} : Set SylowModel) = _
  congr 1
  simp only [o75, Matrix.range_cons, Matrix.range_empty, Set.singleton_union, Set.union_empty]

private def o76 : Fin 7 → SylowModel := ![root 3 * root 6 * root 7 * root 8, rootOne ^ 3, rootOne ^ 2, root 4, root 7 * root 8 * root 9, root 9, root 8]
set_option maxHeartbeats 1600000 in
private theorem node76 : smallParityCensusNode 76 = Subgroup.closure (Set.range o76) := by
  change Subgroup.closure ({root 3 * root 6 * root 7 * root 8, rootOne ^ 3, rootOne ^ 2, root 4, root 7 * root 8 * root 9, root 9, root 8} : Set SylowModel) = _
  congr 1
  simp only [o76, Matrix.range_cons, Matrix.range_empty, Set.singleton_union, Set.union_empty]

private def o77 : Fin 7 → SylowModel := ![root 3, rootOne ^ 3 * root 5 * root 8, rootOne ^ 2 * root 6 * root 7 * root 8, root 4 * root 9, root 7 * root 8 * root 9, root 9, root 8]
set_option maxHeartbeats 1600000 in
private theorem node77 : smallParityCensusNode 77 = Subgroup.closure (Set.range o77) := by
  change Subgroup.closure ({root 3, rootOne ^ 3 * root 5 * root 8, rootOne ^ 2 * root 6 * root 7 * root 8, root 4 * root 9, root 7 * root 8 * root 9, root 9, root 8} : Set SylowModel) = _
  congr 1
  simp only [o77, Matrix.range_cons, Matrix.range_empty, Set.singleton_union, Set.union_empty]

private def o78 : Fin 7 → SylowModel := ![root 3 * root 6 * root 7 * root 8, rootOne ^ 3 * root 5 * root 8, rootOne ^ 2 * root 6 * root 7 * root 8, root 4 * root 9, root 7 * root 8 * root 9, root 9, root 8]
set_option maxHeartbeats 1600000 in
private theorem node78 : smallParityCensusNode 78 = Subgroup.closure (Set.range o78) := by
  change Subgroup.closure ({root 3 * root 6 * root 7 * root 8, rootOne ^ 3 * root 5 * root 8, rootOne ^ 2 * root 6 * root 7 * root 8, root 4 * root 9, root 7 * root 8 * root 9, root 9, root 8} : Set SylowModel) = _
  congr 1
  simp only [o78, Matrix.range_cons, Matrix.range_empty, Set.singleton_union, Set.union_empty]

private def o79 : Fin 7 → SylowModel := ![root 3 * root 5 * root 8, rootOne ^ 3, rootOne ^ 2, root 4 * root 6 * root 7 * root 8 * root 9, root 9, root 7 * root 8 * root 9, root 8]
set_option maxHeartbeats 1600000 in
private theorem node79 : smallParityCensusNode 79 = Subgroup.closure (Set.range o79) := by
  change Subgroup.closure ({root 3 * root 5 * root 8, rootOne ^ 3, rootOne ^ 2, root 4 * root 6 * root 7 * root 8 * root 9, root 9, root 7 * root 8 * root 9, root 8} : Set SylowModel) = _
  congr 1
  simp only [o79, Matrix.range_cons, Matrix.range_empty, Set.singleton_union, Set.union_empty]

private def o80 : Fin 7 → SylowModel := ![root 3 * root 5 * root 8, rootOne ^ 3 * root 5 * root 8, rootOne ^ 2 * root 6 * root 7 * root 8, root 4 * root 6 * root 7 * root 8, root 9, root 7 * root 8, root 8]
set_option maxHeartbeats 1600000 in
private theorem node80 : smallParityCensusNode 80 = Subgroup.closure (Set.range o80) := by
  change Subgroup.closure ({root 3 * root 5 * root 8, rootOne ^ 3 * root 5 * root 8, rootOne ^ 2 * root 6 * root 7 * root 8, root 4 * root 6 * root 7 * root 8, root 9, root 7 * root 8, root 8} : Set SylowModel) = _
  congr 1
  simp only [o80, Matrix.range_cons, Matrix.range_empty, Set.singleton_union, Set.union_empty]

private def o81 : Fin 7 → SylowModel := ![root 2 * root 4 * root 8, rootOne ^ 3, rootOne ^ 2, root 4, root 7, root 9, root 8]
set_option maxHeartbeats 1600000 in
private theorem node81 : smallParityCensusNode 81 = Subgroup.closure (Set.range o81) := by
  change Subgroup.closure ({root 2 * root 4 * root 8, rootOne ^ 3, rootOne ^ 2, root 4, root 7, root 9, root 8} : Set SylowModel) = _
  congr 1
  simp only [o81, Matrix.range_cons, Matrix.range_empty, Set.singleton_union, Set.union_empty]

private def o82 : Fin 7 → SylowModel := ![root 2 * root 4 * root 8, rootOne ^ 3 * root 2 * root 3 * root 4 * root 7, rootOne ^ 2, root 4, root 7, root 9, root 8]
set_option maxHeartbeats 1600000 in
private theorem node82 : smallParityCensusNode 82 = Subgroup.closure (Set.range o82) := by
  change Subgroup.closure ({root 2 * root 4 * root 8, rootOne ^ 3 * root 2 * root 3 * root 4 * root 7, rootOne ^ 2, root 4, root 7, root 9, root 8} : Set SylowModel) = _
  congr 1
  simp only [o82, Matrix.range_cons, Matrix.range_empty, Set.singleton_union, Set.union_empty]

private def o83 : Fin 7 → SylowModel := ![root 2 * root 4 * root 8, rootOne ^ 3, root 6 * root 7 * root 8, rootOne ^ 2, root 7 * root 8 * root 9, root 8 * root 9, root 8]
set_option maxHeartbeats 1600000 in
private theorem node83 : smallParityCensusNode 83 = Subgroup.closure (Set.range o83) := by
  change Subgroup.closure ({root 2 * root 4 * root 8, rootOne ^ 3, root 6 * root 7 * root 8, rootOne ^ 2, root 7 * root 8 * root 9, root 8 * root 9, root 8} : Set SylowModel) = _
  congr 1
  simp only [o83, Matrix.range_cons, Matrix.range_empty, Set.singleton_union, Set.union_empty]

private def o84 : Fin 7 → SylowModel := ![root 2 * root 4 * root 8, rootOne ^ 3, root 4 * root 6 * root 7 * root 8, rootOne ^ 2, root 7 * root 8 * root 9, root 8 * root 9, root 8]
set_option maxHeartbeats 1600000 in
private theorem node84 : smallParityCensusNode 84 = Subgroup.closure (Set.range o84) := by
  change Subgroup.closure ({root 2 * root 4 * root 8, rootOne ^ 3, root 4 * root 6 * root 7 * root 8, rootOne ^ 2, root 7 * root 8 * root 9, root 8 * root 9, root 8} : Set SylowModel) = _
  congr 1
  simp only [o84, Matrix.range_cons, Matrix.range_empty, Set.singleton_union, Set.union_empty]

private def o85 : Fin 7 → SylowModel := ![root 2 * root 8, rootOne ^ 3, root 6 * root 7 * root 8, rootOne ^ 2, root 7 * root 8 * root 9, root 8 * root 9, root 8]
set_option maxHeartbeats 1600000 in
private theorem node85 : smallParityCensusNode 85 = Subgroup.closure (Set.range o85) := by
  change Subgroup.closure ({root 2 * root 8, rootOne ^ 3, root 6 * root 7 * root 8, rootOne ^ 2, root 7 * root 8 * root 9, root 8 * root 9, root 8} : Set SylowModel) = _
  congr 1
  simp only [o85, Matrix.range_cons, Matrix.range_empty, Set.singleton_union, Set.union_empty]

private def o86 : Fin 7 → SylowModel := ![root 2 * root 8, rootOne ^ 3, root 4 * root 6 * root 7 * root 8, rootOne ^ 2, root 7 * root 8 * root 9, root 8 * root 9, root 8]
set_option maxHeartbeats 1600000 in
private theorem node86 : smallParityCensusNode 86 = Subgroup.closure (Set.range o86) := by
  change Subgroup.closure ({root 2 * root 8, rootOne ^ 3, root 4 * root 6 * root 7 * root 8, rootOne ^ 2, root 7 * root 8 * root 9, root 8 * root 9, root 8} : Set SylowModel) = _
  congr 1
  simp only [o86, Matrix.range_cons, Matrix.range_empty, Set.singleton_union, Set.union_empty]

private def o87 : Fin 7 → SylowModel := ![root 2 * root 4 * root 5 * root 9, rootOne ^ 3, rootOne ^ 2, root 6 * root 7 * root 8, root 8 * root 9, root 7 * root 8 * root 9, root 8]
set_option maxHeartbeats 1600000 in
private theorem node87 : smallParityCensusNode 87 = Subgroup.closure (Set.range o87) := by
  change Subgroup.closure ({root 2 * root 4 * root 5 * root 9, rootOne ^ 3, rootOne ^ 2, root 6 * root 7 * root 8, root 8 * root 9, root 7 * root 8 * root 9, root 8} : Set SylowModel) = _
  congr 1
  simp only [o87, Matrix.range_cons, Matrix.range_empty, Set.singleton_union, Set.union_empty]

private def o88 : Fin 7 → SylowModel := ![root 2 * root 4 * root 5 * root 9, rootOne ^ 3 * root 2 * root 3 * root 4 * root 5 * root 7 * root 8 * root 9, rootOne ^ 2 * root 4 * root 6 * root 8 * root 9, root 6 * root 8 * root 9, root 8 * root 9, root 7, root 8]
set_option maxHeartbeats 1600000 in
private theorem node88 : smallParityCensusNode 88 = Subgroup.closure (Set.range o88) := by
  change Subgroup.closure ({root 2 * root 4 * root 5 * root 9, rootOne ^ 3 * root 2 * root 3 * root 4 * root 5 * root 7 * root 8 * root 9, rootOne ^ 2 * root 4 * root 6 * root 8 * root 9, root 6 * root 8 * root 9, root 8 * root 9, root 7, root 8} : Set SylowModel) = _
  congr 1
  simp only [o88, Matrix.range_cons, Matrix.range_empty, Set.singleton_union, Set.union_empty]

private def o89 : Fin 7 → SylowModel := ![root 2 * root 4 * root 8, rootOne ^ 3 * root 5 * root 8, rootOne ^ 2 * root 6 * root 7 * root 8, root 4 * root 9, root 7, root 9, root 8]
set_option maxHeartbeats 1600000 in
private theorem node89 : smallParityCensusNode 89 = Subgroup.closure (Set.range o89) := by
  change Subgroup.closure ({root 2 * root 4 * root 8, rootOne ^ 3 * root 5 * root 8, rootOne ^ 2 * root 6 * root 7 * root 8, root 4 * root 9, root 7, root 9, root 8} : Set SylowModel) = _
  congr 1
  simp only [o89, Matrix.range_cons, Matrix.range_empty, Set.singleton_union, Set.union_empty]

private def o90 : Fin 7 → SylowModel := ![root 2 * root 4 * root 8, rootOne ^ 3 * root 2 * root 3 * root 4 * root 5 * root 7 * root 8 * root 9, rootOne ^ 2 * root 6 * root 7 * root 8, root 4 * root 9, root 7, root 9, root 8]
set_option maxHeartbeats 1600000 in
private theorem node90 : smallParityCensusNode 90 = Subgroup.closure (Set.range o90) := by
  change Subgroup.closure ({root 2 * root 4 * root 8, rootOne ^ 3 * root 2 * root 3 * root 4 * root 5 * root 7 * root 8 * root 9, rootOne ^ 2 * root 6 * root 7 * root 8, root 4 * root 9, root 7, root 9, root 8} : Set SylowModel) = _
  congr 1
  simp only [o90, Matrix.range_cons, Matrix.range_empty, Set.singleton_union, Set.union_empty]

private def o91 : Fin 7 → SylowModel := ![root 2 * root 4 * root 8, rootOne ^ 3 * root 5 * root 8, root 6 * root 7 * root 8, rootOne ^ 2 * root 6 * root 7 * root 8, root 7 * root 8 * root 9, root 8 * root 9, root 8]
set_option maxHeartbeats 1600000 in
private theorem node91 : smallParityCensusNode 91 = Subgroup.closure (Set.range o91) := by
  change Subgroup.closure ({root 2 * root 4 * root 8, rootOne ^ 3 * root 5 * root 8, root 6 * root 7 * root 8, rootOne ^ 2 * root 6 * root 7 * root 8, root 7 * root 8 * root 9, root 8 * root 9, root 8} : Set SylowModel) = _
  congr 1
  simp only [o91, Matrix.range_cons, Matrix.range_empty, Set.singleton_union, Set.union_empty]

private def o92 : Fin 7 → SylowModel := ![root 2 * root 4 * root 8, rootOne ^ 3 * root 5 * root 8, root 4 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2 * root 6 * root 7 * root 8, root 7 * root 8 * root 9, root 8 * root 9, root 8]
set_option maxHeartbeats 1600000 in
private theorem node92 : smallParityCensusNode 92 = Subgroup.closure (Set.range o92) := by
  change Subgroup.closure ({root 2 * root 4 * root 8, rootOne ^ 3 * root 5 * root 8, root 4 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2 * root 6 * root 7 * root 8, root 7 * root 8 * root 9, root 8 * root 9, root 8} : Set SylowModel) = _
  congr 1
  simp only [o92, Matrix.range_cons, Matrix.range_empty, Set.singleton_union, Set.union_empty]

private def o93 : Fin 7 → SylowModel := ![root 2 * root 8 * root 9, rootOne ^ 3 * root 5 * root 8, root 6 * root 7 * root 8, rootOne ^ 2 * root 6 * root 7 * root 8, root 7 * root 8 * root 9, root 8 * root 9, root 8]
set_option maxHeartbeats 1600000 in
private theorem node93 : smallParityCensusNode 93 = Subgroup.closure (Set.range o93) := by
  change Subgroup.closure ({root 2 * root 8 * root 9, rootOne ^ 3 * root 5 * root 8, root 6 * root 7 * root 8, rootOne ^ 2 * root 6 * root 7 * root 8, root 7 * root 8 * root 9, root 8 * root 9, root 8} : Set SylowModel) = _
  congr 1
  simp only [o93, Matrix.range_cons, Matrix.range_empty, Set.singleton_union, Set.union_empty]

private def o94 : Fin 7 → SylowModel := ![root 2 * root 8 * root 9, rootOne ^ 3 * root 5 * root 8, root 4 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2 * root 6 * root 7 * root 8, root 7 * root 8 * root 9, root 8 * root 9, root 8]
set_option maxHeartbeats 1600000 in
private theorem node94 : smallParityCensusNode 94 = Subgroup.closure (Set.range o94) := by
  change Subgroup.closure ({root 2 * root 8 * root 9, rootOne ^ 3 * root 5 * root 8, root 4 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2 * root 6 * root 7 * root 8, root 7 * root 8 * root 9, root 8 * root 9, root 8} : Set SylowModel) = _
  congr 1
  simp only [o94, Matrix.range_cons, Matrix.range_empty, Set.singleton_union, Set.union_empty]

private def o95 : Fin 7 → SylowModel := ![rootOne * root 0 * root 1 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8 * root 9, rootOne * root 0 * root 1 * root 2 * root 3 * root 7 * root 8 * root 9, rootOne ^ 2 * root 1 * root 3 * root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 4 * root 5 * root 7 * root 9, root 8 * root 9, root 9]
set_option maxHeartbeats 1600000 in
private theorem node95 : smallParityCensusNode 95 = Subgroup.closure (Set.range o95) := by
  change Subgroup.closure ({rootOne * root 0 * root 1 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8 * root 9, rootOne * root 0 * root 1 * root 2 * root 3 * root 7 * root 8 * root 9, rootOne ^ 2 * root 1 * root 3 * root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 4 * root 5 * root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) = _
  congr 1
  simp only [o95, Matrix.range_cons, Matrix.range_empty, Set.singleton_union, Set.union_empty]

private def o96 : Fin 7 → SylowModel := ![rootOne * root 0 * root 1 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8 * root 9, rootOne * root 0 * root 1 * root 2 * root 3 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2 * root 1 * root 3 * root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 4 * root 5 * root 7 * root 9, root 8 * root 9, root 9]
set_option maxHeartbeats 1600000 in
private theorem node96 : smallParityCensusNode 96 = Subgroup.closure (Set.range o96) := by
  change Subgroup.closure ({rootOne * root 0 * root 1 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8 * root 9, rootOne * root 0 * root 1 * root 2 * root 3 * root 6 * root 7 * root 8 * root 9, rootOne ^ 2 * root 1 * root 3 * root 6 * root 7 * root 8 * root 9, root 7 * root 9, root 4 * root 5 * root 7 * root 9, root 8 * root 9, root 9} : Set SylowModel) = _
  congr 1
  simp only [o96, Matrix.range_cons, Matrix.range_empty, Set.singleton_union, Set.union_empty]

private def s29 : Fin 3 → SylowModel := ![rootOne ^ 3, root 4 * root 7 * root 8, root 5 * root 8]
set_option maxHeartbeats 1600000 in
private theorem gen29 : Subgroup.closure (Set.range s29) = smallParityCensusNode 29 := by
  rw [node29]
  exact closure_eq_words s29 o29 (![[0], [3, 5, 6, 7], [1]]) (![[0], [2], [0, 0], [0, 0, 2, 0, 1, 0, 2], [0, 0, 0, 2, 0, 2], [0, 0, 2, 0, 0, 2], [1, 2, 1, 2], [0, 0, 0, 1, 0, 1]]) (by decide +kernel) (by decide +kernel)

private def e29_1 : Fin 6 → SylowModel := ![decode 0, decode 400, decode 288, decode 2048, decode 144, decode 608]
set_option maxHeartbeats 1600000 in
private theorem edgeEq29_1 : binaryFamily s29 (s29 0) (![true, false, false]) = e29_1 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert29_1 : Subgroup.closure (Set.range e29_1) ≤ character.ker := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨j, rfl⟩
  exact (show ∀ j, e29_1 j ∈ character.ker from by decide +kernel) j

private def e29_2 : Fin 6 → SylowModel := ![decode 1024, decode 0, decode 288, decode 1280, decode 0, decode 800]
set_option maxHeartbeats 1600000 in
private theorem edgeEq29_2 : binaryFamily s29 (s29 1) (![false, true, false]) = e29_2 := by decide +kernel
private def a29_2 (k : Fin 128) : SylowModel :=
  decode ((#[0, 1024, 2048, 64, 384, 768, 512, 3072, 1984, 1152, 1792, 1536, 2368, 2432, 2816, 2560, 224, 448, 832, 576, 640, 896, 256, 3776, 3200, 3840, 3584, 1312, 1856, 1216, 1472, 1920, 1664, 1280, 2656, 2240, 2624, 2880, 2688, 2944, 2304, 160, 352, 992, 736, 704, 960, 320, 128, 3744, 3648, 3520, 3264, 3968, 3712, 3328, 1760, 1440, 1568, 1824, 1088, 1344, 1728, 1408, 2848, 3040, 2400, 2144, 3008, 2752, 2112, 2176, 288, 928, 672, 608, 864, 480, 192, 3168, 3616, 3488, 3232, 3392, 3136, 4032, 3456, 1632, 1504, 1248, 1696, 1952, 1056, 1600, 2720, 2080, 2336, 2272, 2528, 2912, 2496, 544, 800, 416, 96, 3296, 3936, 3680, 3360, 3104, 4000, 3904, 1376, 1120, 2016, 1184, 2464, 2208, 2592, 2784, 32, 4064, 3808, 3424, 3872, 1888, 2976, 3552] : Array ℕ).getD k.val 0)
private def next29_2 (k : Fin 128) (j : Fin 6) : Fin 128 :=
  Fin.ofNat 128 (((#[#[1, 0, 72, 33, 0, 102],
    #[2, 1, 87, 40, 1, 113],
    #[7, 2, 94, 55, 2, 117],
    #[60, 3, 42, 61, 3, 76],
    #[63, 4, 41, 9, 4, 74],
    #[10, 5, 101, 11, 5, 120],
    #[11, 6, 102, 10, 6, 72],
    #[0, 7, 105, 22, 7, 122],
    #[68, 8, 57, 69, 8, 91],
    #[71, 9, 56, 13, 9, 89],
    #[14, 10, 112, 15, 10, 125],
    #[15, 11, 113, 14, 11, 87],
    #[83, 12, 65, 84, 12, 98],
    #[86, 13, 64, 24, 13, 96],
    #[25, 14, 116, 26, 14, 126],
    #[26, 15, 117, 25, 15, 94],
    #[89, 16, 17, 88, 16, 46],
    #[30, 17, 16, 29, 17, 44],
    #[28, 18, 75, 93, 18, 104],
    #[93, 19, 76, 28, 19, 42],
    #[32, 20, 73, 31, 20, 103],
    #[31, 21, 74, 32, 21, 41],
    #[33, 22, 120, 1, 22, 101],
    #[45, 23, 80, 46, 23, 109],
    #[48, 24, 79, 4, 24, 107],
    #[5, 25, 121, 6, 25, 127],
    #[6, 26, 122, 5, 26, 105],
    #[96, 27, 28, 95, 27, 61],
    #[37, 28, 27, 36, 28, 59],
    #[35, 29, 90, 100, 29, 115],
    #[100, 30, 91, 35, 30, 57],
    #[39, 31, 88, 38, 31, 114],
    #[38, 32, 89, 39, 32, 56],
    #[40, 33, 125, 2, 33, 112],
    #[107, 34, 35, 106, 34, 69],
    #[52, 35, 34, 51, 35, 67],
    #[50, 36, 97, 111, 36, 119],
    #[111, 37, 98, 50, 37, 65],
    #[54, 38, 95, 53, 38, 118],
    #[53, 39, 96, 54, 39, 64],
    #[55, 40, 126, 7, 40, 116],
    #[115, 41, 4, 57, 41, 21],
    #[112, 42, 3, 113, 42, 19],
    #[114, 43, 45, 56, 43, 78],
    #[56, 44, 46, 114, 44, 17],
    #[62, 45, 43, 8, 45, 77],
    #[8, 46, 44, 62, 46, 16],
    #[61, 47, 104, 60, 47, 75],
    #[9, 48, 103, 63, 48, 73],
    #[74, 49, 50, 73, 49, 84],
    #[19, 50, 49, 18, 50, 82],
    #[17, 51, 108, 78, 51, 124],
    #[78, 52, 109, 17, 52, 80],
    #[21, 53, 106, 20, 53, 123],
    #[20, 54, 107, 21, 54, 79],
    #[22, 55, 127, 0, 55, 121],
    #[119, 56, 9, 65, 56, 32],
    #[116, 57, 8, 117, 57, 30],
    #[118, 58, 60, 64, 58, 93],
    #[64, 59, 61, 118, 59, 28],
    #[70, 60, 58, 12, 60, 92],
    #[12, 61, 59, 70, 61, 27],
    #[69, 62, 115, 68, 62, 90],
    #[13, 63, 114, 71, 63, 88],
    #[124, 64, 13, 80, 64, 39],
    #[121, 65, 12, 122, 65, 37],
    #[123, 66, 68, 79, 66, 100],
    #[79, 67, 69, 123, 67, 35],
    #[85, 68, 66, 23, 68, 99],
    #[23, 69, 67, 85, 69, 34],
    #[84, 70, 119, 83, 70, 97],
    #[24, 71, 118, 86, 71, 95],
    #[27, 72, 0, 92, 72, 6],
    #[91, 73, 20, 90, 73, 48],
    #[90, 74, 21, 91, 74, 4],
    #[87, 75, 18, 125, 75, 47],
    #[125, 76, 19, 87, 76, 3],
    #[88, 77, 78, 89, 77, 45],
    #[29, 78, 77, 30, 78, 43],
    #[104, 79, 24, 42, 79, 54],
    #[101, 80, 23, 102, 80, 52],
    #[103, 81, 83, 41, 81, 111],
    #[41, 82, 84, 103, 82, 50],
    #[47, 83, 81, 3, 83, 110],
    #[3, 84, 82, 47, 84, 49],
    #[46, 85, 124, 45, 85, 108],
    #[4, 86, 123, 48, 86, 106],
    #[34, 87, 1, 99, 87, 11],
    #[98, 88, 31, 97, 88, 63],
    #[97, 89, 32, 98, 89, 9],
    #[94, 90, 29, 126, 90, 62],
    #[126, 91, 30, 94, 91, 8],
    #[95, 92, 93, 96, 92, 60],
    #[36, 93, 92, 37, 93, 58],
    #[49, 94, 2, 110, 94, 15],
    #[109, 95, 38, 108, 95, 71],
    #[108, 96, 39, 109, 96, 13],
    #[105, 97, 36, 127, 97, 70],
    #[127, 98, 37, 105, 98, 12],
    #[106, 99, 100, 107, 99, 68],
    #[51, 100, 99, 52, 100, 66],
    #[58, 101, 5, 59, 101, 22],
    #[59, 102, 6, 58, 102, 0],
    #[57, 103, 48, 115, 103, 20],
    #[113, 104, 47, 112, 104, 18],
    #[16, 105, 7, 77, 105, 26],
    #[76, 106, 53, 75, 106, 86],
    #[75, 107, 54, 76, 107, 24],
    #[72, 108, 51, 120, 108, 85],
    #[120, 109, 52, 72, 109, 23],
    #[73, 110, 111, 74, 110, 83],
    #[18, 111, 110, 19, 111, 81],
    #[66, 112, 10, 67, 112, 33],
    #[67, 113, 11, 66, 113, 1],
    #[65, 114, 63, 119, 114, 31],
    #[117, 115, 62, 116, 115, 29],
    #[81, 116, 14, 82, 116, 40],
    #[82, 117, 15, 81, 117, 2],
    #[80, 118, 71, 124, 118, 38],
    #[122, 119, 70, 121, 119, 36],
    #[92, 120, 22, 27, 120, 5],
    #[43, 121, 25, 44, 121, 55],
    #[44, 122, 26, 43, 122, 7],
    #[42, 123, 86, 104, 123, 53],
    #[102, 124, 85, 101, 124, 51],
    #[99, 125, 33, 34, 125, 10],
    #[110, 126, 40, 49, 126, 14],
    #[77, 127, 55, 16, 127, 25]] : Array (Array ℕ)).getD k.val #[]).getD j.val 0)
private def prev29_2 (k : Fin 128) (j : Fin 6) : Fin 128 :=
  Fin.ofNat 128 (((#[#[7, 0, 72, 55, 0, 102],
    #[0, 1, 87, 22, 1, 113],
    #[1, 2, 94, 33, 2, 117],
    #[84, 3, 42, 83, 3, 76],
    #[86, 4, 41, 24, 4, 74],
    #[25, 5, 101, 26, 5, 120],
    #[26, 6, 102, 25, 6, 72],
    #[2, 7, 105, 40, 7, 122],
    #[46, 8, 57, 45, 8, 91],
    #[48, 9, 56, 4, 9, 89],
    #[5, 10, 112, 6, 10, 125],
    #[6, 11, 113, 5, 11, 87],
    #[61, 12, 65, 60, 12, 98],
    #[63, 13, 64, 9, 13, 96],
    #[10, 14, 116, 11, 14, 126],
    #[11, 15, 117, 10, 15, 94],
    #[105, 16, 17, 127, 16, 46],
    #[51, 17, 16, 52, 17, 44],
    #[111, 18, 75, 50, 18, 104],
    #[50, 19, 76, 111, 19, 42],
    #[54, 20, 73, 53, 20, 103],
    #[53, 21, 74, 54, 21, 41],
    #[55, 22, 120, 7, 22, 101],
    #[69, 23, 80, 68, 23, 109],
    #[71, 24, 79, 13, 24, 107],
    #[14, 25, 121, 15, 25, 127],
    #[15, 26, 122, 14, 26, 105],
    #[72, 27, 28, 120, 27, 61],
    #[18, 28, 27, 19, 28, 59],
    #[78, 29, 90, 17, 29, 115],
    #[17, 30, 91, 78, 30, 57],
    #[21, 31, 88, 20, 31, 114],
    #[20, 32, 89, 21, 32, 56],
    #[22, 33, 125, 0, 33, 112],
    #[87, 34, 35, 125, 34, 69],
    #[29, 35, 34, 30, 35, 67],
    #[93, 36, 97, 28, 36, 119],
    #[28, 37, 98, 93, 37, 65],
    #[32, 38, 95, 31, 38, 118],
    #[31, 39, 96, 32, 39, 64],
    #[33, 40, 126, 1, 40, 116],
    #[82, 41, 4, 81, 41, 21],
    #[123, 42, 3, 79, 42, 19],
    #[121, 43, 45, 122, 43, 78],
    #[122, 44, 46, 121, 44, 17],
    #[23, 45, 43, 85, 45, 77],
    #[85, 46, 44, 23, 46, 16],
    #[83, 47, 104, 84, 47, 75],
    #[24, 48, 103, 86, 48, 73],
    #[94, 49, 50, 126, 49, 84],
    #[36, 50, 49, 37, 50, 82],
    #[100, 51, 108, 35, 51, 124],
    #[35, 52, 109, 100, 52, 80],
    #[39, 53, 106, 38, 53, 123],
    #[38, 54, 107, 39, 54, 79],
    #[40, 55, 127, 2, 55, 121],
    #[44, 56, 9, 43, 56, 32],
    #[103, 57, 8, 41, 57, 30],
    #[101, 58, 60, 102, 58, 93],
    #[102, 59, 61, 101, 59, 28],
    #[3, 60, 58, 47, 60, 92],
    #[47, 61, 59, 3, 61, 27],
    #[45, 62, 115, 46, 62, 90],
    #[4, 63, 114, 48, 63, 88],
    #[59, 64, 13, 58, 64, 39],
    #[114, 65, 12, 56, 65, 37],
    #[112, 66, 68, 113, 66, 100],
    #[113, 67, 69, 112, 67, 35],
    #[8, 68, 66, 62, 68, 99],
    #[62, 69, 67, 8, 69, 34],
    #[60, 70, 119, 61, 70, 97],
    #[9, 71, 118, 63, 71, 95],
    #[108, 72, 0, 109, 72, 6],
    #[110, 73, 20, 49, 73, 48],
    #[49, 74, 21, 110, 74, 4],
    #[107, 75, 18, 106, 75, 47],
    #[106, 76, 19, 107, 76, 3],
    #[127, 77, 78, 105, 77, 45],
    #[52, 78, 77, 51, 78, 43],
    #[67, 79, 24, 66, 79, 54],
    #[118, 80, 23, 64, 80, 52],
    #[116, 81, 83, 117, 81, 111],
    #[117, 82, 84, 116, 82, 50],
    #[12, 83, 81, 70, 83, 110],
    #[70, 84, 82, 12, 84, 49],
    #[68, 85, 124, 69, 85, 108],
    #[13, 86, 123, 71, 86, 106],
    #[75, 87, 1, 76, 87, 11],
    #[77, 88, 31, 16, 88, 63],
    #[16, 89, 32, 77, 89, 9],
    #[74, 90, 29, 73, 90, 62],
    #[73, 91, 30, 74, 91, 8],
    #[120, 92, 93, 72, 92, 60],
    #[19, 93, 92, 18, 93, 58],
    #[90, 94, 2, 91, 94, 15],
    #[92, 95, 38, 27, 95, 71],
    #[27, 96, 39, 92, 96, 13],
    #[89, 97, 36, 88, 97, 70],
    #[88, 98, 37, 89, 98, 12],
    #[125, 99, 100, 87, 99, 68],
    #[30, 100, 99, 29, 100, 66],
    #[80, 101, 5, 124, 101, 22],
    #[124, 102, 6, 80, 102, 0],
    #[81, 103, 48, 82, 103, 20],
    #[79, 104, 47, 123, 104, 18],
    #[97, 105, 7, 98, 105, 26],
    #[99, 106, 53, 34, 106, 86],
    #[34, 107, 54, 99, 107, 24],
    #[96, 108, 51, 95, 108, 85],
    #[95, 109, 52, 96, 109, 23],
    #[126, 110, 111, 94, 110, 83],
    #[37, 111, 110, 36, 111, 81],
    #[42, 112, 10, 104, 112, 33],
    #[104, 113, 11, 42, 113, 1],
    #[43, 114, 63, 44, 114, 31],
    #[41, 115, 62, 103, 115, 29],
    #[57, 116, 14, 115, 116, 40],
    #[115, 117, 15, 57, 117, 2],
    #[58, 118, 71, 59, 118, 38],
    #[56, 119, 70, 114, 119, 36],
    #[109, 120, 22, 108, 120, 5],
    #[65, 121, 25, 119, 121, 55],
    #[119, 122, 26, 65, 122, 7],
    #[66, 123, 86, 67, 123, 53],
    #[64, 124, 85, 118, 124, 51],
    #[76, 125, 33, 75, 125, 10],
    #[91, 126, 40, 90, 126, 14],
    #[98, 127, 55, 97, 127, 25]] : Array (Array ℕ)).getD k.val #[]).getD j.val 0)
set_option maxHeartbeats 1600000 in
private theorem cert29_2 : ∃ c, c ∈ Subgroup.centralizer (Subgroup.closure (Set.range e29_2) : Set SylowModel) ∧ c ∉ Subgroup.closure (Set.range e29_2) := by
  refine ⟨root 2 * root 8, centralizes_generators e29_2 _ (by decide +kernel), ?_⟩
  exact outside_of_table e29_2 a29_2 0 next29_2 prev29_2
    (by decide +kernel) (by decide +kernel) (by decide +kernel) _ (by decide +kernel)

private def e29_3 : Fin 6 → SylowModel := ![decode 0, decode 3472, decode 288, decode 2048, decode 1168, decode 608]
set_option maxHeartbeats 1600000 in
private theorem edgeEq29_3 : binaryFamily s29 (s29 0) (![true, true, false]) = e29_3 := by decide +kernel
private def a29_3 (k : Fin 128) : SylowModel :=
  decode ((#[0, 2048, 64, 384, 768, 512, 1168, 2368, 2432, 2816, 2560, 224, 448, 832, 576, 640, 896, 256, 3216, 1872, 1040, 1936, 1680, 2656, 2240, 2624, 2880, 2688, 2944, 2304, 160, 352, 992, 736, 704, 960, 320, 128, 3664, 3088, 3984, 3728, 1968, 2000, 1104, 1360, 1808, 1552, 1424, 2848, 3040, 2400, 2144, 3008, 2752, 2112, 2176, 288, 928, 672, 608, 864, 480, 192, 3120, 3792, 3408, 3152, 3856, 3600, 3472, 1136, 1840, 1200, 1456, 1232, 1488, 1616, 1296, 2720, 2080, 2336, 2272, 2528, 2912, 2496, 544, 800, 416, 96, 3824, 3248, 3888, 3632, 3536, 3280, 3920, 3344, 1264, 1904, 1648, 1072, 1328, 1712, 1744, 2464, 2208, 2592, 2784, 32, 3696, 3568, 3312, 4016, 3760, 3376, 4048, 2032, 1776, 1392, 1584, 2976, 3440, 3184, 4080, 3504, 1520, 3952] : Array ℕ).getD k.val 0)
private def next29_3 (k : Fin 128) (j : Fin 6) : Fin 128 :=
  Fin.ofNat 128 (((#[#[0, 70, 57, 1, 6, 60],
    #[1, 48, 79, 0, 18, 82],
    #[2, 94, 31, 55, 75, 86],
    #[3, 39, 30, 8, 78, 32],
    #[4, 41, 86, 9, 21, 31],
    #[5, 40, 87, 10, 22, 89],
    #[6, 0, 118, 18, 29, 120],
    #[7, 75, 50, 36, 94, 105],
    #[8, 20, 49, 3, 97, 51],
    #[9, 22, 105, 4, 40, 50],
    #[10, 21, 106, 5, 41, 108],
    #[11, 127, 12, 82, 100, 15],
    #[12, 67, 11, 85, 45, 58],
    #[13, 65, 60, 26, 43, 57],
    #[14, 116, 61, 25, 104, 109],
    #[15, 68, 58, 27, 47, 11],
    #[16, 69, 59, 28, 46, 62],
    #[17, 18, 109, 29, 48, 61],
    #[18, 1, 123, 6, 17, 125],
    #[19, 35, 102, 96, 54, 126],
    #[20, 37, 100, 39, 8, 103],
    #[21, 4, 126, 40, 10, 102],
    #[22, 5, 98, 41, 9, 101],
    #[23, 126, 24, 60, 112, 27],
    #[24, 45, 23, 63, 67, 80],
    #[25, 43, 82, 14, 65, 79],
    #[26, 104, 83, 13, 116, 121],
    #[27, 46, 80, 15, 69, 23],
    #[28, 47, 81, 16, 68, 84],
    #[29, 6, 121, 17, 70, 83],
    #[30, 92, 3, 106, 120, 34],
    #[31, 90, 2, 51, 117, 4],
    #[32, 123, 34, 50, 119, 3],
    #[33, 122, 35, 108, 71, 37],
    #[34, 96, 32, 54, 77, 30],
    #[35, 38, 33, 53, 19, 88],
    #[36, 95, 89, 7, 76, 87],
    #[37, 97, 88, 56, 20, 33],
    #[38, 54, 114, 77, 35, 127],
    #[39, 56, 112, 20, 3, 115],
    #[40, 9, 127, 21, 5, 114],
    #[41, 10, 110, 22, 4, 113],
    #[42, 57, 76, 113, 80, 78],
    #[43, 13, 74, 116, 25, 119],
    #[44, 63, 120, 67, 85, 118],
    #[45, 12, 72, 66, 24, 117],
    #[46, 16, 119, 68, 27, 74],
    #[47, 15, 71, 69, 28, 73],
    #[48, 17, 117, 70, 1, 72],
    #[49, 73, 8, 87, 125, 53],
    #[50, 71, 7, 32, 122, 9],
    #[51, 118, 53, 31, 124, 8],
    #[52, 117, 54, 89, 90, 56],
    #[53, 77, 51, 35, 96, 49],
    #[54, 19, 52, 34, 38, 107],
    #[55, 76, 108, 2, 95, 106],
    #[56, 78, 107, 37, 39, 52],
    #[57, 114, 0, 81, 42, 13],
    #[58, 64, 15, 121, 102, 12],
    #[59, 115, 16, 79, 101, 63],
    #[60, 111, 13, 23, 98, 0],
    #[61, 112, 14, 84, 126, 17],
    #[62, 110, 63, 83, 99, 16],
    #[63, 66, 62, 24, 44, 59],
    #[64, 79, 95, 101, 58, 97],
    #[65, 25, 93, 104, 13, 124],
    #[66, 85, 125, 45, 63, 123],
    #[67, 24, 91, 44, 12, 122],
    #[68, 28, 124, 46, 15, 93],
    #[69, 27, 90, 47, 16, 92],
    #[70, 29, 122, 48, 0, 91],
    #[71, 33, 47, 123, 50, 104],
    #[72, 88, 45, 92, 106, 48],
    #[73, 86, 104, 91, 49, 47],
    #[74, 87, 43, 125, 107, 46],
    #[75, 2, 103, 95, 7, 100],
    #[76, 36, 42, 94, 55, 99],
    #[77, 34, 101, 38, 53, 98],
    #[78, 3, 99, 97, 56, 42],
    #[79, 102, 1, 59, 64, 25],
    #[80, 42, 27, 109, 114, 24],
    #[81, 103, 28, 57, 113, 85],
    #[82, 99, 25, 11, 110, 1],
    #[83, 100, 26, 62, 127, 29],
    #[84, 98, 85, 61, 111, 28],
    #[85, 44, 84, 12, 66, 81],
    #[86, 125, 4, 107, 73, 2],
    #[87, 91, 5, 49, 74, 36],
    #[88, 93, 37, 105, 72, 35],
    #[89, 124, 36, 52, 118, 5],
    #[90, 52, 69, 118, 31, 116],
    #[91, 107, 67, 73, 87, 70],
    #[92, 105, 116, 72, 30, 69],
    #[93, 106, 65, 120, 88, 68],
    #[94, 7, 115, 76, 2, 112],
    #[95, 55, 64, 75, 36, 111],
    #[96, 53, 113, 19, 34, 110],
    #[97, 8, 111, 78, 37, 64],
    #[98, 60, 22, 112, 84, 77],
    #[99, 62, 78, 127, 82, 76],
    #[100, 11, 20, 110, 83, 75],
    #[101, 59, 77, 64, 121, 22],
    #[102, 58, 19, 115, 79, 21],
    #[103, 109, 75, 114, 81, 20],
    #[104, 14, 73, 65, 26, 71],
    #[105, 120, 9, 88, 92, 7],
    #[106, 72, 10, 30, 93, 55],
    #[107, 74, 56, 86, 91, 54],
    #[108, 119, 55, 33, 123, 10],
    #[109, 113, 17, 80, 103, 14],
    #[110, 82, 41, 100, 62, 96],
    #[111, 84, 97, 126, 60, 95],
    #[112, 23, 39, 98, 61, 94],
    #[113, 81, 96, 42, 109, 41],
    #[114, 80, 38, 103, 57, 40],
    #[115, 121, 94, 102, 59, 39],
    #[116, 26, 92, 43, 14, 90],
    #[117, 31, 48, 124, 52, 45],
    #[118, 89, 6, 90, 51, 44],
    #[119, 32, 46, 122, 108, 43],
    #[120, 30, 44, 93, 105, 6],
    #[121, 101, 29, 58, 115, 26],
    #[122, 50, 70, 119, 33, 67],
    #[123, 108, 18, 71, 32, 66],
    #[124, 51, 68, 117, 89, 65],
    #[125, 49, 66, 74, 86, 18],
    #[126, 61, 21, 111, 23, 19],
    #[127, 83, 40, 99, 11, 38]] : Array (Array ℕ)).getD k.val #[]).getD j.val 0)
private def prev29_3 (k : Fin 128) (j : Fin 6) : Fin 128 :=
  Fin.ofNat 128 (((#[#[0, 6, 57, 1, 70, 60],
    #[1, 18, 79, 0, 48, 82],
    #[2, 75, 31, 55, 94, 86],
    #[3, 78, 30, 8, 39, 32],
    #[4, 21, 86, 9, 41, 31],
    #[5, 22, 87, 10, 40, 89],
    #[6, 29, 118, 18, 0, 120],
    #[7, 94, 50, 36, 75, 105],
    #[8, 97, 49, 3, 20, 51],
    #[9, 40, 105, 4, 22, 50],
    #[10, 41, 106, 5, 21, 108],
    #[11, 100, 12, 82, 127, 15],
    #[12, 45, 11, 85, 67, 58],
    #[13, 43, 60, 26, 65, 57],
    #[14, 104, 61, 25, 116, 109],
    #[15, 47, 58, 27, 68, 11],
    #[16, 46, 59, 28, 69, 62],
    #[17, 48, 109, 29, 18, 61],
    #[18, 17, 123, 6, 1, 125],
    #[19, 54, 102, 96, 35, 126],
    #[20, 8, 100, 39, 37, 103],
    #[21, 10, 126, 40, 4, 102],
    #[22, 9, 98, 41, 5, 101],
    #[23, 112, 24, 60, 126, 27],
    #[24, 67, 23, 63, 45, 80],
    #[25, 65, 82, 14, 43, 79],
    #[26, 116, 83, 13, 104, 121],
    #[27, 69, 80, 15, 46, 23],
    #[28, 68, 81, 16, 47, 84],
    #[29, 70, 121, 17, 6, 83],
    #[30, 120, 3, 106, 92, 34],
    #[31, 117, 2, 51, 90, 4],
    #[32, 119, 34, 50, 123, 3],
    #[33, 71, 35, 108, 122, 37],
    #[34, 77, 32, 54, 96, 30],
    #[35, 19, 33, 53, 38, 88],
    #[36, 76, 89, 7, 95, 87],
    #[37, 20, 88, 56, 97, 33],
    #[38, 35, 114, 77, 54, 127],
    #[39, 3, 112, 20, 56, 115],
    #[40, 5, 127, 21, 9, 114],
    #[41, 4, 110, 22, 10, 113],
    #[42, 80, 76, 113, 57, 78],
    #[43, 25, 74, 116, 13, 119],
    #[44, 85, 120, 67, 63, 118],
    #[45, 24, 72, 66, 12, 117],
    #[46, 27, 119, 68, 16, 74],
    #[47, 28, 71, 69, 15, 73],
    #[48, 1, 117, 70, 17, 72],
    #[49, 125, 8, 87, 73, 53],
    #[50, 122, 7, 32, 71, 9],
    #[51, 124, 53, 31, 118, 8],
    #[52, 90, 54, 89, 117, 56],
    #[53, 96, 51, 35, 77, 49],
    #[54, 38, 52, 34, 19, 107],
    #[55, 95, 108, 2, 76, 106],
    #[56, 39, 107, 37, 78, 52],
    #[57, 42, 0, 81, 114, 13],
    #[58, 102, 15, 121, 64, 12],
    #[59, 101, 16, 79, 115, 63],
    #[60, 98, 13, 23, 111, 0],
    #[61, 126, 14, 84, 112, 17],
    #[62, 99, 63, 83, 110, 16],
    #[63, 44, 62, 24, 66, 59],
    #[64, 58, 95, 101, 79, 97],
    #[65, 13, 93, 104, 25, 124],
    #[66, 63, 125, 45, 85, 123],
    #[67, 12, 91, 44, 24, 122],
    #[68, 15, 124, 46, 28, 93],
    #[69, 16, 90, 47, 27, 92],
    #[70, 0, 122, 48, 29, 91],
    #[71, 50, 47, 123, 33, 104],
    #[72, 106, 45, 92, 88, 48],
    #[73, 49, 104, 91, 86, 47],
    #[74, 107, 43, 125, 87, 46],
    #[75, 7, 103, 95, 2, 100],
    #[76, 55, 42, 94, 36, 99],
    #[77, 53, 101, 38, 34, 98],
    #[78, 56, 99, 97, 3, 42],
    #[79, 64, 1, 59, 102, 25],
    #[80, 114, 27, 109, 42, 24],
    #[81, 113, 28, 57, 103, 85],
    #[82, 110, 25, 11, 99, 1],
    #[83, 127, 26, 62, 100, 29],
    #[84, 111, 85, 61, 98, 28],
    #[85, 66, 84, 12, 44, 81],
    #[86, 73, 4, 107, 125, 2],
    #[87, 74, 5, 49, 91, 36],
    #[88, 72, 37, 105, 93, 35],
    #[89, 118, 36, 52, 124, 5],
    #[90, 31, 69, 118, 52, 116],
    #[91, 87, 67, 73, 107, 70],
    #[92, 30, 116, 72, 105, 69],
    #[93, 88, 65, 120, 106, 68],
    #[94, 2, 115, 76, 7, 112],
    #[95, 36, 64, 75, 55, 111],
    #[96, 34, 113, 19, 53, 110],
    #[97, 37, 111, 78, 8, 64],
    #[98, 84, 22, 112, 60, 77],
    #[99, 82, 78, 127, 62, 76],
    #[100, 83, 20, 110, 11, 75],
    #[101, 121, 77, 64, 59, 22],
    #[102, 79, 19, 115, 58, 21],
    #[103, 81, 75, 114, 109, 20],
    #[104, 26, 73, 65, 14, 71],
    #[105, 92, 9, 88, 120, 7],
    #[106, 93, 10, 30, 72, 55],
    #[107, 91, 56, 86, 74, 54],
    #[108, 123, 55, 33, 119, 10],
    #[109, 103, 17, 80, 113, 14],
    #[110, 62, 41, 100, 82, 96],
    #[111, 60, 97, 126, 84, 95],
    #[112, 61, 39, 98, 23, 94],
    #[113, 109, 96, 42, 81, 41],
    #[114, 57, 38, 103, 80, 40],
    #[115, 59, 94, 102, 121, 39],
    #[116, 14, 92, 43, 26, 90],
    #[117, 52, 48, 124, 31, 45],
    #[118, 51, 6, 90, 89, 44],
    #[119, 108, 46, 122, 32, 43],
    #[120, 105, 44, 93, 30, 6],
    #[121, 115, 29, 58, 101, 26],
    #[122, 33, 70, 119, 50, 67],
    #[123, 32, 18, 71, 108, 66],
    #[124, 89, 68, 117, 51, 65],
    #[125, 86, 66, 74, 49, 18],
    #[126, 23, 21, 111, 61, 19],
    #[127, 11, 40, 99, 83, 38]] : Array (Array ℕ)).getD k.val #[]).getD j.val 0)
set_option maxHeartbeats 1600000 in
private theorem cert29_3 : ∃ c, c ∈ Subgroup.centralizer (Subgroup.closure (Set.range e29_3) : Set SylowModel) ∧ c ∉ Subgroup.closure (Set.range e29_3) := by
  refine ⟨root 2 * root 7, centralizes_generators e29_3 _ (by decide +kernel), ?_⟩
  exact outside_of_table e29_3 a29_3 0 next29_3 prev29_3
    (by decide +kernel) (by decide +kernel) (by decide +kernel) _ (by decide +kernel)

private def e29_4 : Fin 6 → SylowModel := ![decode 1024, decode 400, decode 0, decode 1856, decode 912, decode 0]
set_option maxHeartbeats 1600000 in
private theorem edgeEq29_4 : binaryFamily s29 (s29 2) (![false, false, true]) = e29_4 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert29_4 : Represented smallParityCensusNode (Subgroup.closure (Set.range e29_4)) := by
  refine ⟨61, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node61]
  exact closure_eq_words _ o61 (![[0], [1, 4, 5, 6], [], [0, 3], [1, 5, 6], []]) (![[0], [0, 0, 3, 4, 3], [0, 0], [0, 0, 0, 3], [1, 4], [0, 0, 3, 3], [0, 3, 0, 3]]) (by decide +kernel) (by decide +kernel)

private def e29_5 : Fin 6 → SylowModel := ![decode 0, decode 400, decode 3360, decode 2048, decode 144, decode 1632]
set_option maxHeartbeats 1600000 in
private theorem edgeEq29_5 : binaryFamily s29 (s29 0) (![true, false, true]) = e29_5 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert29_5 : Represented smallParityCensusNode (Subgroup.closure (Set.range e29_5)) := by
  refine ⟨63, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node63]
  exact closure_eq_words _ o63 (![[], [1, 4, 5, 6], [0, 3, 2], [2], [1, 4, 5], [0]]) (![[5], [2, 1, 3, 5, 3], [3], [2, 2, 3], [1, 2, 4, 5], [2, 3, 5, 3], [1, 4]]) (by decide +kernel) (by decide +kernel)

private def e29_6 : Fin 6 → SylowModel := ![decode 1024, decode 0, decode 688, decode 1280, decode 0, decode 176]
set_option maxHeartbeats 1600000 in
private theorem edgeEq29_6 : binaryFamily s29 (s29 1) (![false, true, true]) = e29_6 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert29_6 : Represented smallParityCensusNode (Subgroup.closure (Set.range e29_6)) := by
  refine ⟨62, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node62]
  exact closure_eq_words _ o62 (![[0], [], [1, 4, 5, 6], [0, 6], [], [1, 5, 6]]) (![[0], [0, 0, 5, 0, 3], [0, 0], [0, 0, 0, 2, 3, 5], [2, 2], [0, 0, 2, 0, 0, 5], [0, 0, 0, 3]]) (by decide +kernel) (by decide +kernel)

private def e29_7 : Fin 6 → SylowModel := ![decode 0, decode 3472, decode 3360, decode 2048, decode 1168, decode 1632]
set_option maxHeartbeats 1600000 in
private theorem edgeEq29_7 : binaryFamily s29 (s29 0) (![true, true, true]) = e29_7 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert29_7 : Represented smallParityCensusNode (Subgroup.closure (Set.range e29_7)) := by
  refine ⟨62, root 2 * root 3 * root 4 * root 7, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node62]
  exact closure_eq_words _ o62 (![[], [0, 1, 2, 1], [0, 1, 2, 3, 4], [2], [4, 5, 0], [0, 1, 6]]) (![[2, 1, 2], [1, 1, 2, 1], [3], [4, 5, 1, 2], [1, 5, 1, 5], [2, 3, 5, 3], [1, 1, 3]]) (by decide +kernel) (by decide +kernel)

private def s30 : Fin 3 → SylowModel := ![rootOne ^ 3, root 2 * root 3 * root 4 * root 7, root 6]
set_option maxHeartbeats 1600000 in
private theorem gen30 : Subgroup.closure (Set.range s30) = smallParityCensusNode 30 := by
  rw [node30]
  exact closure_eq_words s30 o30 (![[0], [1], [4, 5, 6]]) (![[0], [1], [0, 0], [0, 0, 0, 1, 1, 1, 0, 1], [0, 0, 1, 2, 0, 0, 1], [0, 0, 0, 1, 1, 0], [1, 1, 1, 2, 1, 2], [0, 0, 2, 0, 0, 2]]) (by decide +kernel) (by decide +kernel)

private def e30_1 : Fin 6 → SylowModel := ![decode 0, decode 156, decode 64, decode 2048, decode 396, decode 960]
set_option maxHeartbeats 1600000 in
private theorem edgeEq30_1 : binaryFamily s30 (s30 0) (![true, false, false]) = e30_1 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert30_1 : Subgroup.closure (Set.range e30_1) ≤ character.ker := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨j, rfl⟩
  exact (show ∀ j, e30_1 j ∈ character.ker from by decide +kernel) j

private def e30_2 : Fin 6 → SylowModel := ![decode 1024, decode 0, decode 64, decode 1040, decode 640, decode 576]
set_option maxHeartbeats 1600000 in
private theorem edgeEq30_2 : binaryFamily s30 (s30 1) (![false, true, false]) = e30_2 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert30_2 : Represented smallParityCensusNode (Subgroup.closure (Set.range e30_2)) := by
  refine ⟨61, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node61]
  exact closure_eq_words _ o61 (![[0], [], [3, 4, 5], [0, 1, 6], [5, 6], [3, 5]]) (![[0], [0, 0, 0, 4, 3, 4], [0, 0], [0, 5, 0, 0, 0], [2, 5], [0, 0, 0, 4, 0], [0, 0, 0, 4, 0, 4]]) (by decide +kernel) (by decide +kernel)

private def e30_3 : Fin 6 → SylowModel := ![decode 0, decode 3228, decode 64, decode 2048, decode 1420, decode 960]
set_option maxHeartbeats 1600000 in
private theorem edgeEq30_3 : binaryFamily s30 (s30 0) (![true, true, false]) = e30_3 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert30_3 : Represented smallParityCensusNode (Subgroup.closure (Set.range e30_3)) := by
  refine ⟨61, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node61]
  exact closure_eq_words _ o61 (![[], [0, 2], [3, 5], [1, 2, 4, 6], [4, 5, 0], [3, 4]]) (![[1, 1, 1], [1, 2, 1, 3, 5], [1, 1], [1, 1, 1, 2, 1], [1, 2, 4, 2], [1, 2, 4, 5], [1, 1, 4, 4]]) (by decide +kernel) (by decide +kernel)

private def e30_4 : Fin 6 → SylowModel := ![decode 1024, decode 156, decode 0, decode 1920, decode 668, decode 0]
set_option maxHeartbeats 1600000 in
private theorem edgeEq30_4 : binaryFamily s30 (s30 2) (![false, false, true]) = e30_4 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert30_4 : Represented smallParityCensusNode (Subgroup.closure (Set.range e30_4)) := by
  refine ⟨64, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node64]
  exact closure_eq_words _ o64 (![[0], [1], [], [0, 4], [1, 5], []]) (![[0], [1], [0, 0], [0, 0, 1, 0, 1, 3], [1, 1], [1, 1, 1, 4], [0, 0, 3, 3]]) (by decide +kernel) (by decide +kernel)

private def e30_5 : Fin 6 → SylowModel := ![decode 0, decode 156, decode 3136, decode 2048, decode 396, decode 1984]
set_option maxHeartbeats 1600000 in
private theorem edgeEq30_5 : binaryFamily s30 (s30 0) (![true, false, true]) = e30_5 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert30_5 : Represented smallParityCensusNode (Subgroup.closure (Set.range e30_5)) := by
  refine ⟨64, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node64]
  exact closure_eq_words _ o64 (![[], [1], [0, 2, 3, 5], [2, 4], [3, 1, 5], [0, 3, 5]]) (![[1, 4, 2, 3], [1], [2, 2], [1, 2, 1, 3, 2], [1, 1], [1, 2, 4, 2, 3], [1, 1, 4, 4]]) (by decide +kernel) (by decide +kernel)

private def e30_6 : Fin 6 → SylowModel := ![decode 1024, decode 0, decode 92, decode 1040, decode 640, decode 220]
set_option maxHeartbeats 1600000 in
private theorem edgeEq30_6 : binaryFamily s30 (s30 1) (![false, true, true]) = e30_6 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert30_6 : Represented smallParityCensusNode (Subgroup.closure (Set.range e30_6)) := by
  refine ⟨64, root 1 * root 2 * root 4 * root 6 * root 7 * root 9, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node64]
  exact closure_eq_words _ o64 (![[1, 0, 5], [], [1, 4, 6], [4, 0, 1], [4, 5], [1, 6]]) (![[3, 5], [0, 0, 5, 0, 0], [0, 2, 0, 2], [0, 0, 0, 4, 3], [2, 2], [2, 2, 4], [0, 0, 0, 4, 0, 4]]) (by decide +kernel) (by decide +kernel)

private def e30_7 : Fin 6 → SylowModel := ![decode 0, decode 3228, decode 3136, decode 2048, decode 1420, decode 1984]
set_option maxHeartbeats 1600000 in
private theorem edgeEq30_7 : binaryFamily s30 (s30 0) (![true, true, true]) = e30_7 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert30_7 : Represented smallParityCensusNode (Subgroup.closure (Set.range e30_7)) := by
  refine ⟨64, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node64]
  exact closure_eq_words _ o64 (![[], [0, 2], [1, 0, 2, 4], [2, 3, 5, 6], [0, 4, 5], [0, 1, 6]]) (![[1, 1, 1], [1, 3, 5, 3], [1, 1], [1, 2, 3, 4, 2], [1, 5, 1, 5], [1, 2, 1, 3, 5], [1, 1, 4, 4]]) (by decide +kernel) (by decide +kernel)

private def s31 : Fin 3 → SylowModel := ![rootOne ^ 3, root 6, root 2 * root 3 * root 4 * root 5 * root 7 * root 8 * root 9]
set_option maxHeartbeats 1600000 in
private theorem gen31 : Subgroup.closure (Set.range s31) = smallParityCensusNode 31 := by
  rw [node31]
  exact closure_eq_words s31 o31 (![[0], [4, 5, 6], [1]]) (![[0], [2], [0, 0], [0, 0, 0, 2, 0, 1, 2], [0, 0, 0, 2, 2, 0, 1], [0, 0, 1, 0, 1, 0], [1, 2, 1, 2, 2, 2], [0, 0, 1, 0, 0, 1]]) (by decide +kernel) (by decide +kernel)

private def e31_1 : Fin 6 → SylowModel := ![decode 0, decode 64, decode 956, decode 2048, decode 960, decode 492]
set_option maxHeartbeats 1600000 in
private theorem edgeEq31_1 : binaryFamily s31 (s31 0) (![true, false, false]) = e31_1 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert31_1 : Subgroup.closure (Set.range e31_1) ≤ character.ker := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨j, rfl⟩
  exact (show ∀ j, e31_1 j ∈ character.ker from by decide +kernel) j

private def e31_2 : Fin 6 → SylowModel := ![decode 1024, decode 0, decode 956, decode 1920, decode 0, decode 444]
set_option maxHeartbeats 1600000 in
private theorem edgeEq31_2 : binaryFamily s31 (s31 1) (![false, true, false]) = e31_2 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert31_2 : Represented smallParityCensusNode (Subgroup.closure (Set.range e31_2)) := by
  refine ⟨65, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node65]
  exact closure_eq_words _ o65 (![[0], [], [1], [5, 0], [], [1, 4, 6]]) (![[0], [2], [0, 0], [0, 0, 2, 3, 5, 3], [0, 0, 0, 2, 2, 3], [0, 0, 3, 0], [0, 0, 3, 3]]) (by decide +kernel) (by decide +kernel)

private def e31_3 : Fin 6 → SylowModel := ![decode 0, decode 3136, decode 956, decode 2048, decode 1984, decode 492]
set_option maxHeartbeats 1600000 in
private theorem edgeEq31_3 : binaryFamily s31 (s31 0) (![true, true, false]) = e31_3 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert31_3 : Represented smallParityCensusNode (Subgroup.closure (Set.range e31_3)) := by
  refine ⟨65, root 2 * root 3 * root 4 * root 7, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node65]
  exact closure_eq_words _ o65 (![[], [0, 2, 3, 4], [1, 4, 6], [2], [3, 0, 4], [1, 3, 5]]) (![[2, 4, 2], [1, 5, 4], [3], [5, 2], [2, 3, 2, 3], [1, 3, 1], [1, 2, 4, 5]]) (by decide +kernel) (by decide +kernel)

private def e31_4 : Fin 6 → SylowModel := ![decode 1024, decode 64, decode 0, decode 1360, decode 576, decode 128]
set_option maxHeartbeats 1600000 in
private theorem edgeEq31_4 : binaryFamily s31 (s31 2) (![false, false, true]) = e31_4 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert31_4 : Represented smallParityCensusNode (Subgroup.closure (Set.range e31_4)) := by
  refine ⟨61, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node61]
  exact closure_eq_words _ o61 (![[0], [3, 4, 5], [], [0, 1, 3, 4, 6], [3, 5], [4, 5, 6]]) (![[0], [0, 0, 0, 1, 3], [0, 0], [0, 0, 3, 3, 4], [1, 4], [0, 0, 3, 3], [0, 3, 0, 3]]) (by decide +kernel) (by decide +kernel)

private def e31_5 : Fin 6 → SylowModel := ![decode 0, decode 64, decode 4028, decode 2048, decode 960, decode 1516]
set_option maxHeartbeats 1600000 in
private theorem edgeEq31_5 : binaryFamily s31 (s31 0) (![true, false, true]) = e31_5 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert31_5 : Represented smallParityCensusNode (Subgroup.closure (Set.range e31_5)) := by
  refine ⟨63, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node63]
  exact closure_eq_words _ o63 (![[], [3, 5], [0, 3, 2], [1, 2, 4, 6], [3, 4], [5, 0]]) (![[1, 5, 1], [1, 2, 3, 2], [5, 1, 5], [1, 5, 2], [1, 4, 5, 2], [5, 2], [1, 3, 1, 3]]) (by decide +kernel) (by decide +kernel)

private def e31_6 : Fin 6 → SylowModel := ![decode 1024, decode 0, decode 1020, decode 1920, decode 0, decode 508]
set_option maxHeartbeats 1600000 in
private theorem edgeEq31_6 : binaryFamily s31 (s31 1) (![false, true, true]) = e31_6 := by decide +kernel
private def a31_6 (k : Fin 128) : SylowModel :=
  decode ((#[0, 1024, 2048, 764, 384, 768, 512, 3072, 1836, 1152, 1792, 1536, 2172, 2432, 2816, 2560, 892, 508, 252, 464, 640, 896, 256, 3244, 3200, 3840, 3584, 1964, 1068, 1324, 1872, 1920, 1664, 1280, 2556, 2940, 2684, 2256, 2688, 2944, 2304, 300, 124, 380, 1020, 80, 720, 976, 128, 3116, 4012, 3756, 3664, 3968, 3712, 3328, 1660, 1196, 1452, 1580, 2000, 1104, 1360, 1408, 2732, 2812, 3068, 2428, 2384, 3024, 2768, 2176, 172, 556, 812, 636, 848, 592, 208, 3324, 3884, 3628, 3500, 3792, 3408, 3152, 3456, 1788, 1404, 1148, 1708, 1232, 1488, 1616, 2860, 2476, 2220, 2300, 2640, 2896, 2512, 940, 684, 44, 336, 3196, 4092, 3836, 3372, 3536, 3280, 3920, 1532, 1276, 1916, 1744, 2092, 2348, 2988, 2128, 428, 3964, 3708, 3580, 4048, 2044, 2604, 3452] : Array ℕ).getD k.val 0)
private def next31_6 (k : Fin 128) (j : Fin 6) : Fin 128 :=
  Fin.ofNat 128 (((#[#[1, 0, 44, 31, 0, 17],
    #[2, 1, 59, 38, 1, 28],
    #[7, 2, 67, 53, 2, 35],
    #[87, 3, 21, 88, 3, 4],
    #[63, 4, 75, 11, 4, 42],
    #[10, 5, 18, 9, 5, 3],
    #[11, 6, 17, 63, 6, 44],
    #[0, 7, 82, 20, 7, 50],
    #[94, 8, 32, 95, 8, 9],
    #[71, 9, 90, 15, 9, 57],
    #[14, 10, 29, 13, 10, 8],
    #[15, 11, 28, 71, 11, 59],
    #[105, 12, 39, 106, 12, 13],
    #[86, 13, 97, 26, 13, 65],
    #[25, 14, 36, 24, 14, 12],
    #[26, 15, 35, 86, 15, 67],
    #[114, 16, 6, 113, 16, 0],
    #[112, 17, 48, 56, 17, 20],
    #[113, 18, 4, 114, 18, 21],
    #[92, 19, 41, 93, 19, 74],
    #[32, 20, 43, 33, 20, 16],
    #[31, 21, 42, 1, 21, 75],
    #[33, 22, 3, 32, 22, 18],
    #[72, 23, 54, 73, 23, 24],
    #[48, 24, 108, 6, 24, 80],
    #[5, 25, 51, 4, 25, 23],
    #[6, 26, 50, 48, 26, 82],
    #[118, 27, 11, 117, 27, 1],
    #[116, 28, 63, 64, 28, 31],
    #[117, 29, 9, 118, 29, 32],
    #[99, 30, 56, 100, 30, 89],
    #[39, 31, 58, 40, 31, 27],
    #[38, 32, 57, 2, 32, 90],
    #[40, 33, 8, 39, 33, 29],
    #[123, 34, 15, 122, 34, 2],
    #[121, 35, 71, 79, 35, 38],
    #[122, 36, 13, 123, 36, 39],
    #[110, 37, 64, 111, 37, 96],
    #[54, 38, 66, 55, 38, 34],
    #[53, 39, 65, 7, 39, 97],
    #[55, 40, 12, 54, 40, 36],
    #[29, 41, 76, 90, 41, 104],
    #[89, 42, 22, 125, 42, 5],
    #[88, 43, 0, 87, 43, 6],
    #[125, 44, 20, 89, 44, 48],
    #[61, 45, 72, 60, 45, 102],
    #[115, 46, 73, 62, 46, 103],
    #[60, 47, 74, 61, 47, 41],
    #[9, 48, 16, 10, 48, 43],
    #[103, 49, 26, 102, 49, 7],
    #[101, 50, 86, 41, 50, 53],
    #[102, 51, 24, 103, 51, 54],
    #[77, 52, 79, 78, 52, 107],
    #[21, 53, 81, 22, 53, 49],
    #[20, 54, 80, 0, 54, 108],
    #[22, 55, 23, 21, 55, 51],
    #[36, 56, 91, 97, 56, 115],
    #[96, 57, 33, 126, 57, 10],
    #[95, 58, 1, 94, 58, 11],
    #[126, 59, 31, 96, 59, 63],
    #[69, 60, 87, 68, 60, 113],
    #[119, 61, 88, 70, 61, 114],
    #[68, 62, 89, 69, 62, 56],
    #[13, 63, 27, 14, 63, 58],
    #[51, 64, 98, 108, 64, 119],
    #[107, 65, 40, 127, 65, 14],
    #[106, 66, 2, 105, 66, 15],
    #[127, 67, 38, 107, 67, 71],
    #[84, 68, 94, 83, 68, 117],
    #[124, 69, 95, 85, 69, 118],
    #[83, 70, 96, 84, 70, 64],
    #[24, 71, 34, 25, 71, 66],
    #[57, 72, 46, 8, 72, 78],
    #[59, 73, 45, 58, 73, 77],
    #[8, 74, 104, 57, 74, 76],
    #[56, 75, 5, 112, 75, 22],
    #[30, 76, 101, 91, 76, 120],
    #[93, 77, 102, 92, 77, 72],
    #[91, 78, 103, 30, 78, 73],
    #[18, 79, 109, 75, 79, 124],
    #[74, 80, 55, 120, 80, 25],
    #[73, 81, 7, 72, 81, 26],
    #[120, 82, 53, 74, 82, 86],
    #[46, 83, 105, 45, 83, 122],
    #[104, 84, 106, 47, 84, 123],
    #[45, 85, 107, 46, 85, 79],
    #[4, 86, 49, 5, 86, 81],
    #[65, 87, 61, 12, 87, 93],
    #[67, 88, 60, 66, 88, 92],
    #[12, 89, 115, 65, 89, 91],
    #[64, 90, 10, 116, 90, 33],
    #[37, 91, 112, 98, 91, 125],
    #[100, 92, 113, 99, 92, 87],
    #[98, 93, 114, 37, 93, 88],
    #[80, 94, 69, 23, 94, 100],
    #[82, 95, 68, 81, 95, 99],
    #[23, 96, 119, 80, 96, 98],
    #[79, 97, 14, 121, 97, 40],
    #[52, 98, 116, 109, 98, 126],
    #[111, 99, 117, 110, 99, 94],
    #[109, 100, 118, 52, 100, 95],
    #[27, 101, 19, 28, 101, 47],
    #[90, 102, 78, 29, 102, 46],
    #[28, 103, 77, 27, 103, 45],
    #[62, 104, 120, 115, 104, 101],
    #[42, 105, 84, 3, 105, 111],
    #[44, 106, 83, 43, 106, 110],
    #[3, 107, 124, 42, 107, 109],
    #[41, 108, 25, 101, 108, 55],
    #[19, 109, 121, 76, 109, 127],
    #[78, 110, 122, 77, 110, 105],
    #[76, 111, 123, 19, 111, 106],
    #[34, 112, 30, 35, 112, 62],
    #[97, 113, 93, 36, 113, 61],
    #[35, 114, 92, 34, 114, 60],
    #[70, 115, 125, 119, 115, 112],
    #[49, 116, 37, 50, 116, 70],
    #[108, 117, 100, 51, 117, 69],
    #[50, 118, 99, 49, 118, 68],
    #[85, 119, 126, 124, 119, 116],
    #[58, 120, 47, 59, 120, 19],
    #[16, 121, 52, 17, 121, 85],
    #[75, 122, 111, 18, 122, 84],
    #[17, 123, 110, 16, 123, 83],
    #[47, 124, 127, 104, 124, 121],
    #[66, 125, 62, 67, 125, 30],
    #[81, 126, 70, 82, 126, 37],
    #[43, 127, 85, 44, 127, 52]] : Array (Array ℕ)).getD k.val #[]).getD j.val 0)
private def prev31_6 (k : Fin 128) (j : Fin 6) : Fin 128 :=
  Fin.ofNat 128 (((#[#[7, 0, 43, 54, 0, 16],
    #[0, 1, 58, 21, 1, 27],
    #[1, 2, 66, 32, 2, 34],
    #[107, 3, 22, 105, 3, 5],
    #[86, 4, 18, 25, 4, 3],
    #[25, 5, 75, 86, 5, 42],
    #[26, 6, 16, 24, 6, 43],
    #[2, 7, 81, 39, 7, 49],
    #[74, 8, 33, 72, 8, 10],
    #[48, 9, 29, 5, 9, 8],
    #[5, 10, 90, 48, 10, 57],
    #[6, 11, 27, 4, 11, 58],
    #[89, 12, 40, 87, 12, 14],
    #[63, 13, 36, 10, 13, 12],
    #[10, 14, 97, 63, 14, 65],
    #[11, 15, 34, 9, 15, 66],
    #[121, 16, 48, 123, 16, 20],
    #[123, 17, 6, 121, 17, 0],
    #[79, 18, 5, 122, 18, 22],
    #[109, 19, 101, 111, 19, 120],
    #[54, 20, 44, 7, 20, 17],
    #[53, 21, 3, 55, 21, 18],
    #[55, 22, 42, 53, 22, 75],
    #[96, 23, 55, 94, 23, 25],
    #[71, 24, 51, 14, 24, 23],
    #[14, 25, 108, 71, 25, 80],
    #[15, 26, 49, 13, 26, 81],
    #[101, 27, 63, 103, 27, 31],
    #[103, 28, 11, 101, 28, 1],
    #[41, 29, 10, 102, 29, 33],
    #[76, 30, 112, 78, 30, 125],
    #[21, 31, 59, 0, 31, 28],
    #[20, 32, 8, 22, 32, 29],
    #[22, 33, 57, 20, 33, 90],
    #[112, 34, 71, 114, 34, 38],
    #[114, 35, 15, 112, 35, 2],
    #[56, 36, 14, 113, 36, 40],
    #[91, 37, 116, 93, 37, 126],
    #[32, 38, 67, 1, 38, 35],
    #[31, 39, 12, 33, 39, 36],
    #[33, 40, 65, 31, 40, 97],
    #[108, 41, 19, 50, 41, 47],
    #[105, 42, 21, 107, 42, 4],
    #[127, 43, 20, 106, 43, 48],
    #[106, 44, 0, 127, 44, 6],
    #[85, 45, 73, 83, 45, 103],
    #[83, 46, 72, 85, 46, 102],
    #[124, 47, 120, 84, 47, 101],
    #[24, 48, 17, 26, 48, 44],
    #[116, 49, 86, 118, 49, 53],
    #[118, 50, 26, 116, 50, 7],
    #[64, 51, 25, 117, 51, 55],
    #[98, 52, 121, 100, 52, 127],
    #[39, 53, 82, 2, 53, 50],
    #[38, 54, 23, 40, 54, 51],
    #[40, 55, 80, 38, 55, 108],
    #[75, 56, 30, 17, 56, 62],
    #[72, 57, 32, 74, 57, 9],
    #[120, 58, 31, 73, 58, 63],
    #[73, 59, 1, 120, 59, 11],
    #[47, 60, 88, 45, 60, 114],
    #[45, 61, 87, 47, 61, 113],
    #[104, 62, 125, 46, 62, 112],
    #[4, 63, 28, 6, 63, 59],
    #[90, 64, 37, 28, 64, 70],
    #[87, 65, 39, 89, 65, 13],
    #[125, 66, 38, 88, 66, 71],
    #[88, 67, 2, 125, 67, 15],
    #[62, 68, 95, 60, 68, 118],
    #[60, 69, 94, 62, 69, 117],
    #[115, 70, 126, 61, 70, 116],
    #[9, 71, 35, 11, 71, 67],
    #[23, 72, 45, 81, 72, 77],
    #[81, 73, 46, 23, 73, 78],
    #[80, 74, 47, 82, 74, 19],
    #[122, 75, 4, 79, 75, 21],
    #[111, 76, 41, 109, 76, 74],
    #[52, 77, 103, 110, 77, 73],
    #[110, 78, 102, 52, 78, 72],
    #[97, 79, 52, 35, 79, 85],
    #[94, 80, 54, 96, 80, 24],
    #[126, 81, 53, 95, 81, 86],
    #[95, 82, 7, 126, 82, 26],
    #[70, 83, 106, 68, 83, 123],
    #[68, 84, 105, 70, 84, 122],
    #[119, 85, 127, 69, 85, 121],
    #[13, 86, 50, 15, 86, 82],
    #[3, 87, 60, 43, 87, 92],
    #[43, 88, 61, 3, 88, 93],
    #[42, 89, 62, 44, 89, 30],
    #[102, 90, 9, 41, 90, 32],
    #[78, 91, 56, 76, 91, 89],
    #[19, 92, 114, 77, 92, 88],
    #[77, 93, 113, 19, 93, 87],
    #[8, 94, 68, 58, 94, 99],
    #[58, 95, 69, 8, 95, 100],
    #[57, 96, 70, 59, 96, 37],
    #[113, 97, 13, 56, 97, 39],
    #[93, 98, 64, 91, 98, 96],
    #[30, 99, 118, 92, 99, 95],
    #[92, 100, 117, 30, 100, 94],
    #[50, 101, 76, 108, 101, 104],
    #[51, 102, 77, 49, 102, 45],
    #[49, 103, 78, 51, 103, 46],
    #[84, 104, 74, 124, 104, 41],
    #[12, 105, 83, 66, 105, 110],
    #[66, 106, 84, 12, 106, 111],
    #[65, 107, 85, 67, 107, 52],
    #[117, 108, 24, 64, 108, 54],
    #[100, 109, 79, 98, 109, 107],
    #[37, 110, 123, 99, 110, 106],
    #[99, 111, 122, 37, 111, 105],
    #[17, 112, 91, 75, 112, 115],
    #[18, 113, 92, 16, 113, 60],
    #[16, 114, 93, 18, 114, 61],
    #[46, 115, 89, 104, 115, 56],
    #[28, 116, 98, 90, 116, 119],
    #[29, 117, 99, 27, 117, 68],
    #[27, 118, 100, 29, 118, 69],
    #[61, 119, 96, 115, 119, 64],
    #[82, 120, 104, 80, 120, 76],
    #[35, 121, 109, 97, 121, 124],
    #[36, 122, 110, 34, 122, 83],
    #[34, 123, 111, 36, 123, 84],
    #[69, 124, 107, 119, 124, 79],
    #[44, 125, 115, 42, 125, 91],
    #[59, 126, 119, 57, 126, 98],
    #[67, 127, 124, 65, 127, 109]] : Array (Array ℕ)).getD k.val #[]).getD j.val 0)
set_option maxHeartbeats 1600000 in
private theorem cert31_6 : ∃ c, c ∈ Subgroup.centralizer (Subgroup.closure (Set.range e31_6) : Set SylowModel) ∧ c ∉ Subgroup.closure (Set.range e31_6) := by
  refine ⟨rootOne ^ 2 * root 2 * root 4 * root 8, centralizes_generators e31_6 _ (by decide +kernel), ?_⟩
  exact outside_of_table e31_6 a31_6 0 next31_6 prev31_6
    (by decide +kernel) (by decide +kernel) (by decide +kernel) _ (by decide +kernel)

private def e31_7 : Fin 6 → SylowModel := ![decode 0, decode 3136, decode 4028, decode 2048, decode 1984, decode 1516]
set_option maxHeartbeats 1600000 in
private theorem edgeEq31_7 : binaryFamily s31 (s31 0) (![true, true, true]) = e31_7 := by decide +kernel
private def a31_7 (k : Fin 128) : SylowModel :=
  decode ((#[0, 2048, 764, 384, 768, 512, 1168, 1984, 2172, 2432, 2816, 2560, 892, 508, 252, 464, 640, 896, 256, 3216, 3776, 1468, 1260, 1040, 1936, 1680, 1856, 1216, 1472, 2556, 2940, 2684, 2256, 2688, 2944, 2304, 300, 124, 380, 1020, 80, 720, 976, 128, 3644, 3692, 3088, 3984, 3728, 3648, 3520, 3264, 1340, 1724, 1980, 1132, 2028, 1772, 1808, 1552, 1424, 1088, 1344, 1728, 2732, 2812, 3068, 2428, 2384, 3024, 2768, 2176, 172, 556, 812, 636, 848, 592, 208, 3772, 3388, 3132, 3820, 3436, 3180, 3856, 3600, 3472, 3392, 3136, 4032, 1596, 1852, 1212, 1900, 1644, 1516, 1296, 1600, 2860, 2476, 2220, 2300, 2640, 2896, 2512, 940, 684, 44, 336, 3516, 3260, 3900, 3564, 3308, 3948, 3344, 3904, 1084, 1388, 2092, 2348, 2988, 2128, 428, 4028, 4076, 2604] : Array ℕ).getD k.val 0)
private def next31_7 (k : Fin 128) (j : Fin 6) : Fin 128 :=
  Fin.ofNat 128 (((#[#[0, 89, 125, 1, 7, 96],
    #[1, 62, 118, 0, 20, 115],
    #[2, 79, 90, 65, 52, 24],
    #[3, 50, 44, 9, 98, 55],
    #[4, 117, 111, 10, 27, 57],
    #[5, 49, 110, 11, 28, 56],
    #[6, 76, 37, 19, 105, 100],
    #[7, 0, 108, 90, 33, 29],
    #[8, 52, 63, 37, 79, 47],
    #[9, 27, 21, 3, 117, 82],
    #[10, 98, 92, 4, 50, 84],
    #[11, 26, 91, 5, 51, 83],
    #[12, 112, 49, 30, 93, 59],
    #[13, 110, 51, 29, 91, 6],
    #[14, 111, 50, 102, 92, 60],
    #[15, 87, 83, 105, 59, 92],
    #[16, 20, 80, 33, 62, 94],
    #[17, 90, 81, 34, 61, 95],
    #[18, 88, 79, 35, 63, 22],
    #[19, 103, 65, 6, 78, 73],
    #[20, 1, 122, 63, 16, 12],
    #[21, 75, 41, 110, 102, 35],
    #[22, 74, 43, 114, 100, 104],
    #[23, 42, 14, 46, 68, 121],
    #[24, 40, 12, 47, 70, 64],
    #[25, 109, 75, 48, 69, 122],
    #[26, 43, 72, 117, 11, 67],
    #[27, 4, 74, 51, 9, 65],
    #[28, 5, 73, 50, 71, 66],
    #[29, 93, 26, 13, 112, 86],
    #[30, 91, 28, 12, 110, 19],
    #[31, 92, 27, 75, 111, 87],
    #[32, 60, 56, 78, 86, 111],
    #[33, 7, 53, 16, 89, 113],
    #[34, 63, 54, 17, 88, 114],
    #[35, 61, 52, 18, 90, 45],
    #[36, 83, 85, 121, 57, 26],
    #[37, 81, 88, 8, 54, 97],
    #[38, 80, 89, 67, 53, 23],
    #[39, 125, 20, 66, 118, 25],
    #[40, 46, 114, 123, 24, 53],
    #[41, 48, 45, 70, 97, 118],
    #[42, 47, 115, 69, 23, 52],
    #[43, 51, 112, 71, 26, 119],
    #[44, 102, 69, 91, 75, 18],
    #[45, 101, 71, 95, 73, 77],
    #[46, 70, 31, 23, 40, 107],
    #[47, 68, 29, 24, 42, 36],
    #[48, 123, 102, 25, 41, 108],
    #[49, 71, 99, 98, 5, 39],
    #[50, 10, 101, 28, 3, 37],
    #[51, 11, 100, 27, 43, 38],
    #[52, 2, 77, 80, 8, 9],
    #[53, 38, 15, 79, 66, 11],
    #[54, 37, 78, 125, 65, 10],
    #[55, 106, 0, 84, 121, 69],
    #[56, 108, 17, 126, 64, 123],
    #[57, 36, 16, 82, 122, 68],
    #[58, 78, 39, 85, 103, 127],
    #[59, 15, 2, 86, 104, 99],
    #[60, 77, 38, 87, 32, 101],
    #[61, 17, 106, 89, 35, 31],
    #[62, 16, 107, 88, 1, 30],
    #[63, 18, 36, 20, 34, 102],
    #[64, 56, 58, 107, 84, 49],
    #[65, 54, 61, 2, 81, 116],
    #[66, 53, 62, 39, 80, 46],
    #[67, 118, 7, 38, 125, 48],
    #[68, 23, 95, 109, 47, 80],
    #[69, 25, 22, 42, 116, 125],
    #[70, 24, 96, 41, 46, 79],
    #[71, 28, 93, 43, 49, 126],
    #[72, 114, 48, 101, 94, 63],
    #[73, 45, 46, 127, 96, 61],
    #[74, 115, 116, 99, 22, 62],
    #[75, 44, 117, 31, 21, 58],
    #[76, 85, 126, 104, 6, 21],
    #[77, 86, 82, 103, 60, 93],
    #[78, 19, 84, 32, 58, 91],
    #[79, 8, 104, 53, 2, 3],
    #[80, 66, 32, 52, 38, 5],
    #[81, 65, 105, 118, 37, 4],
    #[82, 120, 1, 57, 107, 41],
    #[83, 122, 34, 119, 36, 109],
    #[84, 64, 33, 55, 108, 40],
    #[85, 105, 67, 58, 76, 124],
    #[86, 32, 8, 59, 77, 72],
    #[87, 104, 66, 60, 15, 74],
    #[88, 34, 120, 62, 18, 14],
    #[89, 33, 121, 61, 0, 13],
    #[90, 35, 64, 7, 17, 75],
    #[91, 13, 109, 44, 30, 33],
    #[92, 14, 40, 112, 31, 34],
    #[93, 12, 42, 111, 29, 1],
    #[94, 72, 4, 115, 127, 32],
    #[95, 124, 5, 45, 99, 105],
    #[96, 73, 3, 113, 101, 103],
    #[97, 41, 13, 116, 123, 120],
    #[98, 3, 124, 49, 10, 8],
    #[99, 95, 25, 74, 113, 90],
    #[100, 22, 23, 124, 115, 88],
    #[101, 96, 97, 72, 45, 89],
    #[102, 21, 98, 14, 44, 85],
    #[103, 58, 119, 77, 19, 44],
    #[104, 59, 55, 76, 87, 112],
    #[105, 6, 57, 15, 85, 110],
    #[106, 126, 87, 122, 55, 28],
    #[107, 82, 19, 64, 119, 27],
    #[108, 84, 86, 120, 56, 98],
    #[109, 116, 113, 68, 25, 54],
    #[110, 30, 123, 21, 13, 16],
    #[111, 31, 68, 93, 14, 17],
    #[112, 29, 70, 92, 12, 0],
    #[113, 99, 10, 96, 124, 15],
    #[114, 127, 11, 22, 72, 78],
    #[115, 100, 9, 94, 74, 76],
    #[116, 69, 30, 97, 109, 106],
    #[117, 9, 127, 26, 4, 2],
    #[118, 39, 76, 81, 67, 71],
    #[119, 107, 18, 83, 120, 70],
    #[120, 119, 60, 108, 82, 51],
    #[121, 55, 6, 36, 126, 50],
    #[122, 57, 59, 106, 83, 117],
    #[123, 97, 94, 40, 48, 81],
    #[124, 113, 47, 100, 95, 7],
    #[125, 67, 103, 54, 39, 43],
    #[126, 121, 35, 56, 106, 42],
    #[127, 94, 24, 73, 114, 20]] : Array (Array ℕ)).getD k.val #[]).getD j.val 0)
private def prev31_7 (k : Fin 128) (j : Fin 6) : Fin 128 :=
  Fin.ofNat 128 (((#[#[0, 7, 55, 1, 89, 112],
    #[1, 20, 82, 0, 62, 93],
    #[2, 52, 59, 65, 79, 117],
    #[3, 98, 96, 9, 50, 79],
    #[4, 27, 94, 10, 117, 81],
    #[5, 28, 95, 11, 49, 80],
    #[6, 105, 121, 19, 76, 13],
    #[7, 33, 67, 90, 0, 124],
    #[8, 79, 86, 37, 52, 98],
    #[9, 117, 115, 3, 27, 52],
    #[10, 50, 113, 4, 98, 54],
    #[11, 51, 114, 5, 26, 53],
    #[12, 93, 24, 30, 112, 20],
    #[13, 91, 97, 29, 110, 89],
    #[14, 92, 23, 102, 111, 88],
    #[15, 59, 53, 105, 87, 113],
    #[16, 62, 57, 33, 20, 110],
    #[17, 61, 56, 34, 90, 111],
    #[18, 63, 119, 35, 88, 44],
    #[19, 78, 107, 6, 103, 30],
    #[20, 16, 39, 63, 1, 127],
    #[21, 102, 9, 110, 75, 76],
    #[22, 100, 69, 114, 74, 18],
    #[23, 68, 100, 46, 42, 38],
    #[24, 70, 127, 47, 40, 2],
    #[25, 69, 99, 48, 109, 39],
    #[26, 11, 29, 117, 43, 36],
    #[27, 9, 31, 51, 4, 107],
    #[28, 71, 30, 50, 5, 106],
    #[29, 112, 47, 13, 93, 7],
    #[30, 110, 116, 12, 91, 62],
    #[31, 111, 46, 75, 92, 61],
    #[32, 86, 80, 78, 60, 94],
    #[33, 89, 84, 16, 7, 91],
    #[34, 88, 83, 17, 63, 92],
    #[35, 90, 126, 18, 61, 21],
    #[36, 57, 63, 121, 83, 47],
    #[37, 54, 6, 8, 81, 50],
    #[38, 53, 60, 67, 80, 51],
    #[39, 118, 58, 66, 125, 49],
    #[40, 24, 92, 123, 46, 84],
    #[41, 97, 21, 70, 48, 82],
    #[42, 23, 93, 69, 47, 126],
    #[43, 26, 22, 71, 51, 125],
    #[44, 75, 3, 91, 102, 103],
    #[45, 73, 41, 95, 101, 35],
    #[46, 40, 73, 23, 70, 66],
    #[47, 42, 124, 24, 68, 8],
    #[48, 41, 72, 25, 123, 67],
    #[49, 5, 12, 98, 71, 64],
    #[50, 3, 14, 28, 10, 121],
    #[51, 43, 13, 27, 11, 120],
    #[52, 8, 35, 80, 2, 42],
    #[53, 66, 33, 79, 38, 40],
    #[54, 65, 34, 125, 37, 109],
    #[55, 121, 104, 84, 106, 3],
    #[56, 64, 32, 126, 108, 5],
    #[57, 122, 105, 82, 36, 4],
    #[58, 103, 64, 85, 78, 75],
    #[59, 104, 122, 86, 15, 12],
    #[60, 32, 120, 87, 77, 14],
    #[61, 35, 65, 89, 17, 73],
    #[62, 1, 66, 88, 16, 74],
    #[63, 34, 8, 20, 18, 72],
    #[64, 84, 90, 107, 56, 24],
    #[65, 81, 19, 2, 54, 27],
    #[66, 80, 87, 39, 53, 28],
    #[67, 125, 85, 38, 118, 26],
    #[68, 47, 111, 109, 23, 57],
    #[69, 116, 44, 42, 25, 55],
    #[70, 46, 112, 41, 24, 119],
    #[71, 49, 45, 43, 28, 118],
    #[72, 94, 26, 101, 114, 86],
    #[73, 96, 28, 127, 45, 19],
    #[74, 22, 27, 99, 115, 87],
    #[75, 21, 25, 31, 44, 90],
    #[76, 6, 118, 104, 85, 115],
    #[77, 60, 52, 103, 86, 45],
    #[78, 58, 54, 32, 19, 114],
    #[79, 2, 18, 53, 8, 70],
    #[80, 38, 16, 52, 66, 68],
    #[81, 37, 17, 118, 65, 123],
    #[82, 107, 77, 57, 120, 9],
    #[83, 36, 15, 119, 122, 11],
    #[84, 108, 78, 55, 64, 10],
    #[85, 76, 36, 58, 105, 102],
    #[86, 77, 108, 59, 32, 29],
    #[87, 15, 106, 60, 104, 31],
    #[88, 18, 37, 62, 34, 100],
    #[89, 0, 38, 61, 33, 101],
    #[90, 17, 2, 7, 35, 99],
    #[91, 30, 11, 44, 13, 78],
    #[92, 31, 10, 112, 14, 15],
    #[93, 29, 71, 111, 12, 77],
    #[94, 127, 123, 115, 72, 16],
    #[95, 99, 68, 45, 124, 17],
    #[96, 101, 70, 113, 73, 0],
    #[97, 123, 101, 116, 41, 37],
    #[98, 10, 102, 49, 3, 108],
    #[99, 113, 49, 74, 95, 59],
    #[100, 115, 51, 124, 22, 6],
    #[101, 45, 50, 72, 96, 60],
    #[102, 44, 48, 14, 21, 63],
    #[103, 19, 125, 77, 58, 96],
    #[104, 87, 79, 76, 59, 22],
    #[105, 85, 81, 15, 6, 95],
    #[106, 55, 61, 122, 126, 116],
    #[107, 119, 62, 64, 82, 46],
    #[108, 56, 7, 120, 84, 48],
    #[109, 25, 91, 68, 116, 83],
    #[110, 13, 5, 21, 30, 105],
    #[111, 14, 4, 93, 31, 32],
    #[112, 12, 43, 92, 29, 104],
    #[113, 124, 109, 96, 99, 33],
    #[114, 72, 40, 22, 127, 34],
    #[115, 74, 42, 94, 100, 1],
    #[116, 109, 74, 97, 69, 65],
    #[117, 4, 75, 26, 9, 122],
    #[118, 67, 1, 81, 39, 41],
    #[119, 120, 103, 83, 107, 43],
    #[120, 82, 88, 108, 119, 97],
    #[121, 126, 89, 36, 55, 23],
    #[122, 83, 20, 106, 57, 25],
    #[123, 48, 110, 40, 97, 56],
    #[124, 95, 98, 100, 113, 85],
    #[125, 39, 0, 54, 67, 69],
    #[126, 106, 76, 56, 121, 71],
    #[127, 114, 117, 73, 94, 58]] : Array (Array ℕ)).getD k.val #[]).getD j.val 0)
set_option maxHeartbeats 1600000 in
private theorem cert31_7 : ∃ c, c ∈ Subgroup.centralizer (Subgroup.closure (Set.range e31_7) : Set SylowModel) ∧ c ∉ Subgroup.closure (Set.range e31_7) := by
  refine ⟨rootOne ^ 2 * root 2 * root 4 * root 7, centralizes_generators e31_7 _ (by decide +kernel), ?_⟩
  exact outside_of_table e31_7 a31_7 0 next31_7 prev31_7
    (by decide +kernel) (by decide +kernel) (by decide +kernel) _ (by decide +kernel)

private def s32 : Fin 3 → SylowModel := ![root 2 * root 3 * root 4 * root 7, root 6, rootOne ^ 3 * root 5 * root 8]
set_option maxHeartbeats 1600000 in
private theorem gen32 : Subgroup.closure (Set.range s32) = smallParityCensusNode 32 := by
  rw [node32]
  exact closure_eq_words s32 o32 (![[1], [4, 5, 6], [0]]) (![[2], [0], [0, 1, 0, 2, 2], [0, 0, 2, 0, 2, 0, 2, 2], [0, 1, 0, 2, 2, 2, 2], [0, 0, 2, 2, 2, 2], [0, 0, 0, 1, 0, 1], [2, 2, 2, 2]]) (by decide +kernel) (by decide +kernel)

private def e32_1 : Fin 6 → SylowModel := ![decode 0, decode 64, decode 1632, decode 640, decode 576, decode 1136]
set_option maxHeartbeats 1600000 in
private theorem edgeEq32_1 : binaryFamily s32 (s32 0) (![true, false, false]) = e32_1 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert32_1 : Represented smallParityCensusNode (Subgroup.closure (Set.range e32_1)) := by
  refine ⟨63, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node63]
  exact closure_eq_words _ o63 (![[], [3, 4, 5], [0], [5, 6], [3, 5], [0, 1, 6]]) (![[2], [2, 2, 2, 5], [1, 3, 5, 5], [2, 2, 2, 4, 2], [1, 4], [2, 2, 2, 2, 3], [2, 2, 2, 2]]) (by decide +kernel) (by decide +kernel)

private def e32_2 : Fin 6 → SylowModel := ![decode 156, decode 0, decode 1632, decode 668, decode 0, decode 1504]
set_option maxHeartbeats 1600000 in
private theorem edgeEq32_2 : binaryFamily s32 (s32 1) (![false, true, false]) = e32_2 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert32_2 : Represented smallParityCensusNode (Subgroup.closure (Set.range e32_2)) := by
  refine ⟨66, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node66]
  exact closure_eq_words _ o66 (![[1], [], [0], [1, 5], [], [0, 4]]) (![[2], [0], [2, 2], [0, 2, 2, 5, 0, 2], [0, 0], [0, 0, 0, 3], [2, 2, 2, 2]]) (by decide +kernel) (by decide +kernel)

private def e32_3 : Fin 6 → SylowModel := ![decode 0, decode 92, decode 1632, decode 640, decode 220, decode 1136]
set_option maxHeartbeats 1600000 in
private theorem edgeEq32_3 : binaryFamily s32 (s32 0) (![true, true, false]) = e32_3 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert32_3 : Represented smallParityCensusNode (Subgroup.closure (Set.range e32_3)) := by
  refine ⟨66, root 1 * root 2 * root 4 * root 6 * root 7 * root 9, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node66]
  exact closure_eq_words _ o66 (![[], [1, 4, 6], [1, 0], [4, 5], [1, 6], [1, 3, 4, 0]]) (![[5, 1, 3], [2, 2, 2, 2, 4], [1, 2, 1, 2], [2, 2, 2, 5, 3], [1, 1], [1, 1, 3], [2, 2, 2, 2]]) (by decide +kernel) (by decide +kernel)

private def e32_4 : Fin 6 → SylowModel := ![decode 156, decode 64, decode 0, decode 908, decode 960, decode 2240]
set_option maxHeartbeats 1600000 in
private theorem edgeEq32_4 : binaryFamily s32 (s32 2) (![false, false, true]) = e32_4 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert32_4 : Subgroup.closure (Set.range e32_4) ≤ character.ker := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨j, rfl⟩
  exact (show ∀ j, e32_4 j ∈ character.ker from by decide +kernel) j

private def e32_5 : Fin 6 → SylowModel := ![decode 0, decode 64, decode 1644, decode 640, decode 576, decode 1788]
set_option maxHeartbeats 1600000 in
private theorem edgeEq32_5 : binaryFamily s32 (s32 0) (![true, false, true]) = e32_5 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert32_5 : Represented smallParityCensusNode (Subgroup.closure (Set.range e32_5)) := by
  refine ⟨63, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node63]
  exact closure_eq_words _ o63 (![[], [3, 5], [0, 4], [4, 5, 6], [3, 4, 5], [0, 1, 6]]) (![[1, 4, 2], [2, 2, 5, 2], [1, 3, 5, 5], [2, 2, 2, 1, 2], [1, 4], [2, 2, 3, 5, 5], [2, 2, 2, 2]]) (by decide +kernel) (by decide +kernel)

private def e32_6 : Fin 6 → SylowModel := ![decode 156, decode 0, decode 1440, decode 668, decode 0, decode 1568]
set_option maxHeartbeats 1600000 in
private theorem edgeEq32_6 : binaryFamily s32 (s32 1) (![false, true, true]) = e32_6 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert32_6 : Represented smallParityCensusNode (Subgroup.closure (Set.range e32_6)) := by
  refine ⟨66, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node66]
  exact closure_eq_words _ o66 (![[1], [], [3, 0], [1, 5], [], [3, 0, 4]]) (![[0, 5, 3], [0], [0, 2, 5, 0], [0, 2, 2, 2, 0, 5], [0, 0], [0, 0, 0, 3], [2, 2, 2, 2]]) (by decide +kernel) (by decide +kernel)

private def e32_7 : Fin 6 → SylowModel := ![decode 0, decode 92, decode 1644, decode 640, decode 220, decode 1788]
set_option maxHeartbeats 1600000 in
private theorem edgeEq32_7 : binaryFamily s32 (s32 0) (![true, true, true]) = e32_7 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert32_7 : Represented smallParityCensusNode (Subgroup.closure (Set.range e32_7)) := by
  refine ⟨66, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node66]
  exact closure_eq_words _ o66 (![[], [1, 4, 6], [0, 5], [4, 5], [1, 6], [0, 3, 6]]) (![[1, 5, 4], [2, 2, 2, 2, 4], [2, 2], [2, 2, 5, 2], [1, 1], [1, 1, 3], [2, 2, 2, 2]]) (by decide +kernel) (by decide +kernel)

private def s33 : Fin 2 → SylowModel := ![root 4 * root 7 * root 8, rootOne * root 0 * root 1 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8 * root 9]
set_option maxHeartbeats 1600000 in
private theorem gen33 : Subgroup.closure (Set.range s33) = smallParityCensusNode 33 := by
  rw [node33]
  exact closure_eq_words s33 o33 (![[2, 6, 7], [0]]) (![[1], [1, 1], [1, 0, 1, 0, 1, 1, 1, 1, 1, 0, 1], [1, 1, 1, 1], [0, 1, 1, 1, 1, 1, 1, 1, 0, 1], [0, 1, 1, 0, 1, 1, 1, 1, 1, 1], [0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1], [1, 1, 1, 1, 1, 1, 1, 1]]) (by decide +kernel) (by decide +kernel)

private def e33_1 : Fin 4 → SylowModel := ![decode 0, decode 3073, decode 0, decode 4033]
set_option maxHeartbeats 1600000 in
private theorem edgeEq33_1 : binaryFamily s33 (s33 0) (![true, false]) = e33_1 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert33_1 : Represented smallParityCensusNode (Subgroup.closure (Set.range e33_1)) := by
  refine ⟨67, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node67]
  exact closure_eq_words _ o67 (![[], [0], [], [0, 2, 6]]) (![[1], [1, 1], [1, 1, 1, 1, 1, 1, 1, 3], [1, 1, 1, 1], [1, 1, 1, 1, 3, 3, 1, 1], [1, 1, 1, 1, 3, 1, 3, 1], [1, 1, 1, 1, 1, 1, 1, 1]]) (by decide +kernel) (by decide +kernel)

private def e33_2 : Fin 4 → SylowModel := ![decode 400, decode 0, decode 80, decode 2522]
set_option maxHeartbeats 1600000 in
private theorem edgeEq33_2 : binaryFamily s33 (s33 1) (![false, true]) = e33_2 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert33_2 : Subgroup.closure (Set.range e33_2) ≤ character.ker := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨j, rfl⟩
  exact (show ∀ j, e33_2 j ∈ character.ker from by decide +kernel) j

private def e33_3 : Fin 4 → SylowModel := ![decode 0, decode 3217, decode 0, decode 3921]
set_option maxHeartbeats 1600000 in
private theorem edgeEq33_3 : binaryFamily s33 (s33 0) (![true, true]) = e33_3 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert33_3 : Represented smallParityCensusNode (Subgroup.closure (Set.range e33_3)) := by
  refine ⟨67, root 2 * root 3 * root 4 * root 7, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node67]
  exact closure_eq_words _ o67 (![[], [0, 5], [], [0, 2, 5]]) (![[1, 1, 1, 1, 1, 3, 1, 3, 1], [1, 1, 1, 1, 1, 1, 1, 1, 1, 1], [1, 1, 1, 1, 3, 3, 3, 1], [1, 1, 1, 1], [1, 1, 1, 1, 3, 3, 1, 1], [1, 1, 1, 1, 3, 1, 3, 1], [1, 1, 1, 1, 1, 1, 1, 1]]) (by decide +kernel) (by decide +kernel)

private def s34 : Fin 2 → SylowModel := ![root 4 * root 7 * root 8, rootOne * root 0 * root 1 * root 6 * root 7 * root 9]
set_option maxHeartbeats 1600000 in
private theorem gen34 : Subgroup.closure (Set.range s34) = smallParityCensusNode 34 := by
  rw [node34]
  exact closure_eq_words s34 o34 (![[2, 6], [0]]) (![[1], [1, 1], [1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1], [1, 1, 1, 1], [0, 1, 1, 1, 1, 1, 1, 1, 0, 1], [0, 1, 1, 0, 1, 1, 1, 1, 1, 1], [0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1], [1, 1, 1, 1, 1, 1, 1, 1]]) (by decide +kernel) (by decide +kernel)

private def e34_1 : Fin 4 → SylowModel := ![decode 0, decode 3573, decode 0, decode 3381]
set_option maxHeartbeats 1600000 in
private theorem edgeEq34_1 : binaryFamily s34 (s34 0) (![true, false]) = e34_1 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert34_1 : Represented smallParityCensusNode (Subgroup.closure (Set.range e34_1)) := by
  refine ⟨68, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node68]
  exact closure_eq_words _ o68 (![[], [0], [], [0, 2, 6]]) (![[1], [1, 1], [1, 1, 1, 1, 1, 1, 1, 3], [1, 1, 1, 1], [1, 1, 1, 1, 3, 3, 1, 1], [1, 1, 1, 1, 3, 1, 3, 1], [1, 1, 1, 1, 1, 1, 1, 1]]) (by decide +kernel) (by decide +kernel)

private def e34_2 : Fin 4 → SylowModel := ![decode 400, decode 0, decode 336, decode 2106]
set_option maxHeartbeats 1600000 in
private theorem edgeEq34_2 : binaryFamily s34 (s34 1) (![false, true]) = e34_2 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert34_2 : Subgroup.closure (Set.range e34_2) ≤ character.ker := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨j, rfl⟩
  exact (show ∀ j, e34_2 j ∈ character.ker from by decide +kernel) j

private def e34_3 : Fin 4 → SylowModel := ![decode 0, decode 3941, decode 0, decode 4005]
set_option maxHeartbeats 1600000 in
private theorem edgeEq34_3 : binaryFamily s34 (s34 0) (![true, true]) = e34_3 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert34_3 : Represented smallParityCensusNode (Subgroup.closure (Set.range e34_3)) := by
  refine ⟨68, root 2 * root 3 * root 4 * root 7, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node68]
  exact closure_eq_words _ o68 (![[], [4, 0, 6], [], [2, 5, 0]]) (![[1, 1, 1, 1, 1, 1, 3, 3, 1], [1, 1, 1, 1, 1, 1, 1, 3, 1, 3], [1, 1, 1, 1, 3, 3, 3, 1], [1, 1, 1, 1], [1, 1, 1, 1, 3, 3, 1, 1], [1, 1, 1, 1, 3, 1, 3, 1], [1, 1, 1, 1, 1, 1, 1, 1]]) (by decide +kernel) (by decide +kernel)

private def s35 : Fin 3 → SylowModel := ![root 4 * root 7 * root 8, rootOne ^ 3 * root 3 * root 4, root 5 * root 8]
set_option maxHeartbeats 1600000 in
private theorem gen35 : Subgroup.closure (Set.range s35) = smallParityCensusNode 35 := by
  rw [node35]
  exact closure_eq_words s35 o35 (![[3, 7], [0], [1]]) (![[1], [2], [1, 1], [1, 0, 1, 1, 1], [1, 1, 1, 2, 1, 2], [1, 1, 2, 1, 1, 2], [0, 2, 0, 2], [0, 1, 0, 1, 1, 1]]) (by decide +kernel) (by decide +kernel)

private def e35_1 : Fin 6 → SylowModel := ![decode 0, decode 1032, decode 288, decode 0, decode 1288, decode 800]
set_option maxHeartbeats 1600000 in
private theorem edgeEq35_1 : binaryFamily s35 (s35 0) (![true, false, false]) = e35_1 := by decide +kernel
private def a35_1 (k : Fin 128) : SylowModel :=
  decode ((#[0, 64, 384, 768, 512, 2448, 224, 448, 832, 576, 640, 896, 256, 1032, 2256, 2064, 2704, 2960, 160, 352, 992, 736, 704, 960, 320, 128, 1992, 1160, 1800, 1544, 2544, 2384, 3024, 2768, 2832, 2576, 2192, 288, 928, 672, 608, 864, 480, 192, 3224, 1320, 1864, 1224, 1480, 1928, 1672, 1288, 2224, 2160, 2800, 3056, 2640, 2896, 2512, 2320, 544, 800, 416, 96, 3672, 3096, 3992, 3736, 1768, 1448, 1576, 1832, 1096, 1352, 1736, 1416, 2352, 2992, 2736, 2928, 2672, 2288, 2128, 32, 3128, 3800, 3416, 3160, 3864, 3608, 3480, 1640, 1512, 1256, 1704, 1960, 1064, 1608, 2608, 2864, 2480, 2416, 3832, 3256, 3896, 3640, 3544, 3288, 3928, 3352, 1384, 1128, 2024, 1192, 2096, 3704, 3576, 3320, 4024, 3768, 3384, 4056, 1896, 3448, 3192, 4088, 3512, 3960] : Array ℕ).getD k.val 0)
private def next35_1 (k : Fin 128) (j : Fin 6) : Fin 128 :=
  Fin.ofNat 128 (((#[#[0, 13, 37, 0, 51, 61],
    #[1, 97, 19, 1, 46, 41],
    #[2, 75, 18, 2, 27, 39],
    #[3, 28, 60, 3, 29, 83],
    #[4, 29, 61, 4, 28, 37],
    #[5, 90, 99, 5, 44, 76],
    #[6, 68, 7, 6, 112, 23],
    #[7, 26, 6, 7, 74, 21],
    #[8, 73, 40, 8, 72, 63],
    #[9, 72, 41, 9, 73, 19],
    #[10, 50, 38, 10, 49, 62],
    #[11, 49, 39, 11, 50, 18],
    #[12, 51, 83, 12, 13, 60],
    #[13, 59, 91, 13, 15, 111],
    #[14, 85, 80, 14, 121, 53],
    #[15, 65, 78, 15, 109, 52],
    #[16, 67, 114, 16, 66, 98],
    #[17, 66, 76, 17, 67, 99],
    #[18, 113, 2, 18, 69, 11],
    #[19, 122, 1, 19, 91, 9],
    #[20, 92, 22, 20, 93, 43],
    #[21, 93, 23, 21, 92, 7],
    #[22, 47, 20, 22, 48, 42],
    #[23, 48, 21, 23, 47, 6],
    #[24, 46, 63, 24, 97, 40],
    #[25, 27, 62, 25, 75, 38],
    #[26, 14, 69, 26, 58, 95],
    #[27, 5, 68, 27, 36, 93],
    #[28, 35, 110, 28, 34, 122],
    #[29, 34, 111, 29, 35, 91],
    #[30, 125, 57, 30, 102, 31],
    #[31, 108, 55, 31, 64, 30],
    #[32, 106, 101, 32, 107, 79],
    #[33, 107, 53, 33, 106, 80],
    #[34, 88, 100, 34, 89, 77],
    #[35, 89, 52, 35, 88, 78],
    #[36, 44, 98, 36, 90, 114],
    #[37, 45, 0, 37, 96, 4],
    #[38, 95, 10, 38, 94, 25],
    #[39, 94, 11, 39, 95, 2],
    #[40, 111, 8, 40, 110, 24],
    #[41, 110, 9, 41, 111, 1],
    #[42, 112, 43, 42, 68, 22],
    #[43, 74, 42, 43, 26, 20],
    #[44, 2, 124, 44, 25, 115],
    #[45, 98, 46, 45, 99, 73],
    #[46, 82, 45, 46, 31, 71],
    #[47, 32, 94, 47, 33, 113],
    #[48, 33, 95, 48, 32, 69],
    #[49, 16, 92, 49, 17, 112],
    #[50, 17, 93, 50, 16, 68],
    #[51, 15, 122, 51, 59, 110],
    #[52, 103, 35, 52, 126, 15],
    #[53, 115, 33, 53, 127, 14],
    #[54, 117, 82, 54, 116, 56],
    #[55, 116, 31, 55, 117, 57],
    #[56, 87, 81, 56, 86, 54],
    #[57, 86, 30, 57, 87, 55],
    #[58, 121, 79, 58, 85, 101],
    #[59, 109, 77, 59, 65, 100],
    #[60, 70, 3, 60, 71, 12],
    #[61, 71, 4, 61, 70, 0],
    #[62, 69, 25, 62, 113, 10],
    #[63, 91, 24, 63, 122, 8],
    #[64, 24, 119, 64, 1, 103],
    #[65, 12, 117, 65, 0, 102],
    #[66, 10, 127, 66, 11, 123],
    #[67, 11, 115, 67, 10, 124],
    #[68, 55, 27, 68, 54, 50],
    #[69, 78, 26, 69, 77, 48],
    #[70, 76, 72, 70, 114, 97],
    #[71, 114, 73, 71, 76, 46],
    #[72, 57, 70, 72, 56, 96],
    #[73, 56, 71, 73, 57, 45],
    #[74, 58, 113, 74, 14, 94],
    #[75, 36, 112, 75, 5, 92],
    #[76, 120, 17, 76, 84, 5],
    #[77, 118, 59, 77, 119, 34],
    #[78, 119, 15, 78, 118, 35],
    #[79, 123, 58, 79, 124, 32],
    #[80, 124, 14, 80, 123, 33],
    #[81, 102, 56, 81, 125, 82],
    #[82, 64, 54, 82, 108, 81],
    #[83, 96, 12, 83, 45, 3],
    #[84, 61, 107, 84, 60, 85],
    #[85, 7, 105, 85, 43, 84],
    #[86, 9, 126, 86, 8, 118],
    #[87, 8, 103, 87, 9, 119],
    #[88, 4, 125, 88, 3, 116],
    #[89, 3, 102, 89, 4, 117],
    #[90, 25, 123, 90, 2, 127],
    #[91, 79, 13, 91, 80, 29],
    #[92, 81, 49, 92, 30, 75],
    #[93, 30, 50, 93, 81, 27],
    #[94, 100, 47, 94, 52, 74],
    #[95, 52, 48, 95, 100, 26],
    #[96, 99, 97, 96, 98, 72],
    #[97, 31, 96, 97, 82, 70],
    #[98, 105, 36, 98, 104, 16],
    #[99, 104, 5, 99, 105, 17],
    #[100, 126, 34, 100, 103, 59],
    #[101, 127, 32, 101, 115, 58],
    #[102, 20, 89, 102, 21, 65],
    #[103, 38, 87, 103, 39, 64],
    #[104, 83, 121, 104, 37, 106],
    #[105, 37, 85, 105, 83, 107],
    #[106, 22, 120, 106, 23, 104],
    #[107, 23, 84, 107, 22, 105],
    #[108, 1, 118, 108, 24, 126],
    #[109, 0, 116, 109, 12, 125],
    #[110, 53, 28, 110, 101, 51],
    #[111, 101, 29, 111, 53, 13],
    #[112, 54, 75, 112, 55, 49],
    #[113, 77, 74, 113, 78, 47],
    #[114, 84, 16, 114, 120, 36],
    #[115, 41, 67, 115, 40, 44],
    #[116, 6, 109, 116, 42, 88],
    #[117, 42, 65, 117, 6, 89],
    #[118, 18, 108, 118, 62, 86],
    #[119, 62, 64, 119, 18, 87],
    #[120, 60, 106, 120, 61, 121],
    #[121, 43, 104, 121, 7, 120],
    #[122, 80, 51, 122, 79, 28],
    #[123, 63, 90, 123, 19, 66],
    #[124, 19, 44, 124, 63, 67],
    #[125, 21, 88, 125, 20, 109],
    #[126, 39, 86, 126, 38, 108],
    #[127, 40, 66, 127, 41, 90]] : Array (Array ℕ)).getD k.val #[]).getD j.val 0)
private def prev35_1 (k : Fin 128) (j : Fin 6) : Fin 128 :=
  Fin.ofNat 128 (((#[#[0, 109, 37, 0, 65, 61],
    #[1, 108, 19, 1, 64, 41],
    #[2, 44, 18, 2, 90, 39],
    #[3, 89, 60, 3, 88, 83],
    #[4, 88, 61, 4, 89, 37],
    #[5, 27, 99, 5, 75, 76],
    #[6, 116, 7, 6, 117, 23],
    #[7, 85, 6, 7, 121, 21],
    #[8, 87, 40, 8, 86, 63],
    #[9, 86, 41, 9, 87, 19],
    #[10, 66, 38, 10, 67, 62],
    #[11, 67, 39, 11, 66, 18],
    #[12, 65, 83, 12, 109, 60],
    #[13, 0, 91, 13, 12, 111],
    #[14, 26, 80, 14, 74, 53],
    #[15, 51, 78, 15, 13, 52],
    #[16, 49, 114, 16, 50, 98],
    #[17, 50, 76, 17, 49, 99],
    #[18, 118, 2, 18, 119, 11],
    #[19, 124, 1, 19, 123, 9],
    #[20, 102, 22, 20, 125, 43],
    #[21, 125, 23, 21, 102, 7],
    #[22, 106, 20, 22, 107, 42],
    #[23, 107, 21, 23, 106, 6],
    #[24, 64, 63, 24, 108, 40],
    #[25, 90, 62, 25, 44, 38],
    #[26, 7, 69, 26, 43, 95],
    #[27, 25, 68, 27, 2, 93],
    #[28, 3, 110, 28, 4, 122],
    #[29, 4, 111, 29, 3, 91],
    #[30, 93, 57, 30, 92, 31],
    #[31, 97, 55, 31, 46, 30],
    #[32, 47, 101, 32, 48, 79],
    #[33, 48, 53, 33, 47, 80],
    #[34, 29, 100, 34, 28, 77],
    #[35, 28, 52, 35, 29, 78],
    #[36, 75, 98, 36, 27, 114],
    #[37, 105, 0, 37, 104, 4],
    #[38, 103, 10, 38, 126, 25],
    #[39, 126, 11, 39, 103, 2],
    #[40, 127, 8, 40, 115, 24],
    #[41, 115, 9, 41, 127, 1],
    #[42, 117, 43, 42, 116, 22],
    #[43, 121, 42, 43, 85, 20],
    #[44, 36, 124, 44, 5, 115],
    #[45, 37, 46, 45, 83, 73],
    #[46, 24, 45, 46, 1, 71],
    #[47, 22, 94, 47, 23, 113],
    #[48, 23, 95, 48, 22, 69],
    #[49, 11, 92, 49, 10, 112],
    #[50, 10, 93, 50, 11, 68],
    #[51, 12, 122, 51, 0, 110],
    #[52, 95, 35, 52, 94, 15],
    #[53, 110, 33, 53, 111, 14],
    #[54, 112, 82, 54, 68, 56],
    #[55, 68, 31, 55, 112, 57],
    #[56, 73, 81, 56, 72, 54],
    #[57, 72, 30, 57, 73, 55],
    #[58, 74, 79, 58, 26, 101],
    #[59, 13, 77, 59, 51, 100],
    #[60, 120, 3, 60, 84, 12],
    #[61, 84, 4, 61, 120, 0],
    #[62, 119, 25, 62, 118, 10],
    #[63, 123, 24, 63, 124, 8],
    #[64, 82, 119, 64, 31, 103],
    #[65, 15, 117, 65, 59, 102],
    #[66, 17, 127, 66, 16, 123],
    #[67, 16, 115, 67, 17, 124],
    #[68, 6, 27, 68, 42, 50],
    #[69, 62, 26, 69, 18, 48],
    #[70, 60, 72, 70, 61, 97],
    #[71, 61, 73, 71, 60, 46],
    #[72, 9, 70, 72, 8, 96],
    #[73, 8, 71, 73, 9, 45],
    #[74, 43, 113, 74, 7, 94],
    #[75, 2, 112, 75, 25, 92],
    #[76, 70, 17, 76, 71, 5],
    #[77, 113, 59, 77, 69, 34],
    #[78, 69, 15, 78, 113, 35],
    #[79, 91, 58, 79, 122, 32],
    #[80, 122, 14, 80, 91, 33],
    #[81, 92, 56, 81, 93, 82],
    #[82, 46, 54, 82, 97, 81],
    #[83, 104, 12, 83, 105, 3],
    #[84, 114, 107, 84, 76, 85],
    #[85, 14, 105, 85, 58, 84],
    #[86, 57, 126, 86, 56, 118],
    #[87, 56, 103, 87, 57, 119],
    #[88, 34, 125, 88, 35, 116],
    #[89, 35, 102, 89, 34, 117],
    #[90, 5, 123, 90, 36, 127],
    #[91, 63, 13, 91, 19, 29],
    #[92, 20, 49, 92, 21, 75],
    #[93, 21, 50, 93, 20, 27],
    #[94, 39, 47, 94, 38, 74],
    #[95, 38, 48, 95, 39, 26],
    #[96, 83, 97, 96, 37, 72],
    #[97, 1, 96, 97, 24, 70],
    #[98, 45, 36, 98, 96, 16],
    #[99, 96, 5, 99, 45, 17],
    #[100, 94, 34, 100, 95, 59],
    #[101, 111, 32, 101, 110, 58],
    #[102, 81, 89, 102, 30, 65],
    #[103, 52, 87, 103, 100, 64],
    #[104, 99, 121, 104, 98, 106],
    #[105, 98, 85, 105, 99, 107],
    #[106, 32, 120, 106, 33, 104],
    #[107, 33, 84, 107, 32, 105],
    #[108, 31, 118, 108, 82, 126],
    #[109, 59, 116, 109, 15, 125],
    #[110, 41, 28, 110, 40, 51],
    #[111, 40, 29, 111, 41, 13],
    #[112, 42, 75, 112, 6, 49],
    #[113, 18, 74, 113, 62, 47],
    #[114, 71, 16, 114, 70, 36],
    #[115, 53, 67, 115, 101, 44],
    #[116, 55, 109, 116, 54, 88],
    #[117, 54, 65, 117, 55, 89],
    #[118, 77, 108, 118, 78, 86],
    #[119, 78, 64, 119, 77, 87],
    #[120, 76, 106, 120, 114, 121],
    #[121, 58, 104, 121, 14, 120],
    #[122, 19, 51, 122, 63, 28],
    #[123, 79, 90, 123, 80, 66],
    #[124, 80, 44, 124, 79, 67],
    #[125, 30, 88, 125, 81, 109],
    #[126, 100, 86, 126, 52, 108],
    #[127, 101, 66, 127, 53, 90]] : Array (Array ℕ)).getD k.val #[]).getD j.val 0)
set_option maxHeartbeats 1600000 in
private theorem cert35_1 : ∃ c, c ∈ Subgroup.centralizer (Subgroup.closure (Set.range e35_1) : Set SylowModel) ∧ c ∉ Subgroup.closure (Set.range e35_1) := by
  refine ⟨root 2 * root 6 * root 7, centralizes_generators e35_1 _ (by decide +kernel), ?_⟩
  exact outside_of_table e35_1 a35_1 0 next35_1 prev35_1
    (by decide +kernel) (by decide +kernel) (by decide +kernel) _ (by decide +kernel)

private def e35_2 : Fin 6 → SylowModel := ![decode 400, decode 0, decode 288, decode 144, decode 2320, decode 96]
set_option maxHeartbeats 1600000 in
private theorem edgeEq35_2 : binaryFamily s35 (s35 1) (![false, true, false]) = e35_2 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert35_2 : Subgroup.closure (Set.range e35_2) ≤ character.ker := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨j, rfl⟩
  exact (show ∀ j, e35_2 j ∈ character.ker from by decide +kernel) j

private def e35_3 : Fin 6 → SylowModel := ![decode 0, decode 1176, decode 288, decode 0, decode 1432, decode 800]
set_option maxHeartbeats 1600000 in
private theorem edgeEq35_3 : binaryFamily s35 (s35 0) (![true, true, false]) = e35_3 := by decide +kernel
private def a35_3 (k : Fin 128) : SylowModel :=
  decode ((#[0, 64, 384, 768, 512, 2448, 224, 448, 832, 576, 640, 896, 256, 2256, 2064, 2704, 2960, 160, 352, 992, 736, 704, 960, 320, 128, 3080, 1176, 2544, 2384, 3024, 2768, 2832, 2576, 2192, 288, 928, 672, 608, 864, 480, 192, 3784, 3208, 3848, 3592, 1880, 1048, 1944, 1688, 2224, 2160, 2800, 3056, 2640, 2896, 2512, 2320, 544, 800, 416, 96, 3752, 3656, 3528, 3272, 3976, 3720, 3336, 1976, 2008, 1112, 1368, 1816, 1560, 1432, 2352, 2992, 2736, 2928, 2672, 2288, 2128, 32, 3176, 3624, 3496, 3240, 3400, 3144, 4040, 3464, 1144, 1848, 1208, 1464, 1240, 1496, 1624, 1304, 2608, 2864, 2480, 2416, 3304, 3944, 3688, 3368, 3112, 4008, 3912, 1272, 1912, 1656, 1080, 1336, 1720, 1752, 2096, 4072, 3816, 3432, 3880, 2040, 1784, 1400, 1592, 3560, 1528] : Array ℕ).getD k.val 0)
private def next35_3 (k : Fin 128) (j : Fin 6) : Fin 128 :=
  Fin.ofNat 128 (((#[#[0, 26, 34, 0, 74, 58],
    #[1, 116, 18, 1, 69, 38],
    #[2, 98, 17, 2, 46, 36],
    #[3, 47, 57, 3, 48, 82],
    #[4, 48, 58, 4, 47, 34],
    #[5, 67, 100, 5, 25, 75],
    #[6, 91, 7, 6, 124, 22],
    #[7, 45, 6, 7, 97, 20],
    #[8, 96, 37, 8, 95, 60],
    #[9, 95, 38, 9, 96, 18],
    #[10, 73, 35, 10, 72, 59],
    #[11, 72, 36, 11, 73, 17],
    #[12, 74, 82, 12, 26, 57],
    #[13, 62, 79, 13, 109, 50],
    #[14, 42, 77, 14, 90, 49],
    #[15, 44, 117, 15, 43, 99],
    #[16, 43, 75, 16, 44, 100],
    #[17, 125, 2, 17, 92, 11],
    #[18, 127, 1, 18, 110, 9],
    #[19, 111, 21, 19, 112, 40],
    #[20, 112, 22, 20, 111, 7],
    #[21, 70, 19, 21, 71, 39],
    #[22, 71, 20, 22, 70, 6],
    #[23, 69, 60, 23, 116, 37],
    #[24, 46, 59, 24, 98, 35],
    #[25, 24, 103, 25, 2, 119],
    #[26, 14, 123, 26, 56, 110],
    #[27, 120, 54, 27, 83, 28],
    #[28, 89, 52, 28, 41, 27],
    #[29, 87, 102, 29, 88, 78],
    #[30, 88, 50, 30, 87, 79],
    #[31, 65, 101, 31, 66, 76],
    #[32, 66, 49, 32, 65, 77],
    #[33, 25, 99, 33, 67, 117],
    #[34, 68, 0, 34, 115, 4],
    #[35, 114, 10, 35, 113, 24],
    #[36, 113, 11, 36, 114, 2],
    #[37, 123, 8, 37, 122, 23],
    #[38, 122, 9, 38, 123, 1],
    #[39, 124, 40, 39, 91, 21],
    #[40, 97, 39, 40, 45, 19],
    #[41, 1, 84, 41, 23, 107],
    #[42, 0, 83, 42, 12, 105],
    #[43, 11, 118, 43, 10, 126],
    #[44, 10, 119, 44, 11, 103],
    #[45, 55, 114, 45, 13, 92],
    #[46, 33, 112, 46, 5, 91],
    #[47, 31, 127, 47, 32, 122],
    #[48, 32, 110, 48, 31, 123],
    #[49, 84, 32, 49, 121, 14],
    #[50, 103, 30, 50, 126, 13],
    #[51, 105, 81, 51, 104, 53],
    #[52, 104, 28, 52, 105, 54],
    #[53, 64, 80, 53, 63, 51],
    #[54, 63, 27, 54, 64, 52],
    #[55, 109, 78, 55, 62, 102],
    #[56, 90, 76, 56, 42, 101],
    #[57, 93, 3, 57, 94, 12],
    #[58, 94, 4, 58, 93, 0],
    #[59, 92, 24, 59, 125, 10],
    #[60, 110, 23, 60, 127, 8],
    #[61, 57, 62, 61, 58, 88],
    #[62, 40, 61, 62, 7, 86],
    #[63, 8, 106, 63, 9, 121],
    #[64, 9, 107, 64, 8, 84],
    #[65, 3, 104, 65, 4, 120],
    #[66, 4, 105, 66, 3, 83],
    #[67, 2, 126, 67, 24, 118],
    #[68, 100, 96, 68, 99, 69],
    #[69, 28, 94, 69, 81, 68],
    #[70, 30, 125, 70, 29, 113],
    #[71, 29, 92, 71, 30, 114],
    #[72, 16, 124, 72, 15, 111],
    #[73, 15, 91, 73, 16, 112],
    #[74, 56, 122, 74, 14, 127],
    #[75, 108, 16, 75, 61, 5],
    #[76, 106, 56, 76, 107, 31],
    #[77, 107, 14, 77, 106, 32],
    #[78, 118, 55, 78, 119, 29],
    #[79, 119, 13, 79, 118, 30],
    #[80, 83, 53, 80, 120, 81],
    #[81, 41, 51, 81, 89, 80],
    #[82, 115, 12, 82, 68, 3],
    #[83, 20, 42, 83, 19, 66],
    #[84, 36, 41, 84, 35, 64],
    #[85, 34, 87, 85, 82, 109],
    #[86, 82, 88, 86, 34, 62],
    #[87, 22, 85, 87, 21, 108],
    #[88, 21, 86, 88, 22, 61],
    #[89, 23, 121, 89, 1, 106],
    #[90, 12, 120, 90, 0, 104],
    #[91, 51, 73, 91, 52, 46],
    #[92, 76, 71, 92, 77, 45],
    #[93, 117, 116, 93, 75, 95],
    #[94, 75, 69, 94, 117, 96],
    #[95, 53, 115, 95, 54, 93],
    #[96, 54, 68, 96, 53, 94],
    #[97, 13, 113, 97, 55, 125],
    #[98, 5, 111, 98, 33, 124],
    #[99, 86, 33, 99, 85, 15],
    #[100, 85, 5, 100, 86, 16],
    #[101, 121, 31, 101, 84, 56],
    #[102, 126, 29, 102, 103, 55],
    #[103, 37, 25, 103, 38, 44],
    #[104, 39, 65, 104, 6, 90],
    #[105, 6, 66, 105, 39, 42],
    #[106, 59, 63, 106, 17, 89],
    #[107, 17, 64, 107, 59, 41],
    #[108, 58, 109, 108, 57, 87],
    #[109, 7, 108, 109, 40, 85],
    #[110, 79, 48, 110, 78, 26],
    #[111, 27, 98, 111, 80, 72],
    #[112, 80, 46, 112, 27, 73],
    #[113, 49, 97, 113, 101, 70],
    #[114, 101, 45, 114, 49, 71],
    #[115, 99, 95, 115, 100, 116],
    #[116, 81, 93, 116, 28, 115],
    #[117, 61, 15, 117, 108, 33],
    #[118, 18, 43, 118, 60, 67],
    #[119, 60, 44, 119, 18, 25],
    #[120, 19, 90, 120, 20, 65],
    #[121, 35, 89, 121, 36, 63],
    #[122, 102, 74, 122, 50, 47],
    #[123, 50, 26, 123, 102, 48],
    #[124, 52, 72, 124, 51, 98],
    #[125, 77, 70, 125, 76, 97],
    #[126, 38, 67, 126, 37, 43],
    #[127, 78, 47, 127, 79, 74]] : Array (Array ℕ)).getD k.val #[]).getD j.val 0)
private def prev35_3 (k : Fin 128) (j : Fin 6) : Fin 128 :=
  Fin.ofNat 128 (((#[#[0, 42, 34, 0, 90, 58],
    #[1, 41, 18, 1, 89, 38],
    #[2, 67, 17, 2, 25, 36],
    #[3, 65, 57, 3, 66, 82],
    #[4, 66, 58, 4, 65, 34],
    #[5, 98, 100, 5, 46, 75],
    #[6, 105, 7, 6, 104, 22],
    #[7, 109, 6, 7, 62, 20],
    #[8, 63, 37, 8, 64, 60],
    #[9, 64, 38, 9, 63, 18],
    #[10, 44, 35, 10, 43, 59],
    #[11, 43, 36, 11, 44, 17],
    #[12, 90, 82, 12, 42, 57],
    #[13, 97, 79, 13, 45, 50],
    #[14, 26, 77, 14, 74, 49],
    #[15, 73, 117, 15, 72, 99],
    #[16, 72, 75, 16, 73, 100],
    #[17, 107, 2, 17, 106, 11],
    #[18, 118, 1, 18, 119, 9],
    #[19, 120, 21, 19, 83, 40],
    #[20, 83, 22, 20, 120, 7],
    #[21, 88, 19, 21, 87, 39],
    #[22, 87, 20, 22, 88, 6],
    #[23, 89, 60, 23, 41, 37],
    #[24, 25, 59, 24, 67, 35],
    #[25, 33, 103, 25, 5, 119],
    #[26, 0, 123, 26, 12, 110],
    #[27, 111, 54, 27, 112, 28],
    #[28, 69, 52, 28, 116, 27],
    #[29, 71, 102, 29, 70, 78],
    #[30, 70, 50, 30, 71, 79],
    #[31, 47, 101, 31, 48, 76],
    #[32, 48, 49, 32, 47, 77],
    #[33, 46, 99, 33, 98, 117],
    #[34, 85, 0, 34, 86, 4],
    #[35, 121, 10, 35, 84, 24],
    #[36, 84, 11, 36, 121, 2],
    #[37, 103, 8, 37, 126, 23],
    #[38, 126, 9, 38, 103, 1],
    #[39, 104, 40, 39, 105, 21],
    #[40, 62, 39, 40, 109, 19],
    #[41, 81, 84, 41, 28, 107],
    #[42, 14, 83, 42, 56, 105],
    #[43, 16, 118, 43, 15, 126],
    #[44, 15, 119, 44, 16, 103],
    #[45, 7, 114, 45, 40, 92],
    #[46, 24, 112, 46, 2, 91],
    #[47, 3, 127, 47, 4, 122],
    #[48, 4, 110, 48, 3, 123],
    #[49, 113, 32, 49, 114, 14],
    #[50, 123, 30, 50, 122, 13],
    #[51, 91, 81, 51, 124, 53],
    #[52, 124, 28, 52, 91, 54],
    #[53, 95, 80, 53, 96, 51],
    #[54, 96, 27, 54, 95, 52],
    #[55, 45, 78, 55, 97, 102],
    #[56, 74, 76, 56, 26, 101],
    #[57, 61, 3, 57, 108, 12],
    #[58, 108, 4, 58, 61, 0],
    #[59, 106, 24, 59, 107, 10],
    #[60, 119, 23, 60, 118, 8],
    #[61, 117, 62, 61, 75, 88],
    #[62, 13, 61, 62, 55, 86],
    #[63, 54, 106, 63, 53, 121],
    #[64, 53, 107, 64, 54, 84],
    #[65, 31, 104, 65, 32, 120],
    #[66, 32, 105, 66, 31, 83],
    #[67, 5, 126, 67, 33, 118],
    #[68, 34, 96, 68, 82, 69],
    #[69, 23, 94, 69, 1, 68],
    #[70, 21, 125, 70, 22, 113],
    #[71, 22, 92, 71, 21, 114],
    #[72, 11, 124, 72, 10, 111],
    #[73, 10, 91, 73, 11, 112],
    #[74, 12, 122, 74, 0, 127],
    #[75, 94, 16, 75, 93, 5],
    #[76, 92, 56, 76, 125, 31],
    #[77, 125, 14, 77, 92, 32],
    #[78, 127, 55, 78, 110, 29],
    #[79, 110, 13, 79, 127, 30],
    #[80, 112, 53, 80, 111, 81],
    #[81, 116, 51, 81, 69, 80],
    #[82, 86, 12, 82, 85, 3],
    #[83, 80, 42, 83, 27, 66],
    #[84, 49, 41, 84, 101, 64],
    #[85, 100, 87, 85, 99, 109],
    #[86, 99, 88, 86, 100, 62],
    #[87, 29, 85, 87, 30, 108],
    #[88, 30, 86, 88, 29, 61],
    #[89, 28, 121, 89, 81, 106],
    #[90, 56, 120, 90, 14, 104],
    #[91, 6, 73, 91, 39, 46],
    #[92, 59, 71, 92, 17, 45],
    #[93, 57, 116, 93, 58, 95],
    #[94, 58, 69, 94, 57, 96],
    #[95, 9, 115, 95, 8, 93],
    #[96, 8, 68, 96, 9, 94],
    #[97, 40, 113, 97, 7, 125],
    #[98, 2, 111, 98, 24, 124],
    #[99, 115, 33, 99, 68, 15],
    #[100, 68, 5, 100, 115, 16],
    #[101, 114, 31, 101, 113, 56],
    #[102, 122, 29, 102, 123, 55],
    #[103, 50, 25, 103, 102, 44],
    #[104, 52, 65, 104, 51, 90],
    #[105, 51, 66, 105, 52, 42],
    #[106, 76, 63, 106, 77, 89],
    #[107, 77, 64, 107, 76, 41],
    #[108, 75, 109, 108, 117, 87],
    #[109, 55, 108, 109, 13, 85],
    #[110, 60, 48, 110, 18, 26],
    #[111, 19, 98, 111, 20, 72],
    #[112, 20, 46, 112, 19, 73],
    #[113, 36, 97, 113, 35, 70],
    #[114, 35, 45, 114, 36, 71],
    #[115, 82, 95, 115, 34, 116],
    #[116, 1, 93, 116, 23, 115],
    #[117, 93, 15, 117, 94, 33],
    #[118, 78, 43, 118, 79, 67],
    #[119, 79, 44, 119, 78, 25],
    #[120, 27, 90, 120, 80, 65],
    #[121, 101, 89, 121, 49, 63],
    #[122, 38, 74, 122, 37, 47],
    #[123, 37, 26, 123, 38, 48],
    #[124, 39, 72, 124, 6, 98],
    #[125, 17, 70, 125, 59, 97],
    #[126, 102, 67, 126, 50, 43],
    #[127, 18, 47, 127, 60, 74]] : Array (Array ℕ)).getD k.val #[]).getD j.val 0)
set_option maxHeartbeats 1600000 in
private theorem cert35_3 : ∃ c, c ∈ Subgroup.centralizer (Subgroup.closure (Set.range e35_3) : Set SylowModel) ∧ c ∉ Subgroup.closure (Set.range e35_3) := by
  refine ⟨root 2 * root 6 * root 8, centralizes_generators e35_3 _ (by decide +kernel), ?_⟩
  exact outside_of_table e35_3 a35_3 0 next35_3 prev35_3
    (by decide +kernel) (by decide +kernel) (by decide +kernel) _ (by decide +kernel)

private def e35_4 : Fin 6 → SylowModel := ![decode 400, decode 1032, decode 0, decode 912, decode 1864, decode 0]
set_option maxHeartbeats 1600000 in
private theorem edgeEq35_4 : binaryFamily s35 (s35 2) (![false, false, true]) = e35_4 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert35_4 : Represented smallParityCensusNode (Subgroup.closure (Set.range e35_4)) := by
  refine ⟨69, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node69]
  exact closure_eq_words _ o69 (![[1, 6], [0], [], [1, 4, 6], [0, 3], []]) (![[1], [0, 1, 4, 1, 4], [1, 1], [1, 1, 1, 4], [0, 3], [1, 1, 4, 4], [1, 4, 1, 4]]) (by decide +kernel) (by decide +kernel)

private def e35_5 : Fin 6 → SylowModel := ![decode 0, decode 1032, decode 688, decode 0, decode 1288, decode 176]
set_option maxHeartbeats 1600000 in
private theorem edgeEq35_5 : binaryFamily s35 (s35 0) (![true, false, true]) = e35_5 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert35_5 : Represented smallParityCensusNode (Subgroup.closure (Set.range e35_5)) := by
  refine ⟨70, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node70]
  exact closure_eq_words _ o70 (![[], [0], [1, 6], [], [0, 6], [1, 4, 6]]) (![[1], [1, 1, 1, 4, 2], [1, 1], [1, 1, 1, 2, 4, 5], [2, 2], [1, 1, 2, 1, 1, 5], [1, 1, 1, 4]]) (by decide +kernel) (by decide +kernel)

private def e35_6 : Fin 6 → SylowModel := ![decode 400, decode 0, decode 3640, decode 144, decode 2320, decode 1640]
set_option maxHeartbeats 1600000 in
private theorem edgeEq35_6 : binaryFamily s35 (s35 1) (![false, true, true]) = e35_6 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert35_6 : Represented smallParityCensusNode (Subgroup.closure (Set.range e35_6)) := by
  refine ⟨71, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node71]
  exact closure_eq_words _ o71 (![[1, 6], [], [0, 3, 2], [1], [2], [0]]) (![[5], [3], [4], [2, 2, 4], [0, 2, 3, 5], [2, 4, 5, 4], [0, 3]]) (by decide +kernel) (by decide +kernel)

private def e35_7 : Fin 6 → SylowModel := ![decode 0, decode 1176, decode 688, decode 0, decode 1432, decode 176]
set_option maxHeartbeats 1600000 in
private theorem edgeEq35_7 : binaryFamily s35 (s35 0) (![true, true, true]) = e35_7 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert35_7 : Represented smallParityCensusNode (Subgroup.closure (Set.range e35_7)) := by
  refine ⟨70, root 2 * root 3 * root 4 * root 7, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node70]
  exact closure_eq_words _ o70 (![[], [0, 6], [1, 4], [], [0], [1]]) (![[4], [5], [1, 1], [1, 1, 1, 2, 4, 5], [2, 2], [1, 1, 2, 1, 1, 5], [1, 1, 1, 4]]) (by decide +kernel) (by decide +kernel)

private def s36 : Fin 3 → SylowModel := ![root 2 * root 3 * root 4 * root 7, root 6, rootOne ^ 3 * root 3 * root 4]
set_option maxHeartbeats 1600000 in
private theorem gen36 : Subgroup.closure (Set.range s36) = smallParityCensusNode 36 := by
  rw [node36]
  exact closure_eq_words s36 o36 (![[1, 6], [4, 5], [0]]) (![[2], [1, 0, 1], [2, 2], [0, 0, 0, 2, 2, 2, 0, 2], [2, 1, 2, 2, 2], [1, 2, 1, 2, 2, 2], [0, 0, 0, 1, 0, 1], [1, 2, 2, 1, 2, 2]]) (by decide +kernel) (by decide +kernel)

private def e36_1 : Fin 6 → SylowModel := ![decode 0, decode 64, decode 1032, decode 640, decode 576, decode 1176]
set_option maxHeartbeats 1600000 in
private theorem edgeEq36_1 : binaryFamily s36 (s36 0) (![true, false, false]) = e36_1 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert36_1 : Represented smallParityCensusNode (Subgroup.closure (Set.range e36_1)) := by
  refine ⟨69, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node69]
  exact closure_eq_words _ o69 (![[], [3, 5], [0], [4, 5, 6], [3, 4, 5], [1, 0]]) (![[2], [2, 2, 5, 2], [2, 2], [2, 1, 2, 2, 2], [1, 4], [1, 2, 1, 2, 2, 2], [2, 2, 5, 5]]) (by decide +kernel) (by decide +kernel)

private def e36_2 : Fin 6 → SylowModel := ![decode 156, decode 0, decode 1032, decode 668, decode 0, decode 1416]
set_option maxHeartbeats 1600000 in
private theorem edgeEq36_2 : binaryFamily s36 (s36 1) (![false, true, false]) = e36_2 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert36_2 : Represented smallParityCensusNode (Subgroup.closure (Set.range e36_2)) := by
  refine ⟨72, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node72]
  exact closure_eq_words _ o72 (![[1, 5, 6], [], [0], [1], [], [4, 0, 5]]) (![[2], [3], [2, 2], [0, 2, 2, 2, 3, 5], [0, 0], [0, 0, 2, 2, 5, 2], [2, 2, 5, 5]]) (by decide +kernel) (by decide +kernel)

private def e36_3 : Fin 6 → SylowModel := ![decode 0, decode 92, decode 1032, decode 640, decode 220, decode 1176]
set_option maxHeartbeats 1600000 in
private theorem edgeEq36_3 : binaryFamily s36 (s36 0) (![true, true, false]) = e36_3 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert36_3 : Represented smallParityCensusNode (Subgroup.closure (Set.range e36_3)) := by
  refine ⟨72, root 1 * root 2 * root 4 * root 6 * root 7 * root 9, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node72]
  exact closure_eq_words _ o72 (![[], [1, 4, 5], [1, 0], [4, 5, 6], [1, 5], [4, 0, 1]]) (![[4, 2, 3], [1, 2, 2, 2, 3, 2], [2, 5], [1, 1, 2, 2, 5, 2], [1, 1], [1, 1, 2, 2, 2, 3, 2], [2, 2, 5, 5]]) (by decide +kernel) (by decide +kernel)

private def e36_4 : Fin 6 → SylowModel := ![decode 156, decode 64, decode 0, decode 268, decode 448, decode 2320]
set_option maxHeartbeats 1600000 in
private theorem edgeEq36_4 : binaryFamily s36 (s36 2) (![false, false, true]) = e36_4 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert36_4 : Subgroup.closure (Set.range e36_4) ≤ character.ker := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨j, rfl⟩
  exact (show ∀ j, e36_4 j ∈ character.ker from by decide +kernel) j

private def e36_5 : Fin 6 → SylowModel := ![decode 0, decode 64, decode 1924, decode 640, decode 576, decode 1428]
set_option maxHeartbeats 1600000 in
private theorem edgeEq36_5 : binaryFamily s36 (s36 0) (![true, false, true]) = e36_5 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert36_5 : Represented smallParityCensusNode (Subgroup.closure (Set.range e36_5)) := by
  refine ⟨69, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node69]
  exact closure_eq_words _ o69 (![[], [3, 4, 5], [0, 4], [5, 6], [3, 5], [1, 0, 4]]) (![[1, 4, 2], [2, 2, 5, 2], [2, 2], [2, 2, 5, 4, 5], [1, 4], [2, 2, 2, 3, 2], [2, 2, 5, 5]]) (by decide +kernel) (by decide +kernel)

private def e36_6 : Fin 6 → SylowModel := ![decode 156, decode 0, decode 1992, decode 668, decode 0, decode 1608]
set_option maxHeartbeats 1600000 in
private theorem edgeEq36_6 : binaryFamily s36 (s36 1) (![false, true, true]) = e36_6 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert36_6 : Represented smallParityCensusNode (Subgroup.closure (Set.range e36_6)) := by
  refine ⟨72, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node72]
  exact closure_eq_words _ o72 (![[1, 5, 6], [], [0, 3], [1], [], [1, 0, 1, 5]]) (![[0, 5, 3], [3], [5, 5], [0, 2, 2, 5, 3, 2], [0, 0], [0, 0, 2, 2, 5, 2], [2, 2, 5, 5]]) (by decide +kernel) (by decide +kernel)

private def e36_7 : Fin 6 → SylowModel := ![decode 0, decode 92, decode 1924, decode 640, decode 220, decode 1428]
set_option maxHeartbeats 1600000 in
private theorem edgeEq36_7 : binaryFamily s36 (s36 0) (![true, true, true]) = e36_7 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert36_7 : Represented smallParityCensusNode (Subgroup.closure (Set.range e36_7)) := by
  refine ⟨72, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node72]
  exact closure_eq_words _ o72 (![[], [1, 4, 5], [0, 5, 6], [4, 5, 6], [1, 5], [0, 3, 5]]) (![[1, 1, 3, 2], [1, 2, 2, 2, 3, 2], [2, 2], [2, 2, 5, 2], [1, 1], [1, 1, 2, 2, 2, 3, 2], [2, 2, 5, 5]]) (by decide +kernel) (by decide +kernel)

private def s37 : Fin 3 → SylowModel := ![root 6, rootOne ^ 3 * root 3 * root 4, root 2 * root 3 * root 4 * root 5 * root 7 * root 8]
set_option maxHeartbeats 1600000 in
private theorem gen37 : Subgroup.closure (Set.range s37) = smallParityCensusNode 37 := by
  rw [node37]
  exact closure_eq_words s37 o37 (![[4, 5], [0], [1]]) (![[1], [2], [1, 1], [1, 1, 1, 2, 1, 0, 2], [1, 0, 1, 1, 1], [0, 1, 0, 1, 1, 1], [0, 2, 0, 2, 2, 2], [0, 1, 1, 0, 1, 1]]) (by decide +kernel) (by decide +kernel)

private def e37_1 : Fin 6 → SylowModel := ![decode 0, decode 1032, decode 444, decode 0, decode 1416, decode 956]
set_option maxHeartbeats 1600000 in
private theorem edgeEq37_1 : binaryFamily s37 (s37 0) (![true, false, false]) = e37_1 := by decide +kernel
private def a37_1 (k : Fin 128) : SylowModel :=
  decode ((#[0, 384, 768, 512, 2172, 2448, 2368, 364, 700, 464, 640, 896, 256, 1032, 2556, 2940, 2684, 2064, 2704, 2960, 2240, 2624, 2880, 236, 620, 876, 828, 444, 188, 80, 720, 976, 128, 1160, 1800, 1544, 2732, 2812, 3068, 2428, 2832, 2576, 2192, 3008, 2752, 2112, 1004, 748, 108, 60, 316, 956, 848, 592, 208, 3364, 3224, 3784, 1076, 1380, 1880, 1928, 1672, 1288, 2860, 2476, 2220, 2300, 2320, 2496, 492, 572, 336, 3492, 3620, 3876, 3096, 3992, 3736, 3656, 3528, 3272, 1204, 1844, 1588, 1508, 1636, 1892, 2008, 1112, 1368, 1416, 2092, 2348, 2988, 3444, 3748, 4004, 3108, 3864, 3608, 3480, 3400, 3144, 4040, 1972, 1716, 1332, 1764, 2020, 1124, 1240, 1496, 1624, 2604, 3572, 3700, 3956, 3236, 3352, 3912, 1460, 1252, 1752, 3828, 4084, 3188, 3316] : Array ℕ).getD k.val 0)
private def next37_1 (k : Fin 128) (j : Fin 6) : Fin 128 :=
  Fin.ofNat 128 (((#[#[0, 13, 27, 0, 91, 51],
    #[1, 91, 49, 1, 13, 71],
    #[2, 34, 8, 2, 62, 28],
    #[3, 35, 51, 3, 61, 27],
    #[4, 117, 20, 4, 124, 44],
    #[5, 101, 36, 5, 76, 66],
    #[6, 120, 39, 6, 57, 15],
    #[7, 86, 52, 7, 109, 72],
    #[8, 105, 11, 8, 84, 1],
    #[9, 88, 25, 9, 113, 7],
    #[10, 62, 26, 10, 34, 50],
    #[11, 61, 71, 11, 35, 49],
    #[12, 63, 28, 12, 33, 8],
    #[13, 68, 86, 13, 5, 110],
    #[14, 124, 6, 14, 117, 22],
    #[15, 126, 43, 15, 115, 69],
    #[16, 95, 44, 16, 127, 20],
    #[17, 76, 64, 17, 101, 93],
    #[18, 78, 65, 18, 99, 94],
    #[19, 77, 66, 19, 100, 36],
    #[20, 57, 67, 20, 120, 37],
    #[21, 103, 16, 21, 80, 4],
    #[22, 102, 15, 22, 81, 39],
    #[23, 109, 30, 23, 86, 54],
    #[24, 59, 29, 24, 122, 53],
    #[25, 110, 72, 25, 85, 52],
    #[26, 84, 3, 26, 105, 0],
    #[27, 82, 32, 27, 107, 10],
    #[28, 121, 1, 28, 58, 11],
    #[29, 113, 47, 29, 88, 23],
    #[30, 111, 48, 30, 90, 24],
    #[31, 112, 7, 31, 89, 25],
    #[32, 33, 50, 32, 63, 26],
    #[33, 5, 108, 33, 68, 122],
    #[34, 41, 59, 34, 18, 87],
    #[35, 40, 110, 35, 19, 86],
    #[36, 97, 68, 36, 74, 40],
    #[37, 115, 21, 37, 126, 45],
    #[38, 127, 22, 38, 95, 6],
    #[39, 116, 69, 39, 125, 43],
    #[40, 99, 92, 40, 78, 114],
    #[41, 100, 93, 41, 77, 64],
    #[42, 56, 94, 42, 119, 65],
    #[43, 80, 38, 43, 103, 14],
    #[44, 81, 37, 44, 102, 67],
    #[45, 79, 4, 45, 104, 16],
    #[46, 122, 9, 46, 59, 31],
    #[47, 85, 54, 47, 110, 30],
    #[48, 87, 53, 48, 108, 29],
    #[49, 107, 12, 49, 82, 2],
    #[50, 58, 0, 50, 121, 3],
    #[51, 106, 10, 51, 83, 32],
    #[52, 90, 70, 52, 111, 46],
    #[53, 89, 23, 53, 112, 47],
    #[54, 123, 24, 54, 60, 48],
    #[55, 26, 79, 55, 51, 103],
    #[56, 1, 95, 56, 12, 117],
    #[57, 9, 98, 57, 72, 74],
    #[58, 114, 111, 58, 36, 123],
    #[59, 39, 62, 59, 14, 33],
    #[60, 45, 84, 60, 20, 58],
    #[61, 18, 85, 61, 41, 109],
    #[62, 19, 122, 62, 40, 108],
    #[63, 17, 87, 63, 42, 59],
    #[64, 74, 42, 64, 97, 18],
    #[65, 118, 41, 65, 55, 17],
    #[66, 73, 40, 66, 98, 68],
    #[67, 125, 45, 67, 116, 21],
    #[68, 119, 114, 68, 56, 92],
    #[69, 104, 14, 69, 79, 38],
    #[70, 108, 31, 70, 87, 9],
    #[71, 83, 2, 71, 106, 12],
    #[72, 60, 46, 72, 123, 70],
    #[73, 51, 57, 73, 26, 81],
    #[74, 49, 102, 74, 28, 120],
    #[75, 50, 103, 75, 27, 79],
    #[76, 12, 115, 76, 1, 125],
    #[77, 10, 116, 77, 3, 126],
    #[78, 11, 117, 78, 2, 95],
    #[79, 72, 118, 79, 9, 96],
    #[80, 30, 75, 80, 53, 55],
    #[81, 31, 74, 81, 52, 98],
    #[82, 36, 89, 82, 114, 113],
    #[83, 93, 88, 83, 65, 112],
    #[84, 92, 123, 84, 66, 111],
    #[85, 14, 35, 85, 39, 13],
    #[86, 16, 91, 86, 37, 61],
    #[87, 15, 33, 87, 38, 62],
    #[88, 20, 106, 88, 45, 82],
    #[89, 22, 107, 89, 43, 83],
    #[90, 21, 58, 90, 44, 84],
    #[91, 42, 109, 91, 17, 85],
    #[92, 55, 19, 92, 118, 5],
    #[93, 98, 18, 93, 73, 42],
    #[94, 96, 17, 94, 75, 41],
    #[95, 7, 119, 95, 70, 99],
    #[96, 28, 80, 96, 49, 104],
    #[97, 27, 81, 97, 50, 57],
    #[98, 71, 120, 98, 8, 102],
    #[99, 3, 124, 99, 10, 127],
    #[100, 2, 125, 100, 11, 115],
    #[101, 32, 126, 101, 0, 116],
    #[102, 53, 97, 102, 30, 73],
    #[103, 52, 96, 103, 31, 118],
    #[104, 54, 55, 104, 29, 75],
    #[105, 65, 60, 105, 93, 90],
    #[106, 66, 113, 106, 92, 89],
    #[107, 64, 112, 107, 94, 88],
    #[108, 37, 63, 108, 16, 34],
    #[109, 38, 13, 109, 15, 35],
    #[110, 4, 61, 110, 67, 91],
    #[111, 43, 121, 111, 22, 105],
    #[112, 44, 82, 112, 21, 106],
    #[113, 6, 83, 113, 69, 107],
    #[114, 75, 5, 114, 96, 19],
    #[115, 70, 101, 115, 7, 77],
    #[116, 24, 100, 116, 47, 76],
    #[117, 25, 99, 117, 46, 119],
    #[118, 8, 104, 118, 71, 80],
    #[119, 0, 127, 119, 32, 124],
    #[120, 29, 73, 120, 54, 97],
    #[121, 94, 90, 121, 64, 60],
    #[122, 67, 34, 122, 4, 63],
    #[123, 69, 105, 123, 6, 121],
    #[124, 47, 78, 124, 24, 56],
    #[125, 46, 77, 125, 25, 101],
    #[126, 48, 76, 126, 23, 100],
    #[127, 23, 56, 127, 48, 78]] : Array (Array ℕ)).getD k.val #[]).getD j.val 0)
private def prev37_1 (k : Fin 128) (j : Fin 6) : Fin 128 :=
  Fin.ofNat 128 (((#[#[0, 119, 50, 0, 101, 26],
    #[1, 56, 28, 1, 76, 8],
    #[2, 100, 71, 2, 78, 49],
    #[3, 99, 26, 3, 77, 50],
    #[4, 110, 45, 4, 122, 21],
    #[5, 33, 114, 5, 13, 92],
    #[6, 113, 14, 6, 123, 38],
    #[7, 95, 31, 7, 115, 9],
    #[8, 118, 2, 8, 98, 12],
    #[9, 57, 46, 9, 79, 70],
    #[10, 77, 51, 10, 99, 27],
    #[11, 78, 8, 11, 100, 28],
    #[12, 76, 49, 12, 56, 71],
    #[13, 0, 109, 13, 1, 85],
    #[14, 85, 69, 14, 59, 43],
    #[15, 87, 22, 15, 109, 6],
    #[16, 86, 21, 16, 108, 45],
    #[17, 63, 94, 17, 91, 65],
    #[18, 61, 93, 18, 34, 64],
    #[19, 62, 92, 19, 35, 114],
    #[20, 88, 4, 20, 60, 16],
    #[21, 90, 37, 21, 112, 67],
    #[22, 89, 38, 22, 111, 14],
    #[23, 127, 53, 23, 126, 29],
    #[24, 116, 54, 24, 124, 30],
    #[25, 117, 9, 25, 125, 31],
    #[26, 55, 10, 26, 73, 32],
    #[27, 97, 0, 27, 75, 3],
    #[28, 96, 12, 28, 74, 2],
    #[29, 120, 24, 29, 104, 48],
    #[30, 80, 23, 30, 102, 47],
    #[31, 81, 70, 31, 103, 46],
    #[32, 101, 27, 32, 119, 51],
    #[33, 32, 87, 33, 12, 59],
    #[34, 2, 122, 34, 10, 108],
    #[35, 3, 85, 35, 11, 109],
    #[36, 82, 5, 36, 58, 19],
    #[37, 108, 44, 37, 86, 20],
    #[38, 109, 43, 38, 87, 69],
    #[39, 59, 6, 39, 85, 22],
    #[40, 35, 66, 40, 62, 36],
    #[41, 34, 65, 41, 61, 94],
    #[42, 91, 64, 42, 63, 93],
    #[43, 111, 15, 43, 89, 39],
    #[44, 112, 16, 44, 90, 4],
    #[45, 60, 67, 45, 88, 37],
    #[46, 125, 72, 46, 117, 52],
    #[47, 124, 29, 47, 116, 53],
    #[48, 126, 30, 48, 127, 54],
    #[49, 74, 1, 49, 96, 11],
    #[50, 75, 32, 50, 97, 10],
    #[51, 73, 3, 51, 55, 0],
    #[52, 103, 7, 52, 81, 25],
    #[53, 102, 48, 53, 80, 24],
    #[54, 104, 47, 54, 120, 23],
    #[55, 92, 104, 55, 65, 80],
    #[56, 42, 127, 56, 68, 124],
    #[57, 20, 73, 57, 6, 97],
    #[58, 50, 90, 58, 28, 60],
    #[59, 24, 34, 59, 46, 63],
    #[60, 72, 105, 60, 54, 121],
    #[61, 11, 110, 61, 3, 86],
    #[62, 10, 59, 62, 2, 87],
    #[63, 12, 108, 63, 32, 122],
    #[64, 107, 17, 64, 121, 41],
    #[65, 105, 18, 65, 83, 42],
    #[66, 106, 19, 66, 84, 5],
    #[67, 122, 20, 67, 110, 44],
    #[68, 13, 36, 68, 33, 66],
    #[69, 123, 39, 69, 113, 15],
    #[70, 115, 52, 70, 95, 72],
    #[71, 98, 11, 71, 118, 1],
    #[72, 79, 25, 72, 57, 7],
    #[73, 66, 120, 73, 93, 102],
    #[74, 64, 81, 74, 36, 57],
    #[75, 114, 80, 75, 94, 104],
    #[76, 17, 126, 76, 5, 116],
    #[77, 19, 125, 77, 41, 115],
    #[78, 18, 124, 78, 40, 127],
    #[79, 45, 55, 79, 69, 75],
    #[80, 43, 96, 80, 21, 118],
    #[81, 44, 97, 81, 22, 73],
    #[82, 27, 112, 82, 49, 88],
    #[83, 71, 113, 83, 51, 89],
    #[84, 26, 60, 84, 8, 90],
    #[85, 47, 61, 85, 25, 91],
    #[86, 7, 13, 86, 23, 35],
    #[87, 48, 63, 87, 70, 34],
    #[88, 9, 83, 88, 29, 107],
    #[89, 53, 82, 89, 31, 106],
    #[90, 52, 121, 90, 30, 105],
    #[91, 1, 86, 91, 0, 110],
    #[92, 84, 40, 92, 106, 68],
    #[93, 83, 41, 93, 105, 17],
    #[94, 121, 42, 94, 107, 18],
    #[95, 16, 56, 95, 38, 78],
    #[96, 94, 103, 96, 114, 79],
    #[97, 36, 102, 97, 64, 120],
    #[98, 93, 57, 98, 66, 81],
    #[99, 40, 117, 99, 18, 95],
    #[100, 41, 116, 100, 19, 126],
    #[101, 5, 115, 101, 17, 125],
    #[102, 22, 74, 102, 44, 98],
    #[103, 21, 75, 103, 43, 55],
    #[104, 69, 118, 104, 45, 96],
    #[105, 8, 123, 105, 26, 111],
    #[106, 51, 88, 106, 71, 112],
    #[107, 49, 89, 107, 27, 113],
    #[108, 70, 33, 108, 48, 62],
    #[109, 23, 91, 109, 7, 61],
    #[110, 25, 35, 110, 47, 13],
    #[111, 30, 58, 111, 52, 84],
    #[112, 31, 107, 112, 53, 83],
    #[113, 29, 106, 113, 9, 82],
    #[114, 58, 68, 114, 82, 40],
    #[115, 37, 76, 115, 15, 100],
    #[116, 39, 77, 116, 67, 101],
    #[117, 4, 78, 117, 14, 56],
    #[118, 65, 79, 118, 92, 103],
    #[119, 68, 95, 119, 42, 117],
    #[120, 6, 98, 120, 20, 74],
    #[121, 28, 111, 121, 50, 123],
    #[122, 46, 62, 122, 24, 33],
    #[123, 54, 84, 123, 72, 58],
    #[124, 14, 99, 124, 4, 119],
    #[125, 67, 100, 125, 39, 76],
    #[126, 15, 101, 126, 37, 77],
    #[127, 38, 119, 127, 16, 99]] : Array (Array ℕ)).getD k.val #[]).getD j.val 0)
set_option maxHeartbeats 1600000 in
private theorem cert37_1 : ∃ c, c ∈ Subgroup.centralizer (Subgroup.closure (Set.range e37_1) : Set SylowModel) ∧ c ∉ Subgroup.closure (Set.range e37_1) := by
  refine ⟨rootOne ^ 2 * root 2 * root 6 * root 7, centralizes_generators e37_1 _ (by decide +kernel), ?_⟩
  exact outside_of_table e37_1 a37_1 0 next37_1 prev37_1
    (by decide +kernel) (by decide +kernel) (by decide +kernel) _ (by decide +kernel)

private def e37_2 : Fin 6 → SylowModel := ![decode 64, decode 0, decode 444, decode 448, decode 2320, decode 364]
set_option maxHeartbeats 1600000 in
private theorem edgeEq37_2 : binaryFamily s37 (s37 1) (![false, true, false]) = e37_2 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert37_2 : Subgroup.closure (Set.range e37_2) ≤ character.ker := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨j, rfl⟩
  exact (show ∀ j, e37_2 j ∈ character.ker from by decide +kernel) j

private def e37_3 : Fin 6 → SylowModel := ![decode 0, decode 1992, decode 444, decode 0, decode 1608, decode 956]
set_option maxHeartbeats 1600000 in
private theorem edgeEq37_3 : binaryFamily s37 (s37 0) (![true, true, false]) = e37_3 := by decide +kernel
private def a37_3 (k : Fin 128) : SylowModel :=
  decode ((#[0, 384, 768, 512, 2172, 2448, 2368, 364, 700, 464, 640, 896, 256, 2556, 2940, 2684, 2064, 2704, 2960, 2240, 2624, 2880, 236, 620, 876, 828, 444, 188, 80, 720, 976, 128, 3080, 1700, 1176, 1992, 2732, 2812, 3068, 2428, 2832, 2576, 2192, 3008, 2752, 2112, 1004, 748, 108, 60, 316, 956, 848, 592, 208, 3208, 3848, 3592, 1572, 1444, 1188, 1048, 1944, 1688, 1864, 1224, 1480, 2860, 2476, 2220, 2300, 2320, 2496, 492, 572, 336, 4020, 4068, 3672, 3976, 3720, 3336, 2036, 1316, 1060, 1956, 1816, 1560, 1432, 1096, 1352, 1736, 2092, 2348, 2988, 3892, 3252, 3508, 3940, 3300, 3556, 3800, 3416, 3160, 3464, 1908, 1268, 1524, 1828, 1304, 1608, 2604, 3124, 3380, 3764, 3172, 3428, 3812, 3544, 3288, 3928, 1140, 1396, 1780, 3636, 3684, 4056, 1652] : Array ℕ).getD k.val 0)
private def next37_3 (k : Fin 128) (j : Fin 6) : Fin 128 :=
  Fin.ofNat 128 (((#[#[0, 35, 26, 0, 110, 51],
    #[1, 110, 49, 1, 35, 74],
    #[2, 65, 8, 2, 90, 27],
    #[3, 66, 51, 3, 89, 26],
    #[4, 97, 19, 4, 112, 44],
    #[5, 120, 36, 5, 101, 69],
    #[6, 104, 39, 6, 32, 14],
    #[7, 59, 52, 7, 84, 75],
    #[8, 121, 11, 8, 107, 1],
    #[9, 61, 24, 9, 88, 7],
    #[10, 90, 25, 10, 65, 50],
    #[11, 89, 74, 11, 66, 49],
    #[12, 91, 27, 12, 64, 8],
    #[13, 112, 6, 13, 97, 21],
    #[14, 114, 43, 14, 95, 72],
    #[15, 76, 44, 15, 124, 19],
    #[16, 101, 67, 16, 120, 93],
    #[17, 103, 68, 17, 118, 94],
    #[18, 102, 69, 18, 119, 36],
    #[19, 32, 70, 19, 104, 37],
    #[20, 80, 15, 20, 56, 4],
    #[21, 79, 14, 21, 57, 39],
    #[22, 84, 29, 22, 59, 54],
    #[23, 33, 28, 23, 108, 53],
    #[24, 85, 75, 24, 58, 52],
    #[25, 107, 3, 25, 121, 0],
    #[26, 105, 31, 26, 123, 10],
    #[27, 127, 1, 27, 82, 11],
    #[28, 88, 47, 28, 61, 22],
    #[29, 86, 48, 29, 63, 23],
    #[30, 87, 7, 30, 62, 24],
    #[31, 64, 50, 31, 91, 25],
    #[32, 75, 99, 32, 9, 117],
    #[33, 13, 64, 33, 39, 90],
    #[34, 19, 82, 34, 45, 107],
    #[35, 5, 85, 35, 71, 59],
    #[36, 116, 71, 36, 99, 40],
    #[37, 95, 20, 37, 114, 45],
    #[38, 124, 21, 38, 76, 6],
    #[39, 96, 72, 39, 113, 43],
    #[40, 118, 92, 40, 103, 111],
    #[41, 119, 93, 41, 102, 67],
    #[42, 78, 94, 42, 126, 68],
    #[43, 56, 38, 43, 80, 13],
    #[44, 57, 37, 44, 79, 70],
    #[45, 55, 4, 45, 81, 15],
    #[46, 108, 9, 46, 33, 30],
    #[47, 58, 54, 47, 85, 29],
    #[48, 60, 53, 48, 83, 28],
    #[49, 123, 12, 49, 105, 2],
    #[50, 82, 0, 50, 127, 3],
    #[51, 122, 10, 51, 106, 31],
    #[52, 63, 73, 52, 86, 46],
    #[53, 62, 22, 53, 87, 47],
    #[54, 109, 23, 54, 34, 48],
    #[55, 9, 115, 55, 75, 125],
    #[56, 53, 77, 56, 29, 100],
    #[57, 52, 117, 57, 30, 99],
    #[58, 39, 35, 58, 13, 66],
    #[59, 37, 89, 59, 15, 110],
    #[60, 38, 90, 60, 14, 64],
    #[61, 45, 105, 61, 19, 122],
    #[62, 43, 106, 62, 21, 123],
    #[63, 44, 107, 63, 20, 82],
    #[64, 71, 108, 64, 5, 83],
    #[65, 17, 60, 65, 41, 33],
    #[66, 18, 59, 66, 40, 85],
    #[67, 99, 42, 67, 116, 17],
    #[68, 125, 41, 68, 77, 16],
    #[69, 98, 40, 69, 117, 71],
    #[70, 113, 45, 70, 96, 20],
    #[71, 126, 111, 71, 78, 92],
    #[72, 81, 13, 72, 55, 38],
    #[73, 83, 30, 73, 60, 9],
    #[74, 106, 2, 74, 122, 12],
    #[75, 34, 46, 75, 109, 73],
    #[76, 73, 118, 76, 7, 126],
    #[77, 51, 80, 77, 25, 55],
    #[78, 12, 97, 78, 1, 76],
    #[79, 29, 98, 79, 53, 116],
    #[80, 30, 125, 80, 52, 115],
    #[81, 28, 100, 81, 54, 77],
    #[82, 36, 109, 82, 111, 86],
    #[83, 15, 65, 83, 37, 91],
    #[84, 14, 66, 84, 38, 35],
    #[85, 70, 110, 85, 4, 89],
    #[86, 21, 121, 86, 43, 127],
    #[87, 20, 122, 87, 44, 105],
    #[88, 72, 123, 88, 6, 106],
    #[89, 41, 84, 89, 17, 58],
    #[90, 40, 83, 90, 18, 108],
    #[91, 42, 33, 91, 16, 60],
    #[92, 77, 18, 92, 125, 5],
    #[93, 117, 17, 93, 98, 42],
    #[94, 115, 16, 94, 100, 41],
    #[95, 7, 102, 95, 73, 120],
    #[96, 47, 101, 96, 23, 119],
    #[97, 46, 126, 97, 24, 118],
    #[98, 25, 57, 98, 51, 32],
    #[99, 27, 104, 99, 49, 79],
    #[100, 26, 55, 100, 50, 80],
    #[101, 1, 113, 101, 12, 95],
    #[102, 3, 114, 102, 10, 96],
    #[103, 2, 76, 103, 11, 97],
    #[104, 54, 116, 104, 28, 98],
    #[105, 111, 88, 105, 36, 62],
    #[106, 68, 87, 106, 93, 61],
    #[107, 69, 86, 107, 92, 109],
    #[108, 4, 91, 108, 70, 65],
    #[109, 6, 127, 109, 72, 121],
    #[110, 16, 58, 110, 42, 84],
    #[111, 100, 5, 111, 115, 18],
    #[112, 23, 78, 112, 47, 103],
    #[113, 24, 120, 113, 46, 102],
    #[114, 22, 119, 114, 48, 101],
    #[115, 49, 81, 115, 27, 56],
    #[116, 50, 32, 116, 26, 57],
    #[117, 8, 79, 117, 74, 104],
    #[118, 10, 124, 118, 3, 112],
    #[119, 11, 95, 119, 2, 113],
    #[120, 0, 96, 120, 31, 114],
    #[121, 93, 63, 121, 68, 34],
    #[122, 92, 62, 122, 69, 88],
    #[123, 94, 61, 123, 67, 87],
    #[124, 48, 103, 124, 22, 78],
    #[125, 74, 56, 125, 8, 81],
    #[126, 31, 112, 126, 0, 124],
    #[127, 67, 34, 127, 94, 63]] : Array (Array ℕ)).getD k.val #[]).getD j.val 0)
private def prev37_3 (k : Fin 128) (j : Fin 6) : Fin 128 :=
  Fin.ofNat 128 (((#[#[0, 120, 50, 0, 126, 25],
    #[1, 101, 27, 1, 78, 8],
    #[2, 103, 74, 2, 119, 49],
    #[3, 102, 25, 3, 118, 50],
    #[4, 108, 45, 4, 85, 20],
    #[5, 35, 111, 5, 64, 92],
    #[6, 109, 13, 6, 88, 38],
    #[7, 95, 30, 7, 76, 9],
    #[8, 117, 2, 8, 125, 12],
    #[9, 55, 46, 9, 32, 73],
    #[10, 118, 51, 10, 102, 26],
    #[11, 119, 8, 11, 103, 27],
    #[12, 78, 49, 12, 101, 74],
    #[13, 33, 72, 13, 58, 43],
    #[14, 84, 21, 14, 60, 6],
    #[15, 83, 20, 15, 59, 45],
    #[16, 110, 94, 16, 91, 68],
    #[17, 65, 93, 17, 89, 67],
    #[18, 66, 92, 18, 90, 111],
    #[19, 34, 4, 19, 61, 15],
    #[20, 87, 37, 20, 63, 70],
    #[21, 86, 38, 21, 62, 13],
    #[22, 114, 53, 22, 124, 28],
    #[23, 112, 54, 23, 96, 29],
    #[24, 113, 9, 24, 97, 30],
    #[25, 98, 10, 25, 77, 31],
    #[26, 100, 0, 26, 116, 3],
    #[27, 99, 12, 27, 115, 2],
    #[28, 81, 23, 28, 104, 48],
    #[29, 79, 22, 29, 56, 47],
    #[30, 80, 73, 30, 57, 46],
    #[31, 126, 26, 31, 120, 51],
    #[32, 19, 116, 32, 6, 98],
    #[33, 23, 91, 33, 46, 65],
    #[34, 75, 127, 34, 54, 121],
    #[35, 0, 58, 35, 1, 84],
    #[36, 82, 5, 36, 105, 18],
    #[37, 59, 44, 37, 83, 19],
    #[38, 60, 43, 38, 84, 72],
    #[39, 58, 6, 39, 33, 21],
    #[40, 90, 69, 40, 66, 36],
    #[41, 89, 68, 41, 65, 94],
    #[42, 91, 67, 42, 110, 93],
    #[43, 62, 14, 43, 86, 39],
    #[44, 63, 15, 44, 87, 4],
    #[45, 61, 70, 45, 34, 37],
    #[46, 97, 75, 46, 113, 52],
    #[47, 96, 28, 47, 112, 53],
    #[48, 124, 29, 48, 114, 54],
    #[49, 115, 1, 49, 99, 11],
    #[50, 116, 31, 50, 100, 10],
    #[51, 77, 3, 51, 98, 0],
    #[52, 57, 7, 52, 80, 24],
    #[53, 56, 48, 53, 79, 23],
    #[54, 104, 47, 54, 81, 22],
    #[55, 45, 100, 55, 72, 77],
    #[56, 43, 125, 56, 20, 115],
    #[57, 44, 98, 57, 21, 116],
    #[58, 47, 110, 58, 24, 89],
    #[59, 7, 66, 59, 22, 35],
    #[60, 48, 65, 60, 73, 91],
    #[61, 9, 123, 61, 28, 106],
    #[62, 53, 122, 62, 30, 105],
    #[63, 52, 121, 63, 29, 127],
    #[64, 31, 33, 64, 12, 60],
    #[65, 2, 83, 65, 10, 108],
    #[66, 3, 84, 66, 11, 58],
    #[67, 127, 16, 67, 123, 41],
    #[68, 106, 17, 68, 121, 42],
    #[69, 107, 18, 69, 122, 5],
    #[70, 85, 19, 70, 108, 44],
    #[71, 64, 36, 71, 35, 69],
    #[72, 88, 39, 72, 109, 14],
    #[73, 76, 52, 73, 95, 75],
    #[74, 125, 11, 74, 117, 1],
    #[75, 32, 24, 75, 55, 7],
    #[76, 15, 103, 76, 38, 78],
    #[77, 92, 56, 77, 68, 81],
    #[78, 42, 112, 78, 71, 124],
    #[79, 21, 117, 79, 44, 99],
    #[80, 20, 77, 80, 43, 100],
    #[81, 72, 115, 81, 45, 125],
    #[82, 50, 34, 82, 27, 63],
    #[83, 73, 90, 83, 48, 64],
    #[84, 22, 89, 84, 7, 110],
    #[85, 24, 35, 85, 47, 66],
    #[86, 29, 107, 86, 52, 82],
    #[87, 30, 106, 87, 53, 123],
    #[88, 28, 105, 88, 9, 122],
    #[89, 11, 59, 89, 3, 85],
    #[90, 10, 60, 90, 2, 33],
    #[91, 12, 108, 91, 31, 83],
    #[92, 122, 40, 92, 107, 71],
    #[93, 121, 41, 93, 106, 16],
    #[94, 123, 42, 94, 127, 17],
    #[95, 37, 119, 95, 14, 101],
    #[96, 39, 120, 96, 70, 102],
    #[97, 4, 78, 97, 13, 103],
    #[98, 69, 79, 98, 93, 104],
    #[99, 67, 32, 99, 36, 57],
    #[100, 111, 81, 100, 94, 56],
    #[101, 16, 96, 101, 5, 114],
    #[102, 18, 95, 102, 41, 113],
    #[103, 17, 124, 103, 40, 112],
    #[104, 6, 99, 104, 19, 117],
    #[105, 26, 61, 105, 49, 87],
    #[106, 74, 62, 106, 51, 88],
    #[107, 25, 63, 107, 8, 34],
    #[108, 46, 64, 108, 23, 90],
    #[109, 54, 82, 109, 75, 107],
    #[110, 1, 85, 110, 0, 59],
    #[111, 105, 71, 111, 82, 40],
    #[112, 13, 126, 112, 4, 118],
    #[113, 70, 101, 113, 39, 119],
    #[114, 14, 102, 114, 37, 120],
    #[115, 94, 55, 115, 111, 80],
    #[116, 36, 104, 116, 67, 79],
    #[117, 93, 57, 117, 69, 32],
    #[118, 40, 76, 118, 17, 97],
    #[119, 41, 114, 119, 18, 96],
    #[120, 5, 113, 120, 16, 95],
    #[121, 8, 86, 121, 25, 109],
    #[122, 51, 87, 122, 74, 61],
    #[123, 49, 88, 123, 26, 62],
    #[124, 38, 118, 124, 15, 126],
    #[125, 68, 80, 125, 92, 55],
    #[126, 71, 97, 126, 42, 76],
    #[127, 27, 109, 127, 50, 86]] : Array (Array ℕ)).getD k.val #[]).getD j.val 0)
set_option maxHeartbeats 1600000 in
private theorem cert37_3 : ∃ c, c ∈ Subgroup.centralizer (Subgroup.closure (Set.range e37_3) : Set SylowModel) ∧ c ∉ Subgroup.closure (Set.range e37_3) := by
  refine ⟨rootOne ^ 2 * root 2 * root 6 * root 8, centralizes_generators e37_3 _ (by decide +kernel), ?_⟩
  exact outside_of_table e37_3 a37_3 0 next37_3 prev37_3
    (by decide +kernel) (by decide +kernel) (by decide +kernel) _ (by decide +kernel)

private def e37_4 : Fin 6 → SylowModel := ![decode 64, decode 1032, decode 0, decode 576, decode 1496, decode 128]
set_option maxHeartbeats 1600000 in
private theorem edgeEq37_4 : binaryFamily s37 (s37 2) (![false, false, true]) = e37_4 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert37_4 : Represented smallParityCensusNode (Subgroup.closure (Set.range e37_4)) := by
  refine ⟨69, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node69]
  exact closure_eq_words _ o69 (![[3, 5], [0], [], [3, 4, 5], [1, 0, 3, 4], [5, 6]]) (![[1], [1, 1, 1, 3, 4], [1, 1], [0, 1, 4, 4, 1], [0, 3], [1, 4, 4, 1], [1, 4, 1, 4]]) (by decide +kernel) (by decide +kernel)

private def e37_5 : Fin 6 → SylowModel := ![decode 0, decode 1032, decode 508, decode 0, decode 1416, decode 1020]
set_option maxHeartbeats 1600000 in
private theorem edgeEq37_5 : binaryFamily s37 (s37 0) (![true, false, true]) = e37_5 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert37_5 : Represented smallParityCensusNode (Subgroup.closure (Set.range e37_5)) := by
  refine ⟨73, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node73]
  exact closure_eq_words _ o73 (![[], [0], [1, 5, 6], [], [0, 5], [1, 1, 1, 6]]) (![[1], [1, 1, 2, 1, 1], [1, 1], [1, 1, 2, 4, 5, 1], [2, 2, 2, 5], [2, 5], [1, 1, 4, 4]]) (by decide +kernel) (by decide +kernel)

private def e37_6 : Fin 6 → SylowModel := ![decode 64, decode 0, decode 4004, decode 448, decode 2320, decode 1636]
set_option maxHeartbeats 1600000 in
private theorem edgeEq37_6 : binaryFamily s37 (s37 1) (![false, true, true]) = e37_6 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert37_6 : Represented smallParityCensusNode (Subgroup.closure (Set.range e37_6)) := by
  refine ⟨71, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node71]
  exact closure_eq_words _ o71 (![[3, 4, 5], [], [0, 3, 2], [3], [1, 2, 6], [4, 5, 0]]) (![[0, 3, 5], [0, 5, 4, 5], [3, 2, 2], [3], [0, 2, 0, 5], [2, 0, 5, 3], [0, 2, 5, 3]]) (by decide +kernel) (by decide +kernel)

private def e37_7 : Fin 6 → SylowModel := ![decode 0, decode 1992, decode 508, decode 0, decode 1608, decode 1020]
set_option maxHeartbeats 1600000 in
private theorem edgeEq37_7 : binaryFamily s37 (s37 0) (![true, true, true]) = e37_7 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert37_7 : Represented smallParityCensusNode (Subgroup.closure (Set.range e37_7)) := by
  refine ⟨73, root 2 * root 3 * root 4 * root 7, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node73]
  exact closure_eq_words _ o73 (![[], [3, 0], [1, 5, 6], [], [0, 3], [1, 1, 1, 6]]) (![[2, 4, 5], [1, 1, 2, 1, 1], [4, 1], [1, 1, 1, 2, 1, 5], [2, 2, 2, 5], [2, 5], [1, 1, 4, 4]]) (by decide +kernel) (by decide +kernel)

private def s38 : Fin 3 → SylowModel := ![root 2 * root 3 * root 4 * root 7, root 6, rootOne ^ 3 * root 3 * root 4 * root 5 * root 8]
set_option maxHeartbeats 1600000 in
private theorem gen38 : Subgroup.closure (Set.range s38) = smallParityCensusNode 38 := by
  rw [node38]
  exact closure_eq_words s38 o38 (![[1, 6], [4, 5], [0]]) (![[2], [1, 0, 1], [0, 1, 0, 2, 2], [0, 0, 2, 0, 2, 0, 2, 2], [2, 2, 2, 1, 2], [1, 2, 2, 2, 1, 2], [0, 0, 0, 1, 0, 1], [2, 2, 2, 2]]) (by decide +kernel) (by decide +kernel)

private def e38_1 : Fin 6 → SylowModel := ![decode 0, decode 64, decode 1640, decode 640, decode 576, decode 1272]
set_option maxHeartbeats 1600000 in
private theorem edgeEq38_1 : binaryFamily s38 (s38 0) (![true, false, false]) = e38_1 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert38_1 : Represented smallParityCensusNode (Subgroup.closure (Set.range e38_1)) := by
  refine ⟨71, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node71]
  exact closure_eq_words _ o71 (![[], [3, 5], [0], [4, 5, 6], [3, 4, 5], [0, 1, 6]]) (![[2], [2, 2, 2, 5], [5, 4, 5], [2, 2, 2, 1, 2], [1, 4], [2, 2, 5, 3, 5], [2, 2, 2, 2]]) (by decide +kernel) (by decide +kernel)

private def e38_2 : Fin 6 → SylowModel := ![decode 156, decode 0, decode 1640, decode 668, decode 0, decode 2024]
set_option maxHeartbeats 1600000 in
private theorem edgeEq38_2 : binaryFamily s38 (s38 1) (![false, true, false]) = e38_2 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert38_2 : Represented smallParityCensusNode (Subgroup.closure (Set.range e38_2)) := by
  refine ⟨74, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node74]
  exact closure_eq_words _ o74 (![[1, 5, 6], [], [0], [1], [], [4, 0, 5]]) (![[2], [3], [2, 2], [0, 2, 0, 2, 2, 5], [0, 0], [0, 0, 2, 2, 2, 5], [2, 2, 2, 2]]) (by decide +kernel) (by decide +kernel)

private def e38_3 : Fin 6 → SylowModel := ![decode 0, decode 92, decode 1640, decode 640, decode 220, decode 1272]
set_option maxHeartbeats 1600000 in
private theorem edgeEq38_3 : binaryFamily s38 (s38 0) (![true, true, false]) = e38_3 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert38_3 : Represented smallParityCensusNode (Subgroup.closure (Set.range e38_3)) := by
  refine ⟨74, root 1 * root 2 * root 4 * root 6 * root 7 * root 9, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node74]
  exact closure_eq_words _ o74 (![[], [1, 4, 5], [3, 0, 1], [4, 5, 6], [1, 5], [0, 1, 4, 5]]) (![[5, 4], [2, 1, 2, 2, 5], [1, 2, 1, 2], [2, 2, 5, 3, 2], [1, 1], [1, 2, 1, 2, 2, 5], [2, 2, 2, 2]]) (by decide +kernel) (by decide +kernel)

private def e38_4 : Fin 6 → SylowModel := ![decode 156, decode 64, decode 0, decode 780, decode 448, decode 2512]
set_option maxHeartbeats 1600000 in
private theorem edgeEq38_4 : binaryFamily s38 (s38 2) (![false, false, true]) = e38_4 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert38_4 : Subgroup.closure (Set.range e38_4) ≤ character.ker := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨j, rfl⟩
  exact (show ∀ j, e38_4 j ∈ character.ker from by decide +kernel) j

private def e38_5 : Fin 6 → SylowModel := ![decode 0, decode 64, decode 2020, decode 640, decode 576, decode 2036]
set_option maxHeartbeats 1600000 in
private theorem edgeEq38_5 : binaryFamily s38 (s38 0) (![true, false, true]) = e38_5 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert38_5 : Represented smallParityCensusNode (Subgroup.closure (Set.range e38_5)) := by
  refine ⟨71, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node71]
  exact closure_eq_words _ o71 (![[], [3, 4, 5], [0], [5, 6], [3, 5], [0, 1, 6]]) (![[2], [2, 2, 2, 5], [5, 1, 5], [2, 1, 2, 5, 5], [1, 4], [2, 2, 2, 2, 3], [2, 2, 2, 2]]) (by decide +kernel) (by decide +kernel)

private def e38_6 : Fin 6 → SylowModel := ![decode 156, decode 0, decode 1448, decode 668, decode 0, decode 1064]
set_option maxHeartbeats 1600000 in
private theorem edgeEq38_6 : binaryFamily s38 (s38 1) (![false, true, true]) = e38_6 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert38_6 : Represented smallParityCensusNode (Subgroup.closure (Set.range e38_6)) := by
  refine ⟨74, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node74]
  exact closure_eq_words _ o74 (![[1, 5, 6], [], [0, 3], [1], [], [3, 4, 0]]) (![[0, 5, 3], [3], [0, 0, 5, 2], [0, 2, 0, 2, 5, 2], [0, 0], [0, 0, 2, 2, 2, 5], [2, 2, 2, 2]]) (by decide +kernel) (by decide +kernel)

private def e38_7 : Fin 6 → SylowModel := ![decode 0, decode 92, decode 2020, decode 640, decode 220, decode 2036]
set_option maxHeartbeats 1600000 in
private theorem edgeEq38_7 : binaryFamily s38 (s38 0) (![true, true, true]) = e38_7 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert38_7 : Represented smallParityCensusNode (Subgroup.closure (Set.range e38_7)) := by
  refine ⟨74, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node74]
  exact closure_eq_words _ o74 (![[], [1, 4, 5], [0], [4, 5, 6], [1, 5], [0, 3, 6]]) (![[2], [2, 4, 2, 2, 5], [2, 2], [2, 2, 2, 5], [1, 1], [1, 2, 4, 2, 2, 5], [2, 2, 2, 2]]) (by decide +kernel) (by decide +kernel)

private def s39 : Fin 3 → SylowModel := ![rootOne ^ 3, root 6, root 3]
set_option maxHeartbeats 1600000 in
private theorem gen39 : Subgroup.closure (Set.range s39) = smallParityCensusNode 39 := by
  rw [node39]
  exact closure_eq_words s39 o39 (![[1], [4, 5, 6], [0]]) (![[2], [0], [0, 0], [0, 0, 0, 2, 0, 2, 2, 2], [0, 0, 0, 2, 1, 2, 0], [0, 0, 1, 0, 1, 0], [1, 2, 1, 2, 2, 2], [2, 2]]) (by decide +kernel) (by decide +kernel)

private def e39_1 : Fin 6 → SylowModel := ![decode 0, decode 64, decode 8, decode 2048, decode 960, decode 24]
set_option maxHeartbeats 1600000 in
private theorem edgeEq39_1 : binaryFamily s39 (s39 0) (![true, false, false]) = e39_1 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert39_1 : Subgroup.closure (Set.range e39_1) ≤ character.ker := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨j, rfl⟩
  exact (show ∀ j, e39_1 j ∈ character.ker from by decide +kernel) j

private def e39_2 : Fin 6 → SylowModel := ![decode 1024, decode 0, decode 8, decode 1920, decode 0, decode 520]
set_option maxHeartbeats 1600000 in
private theorem edgeEq39_2 : binaryFamily s39 (s39 1) (![false, true, false]) = e39_2 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert39_2 : Represented smallParityCensusNode (Subgroup.closure (Set.range e39_2)) := by
  refine ⟨75, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node75]
  exact closure_eq_words _ o75 (![[1], [], [0], [4, 1], [], [0, 5]]) (![[2], [0], [0, 0], [0, 0, 2, 3, 2, 3], [0, 0, 3, 0], [2, 2, 2, 5], [2, 2]]) (by decide +kernel) (by decide +kernel)

private def e39_3 : Fin 6 → SylowModel := ![decode 0, decode 3136, decode 8, decode 2048, decode 1984, decode 24]
set_option maxHeartbeats 1600000 in
private theorem edgeEq39_3 : binaryFamily s39 (s39 0) (![true, true, false]) = e39_3 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert39_3 : Represented smallParityCensusNode (Subgroup.closure (Set.range e39_3)) := by
  refine ⟨75, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node75]
  exact closure_eq_words _ o75 (![[], [0, 1, 0, 2, 5], [0, 4, 6], [1, 4, 1], [0, 1, 0, 5], [0, 3, 4, 5]]) (![[1, 1, 2, 3], [2, 2, 2, 5, 4], [1, 1], [1, 2, 4, 2], [1, 3, 1], [1, 2, 2, 2, 4, 5], [2, 2]]) (by decide +kernel) (by decide +kernel)

private def e39_4 : Fin 6 → SylowModel := ![decode 1024, decode 64, decode 0, decode 1040, decode 576, decode 256]
set_option maxHeartbeats 1600000 in
private theorem edgeEq39_4 : binaryFamily s39 (s39 2) (![false, false, true]) = e39_4 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert39_4 : Represented smallParityCensusNode (Subgroup.closure (Set.range e39_4)) := by
  refine ⟨61, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node61]
  exact closure_eq_words _ o61 (![[0], [3, 4, 5], [], [0, 1, 6], [3, 5], [6]]) (![[0], [0, 0, 0, 3, 5], [0, 0], [0, 4, 0, 0, 0], [1, 4], [0, 0, 1, 0, 1, 0], [5]]) (by decide +kernel) (by decide +kernel)

private def e39_5 : Fin 6 → SylowModel := ![decode 0, decode 64, decode 3080, decode 2048, decode 960, decode 1048]
set_option maxHeartbeats 1600000 in
private theorem edgeEq39_5 : binaryFamily s39 (s39 0) (![true, false, true]) = e39_5 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert39_5 : Represented smallParityCensusNode (Subgroup.closure (Set.range e39_5)) := by
  refine ⟨69, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node69]
  exact closure_eq_words _ o69 (![[], [3, 5], [0, 1, 2, 5], [1, 2, 5], [3, 4], [1, 0, 5]]) (![[2, 3], [1, 2, 3, 1, 2], [2, 2], [2, 1, 5], [1, 5, 4, 2], [1, 2, 1, 5], [2, 5]]) (by decide +kernel) (by decide +kernel)

private def e39_6 : Fin 6 → SylowModel := ![decode 1024, decode 0, decode 72, decode 1920, decode 0, decode 584]
set_option maxHeartbeats 1600000 in
private theorem edgeEq39_6 : binaryFamily s39 (s39 1) (![false, true, true]) = e39_6 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert39_6 : Represented smallParityCensusNode (Subgroup.closure (Set.range e39_6)) := by
  refine ⟨76, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node76]
  exact closure_eq_words _ o76 (![[1], [], [0, 4, 5], [4, 1], [], [0, 4]]) (![[0, 0, 3, 0, 5], [0], [0, 0], [0, 0, 2, 0, 5, 3], [0, 0, 3, 0], [2, 2, 2, 5], [2, 5]]) (by decide +kernel) (by decide +kernel)

private def e39_7 : Fin 6 → SylowModel := ![decode 0, decode 3136, decode 3080, decode 2048, decode 1984, decode 1048]
set_option maxHeartbeats 1600000 in
private theorem edgeEq39_7 : binaryFamily s39 (s39 0) (![true, true, true]) = e39_7 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert39_7 : Represented smallParityCensusNode (Subgroup.closure (Set.range e39_7)) := by
  refine ⟨76, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node76]
  exact closure_eq_words _ o76 (![[], [0, 0, 1, 2, 3], [0, 1, 2, 3, 5], [1, 4, 1], [0, 0, 1, 3], [0, 1, 4]]) (![[1, 1, 2, 1], [2, 2, 4, 3], [1, 1], [1, 2, 3, 1, 5], [1, 3, 1], [1, 2, 1, 2], [2, 5]]) (by decide +kernel) (by decide +kernel)

private def s40 : Fin 3 → SylowModel := ![root 6, root 3, rootOne ^ 3 * root 5 * root 8]
set_option maxHeartbeats 1600000 in
private theorem gen40 : Subgroup.closure (Set.range s40) = smallParityCensusNode 40 := by
  rw [node40]
  exact closure_eq_words s40 o40 (![[4, 5, 6], [0], [1]]) (![[1], [2], [2, 1, 0, 1, 2], [1, 2, 1, 2, 2, 2], [1, 2, 0, 2, 2, 2, 1], [0, 2, 2, 2, 0, 2], [0, 1, 0, 1, 1, 1], [1, 1]]) (by decide +kernel) (by decide +kernel)

private def e40_1 : Fin 6 → SylowModel := ![decode 0, decode 8, decode 1632, decode 0, decode 520, decode 1504]
set_option maxHeartbeats 1600000 in
private theorem edgeEq40_1 : binaryFamily s40 (s40 0) (![true, false, false]) = e40_1 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert40_1 : Represented smallParityCensusNode (Subgroup.closure (Set.range e40_1)) := by
  refine ⟨77, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node77]
  exact closure_eq_words _ o77 (![[], [0], [1], [], [0, 5], [4, 1]]) (![[1], [2], [2, 2], [1, 2, 2, 2, 1, 2], [2, 2, 2, 5], [1, 1, 1, 4], [1, 1]]) (by decide +kernel) (by decide +kernel)

private def e40_2 : Fin 6 → SylowModel := ![decode 64, decode 0, decode 1632, decode 576, decode 256, decode 1648]
set_option maxHeartbeats 1600000 in
private theorem edgeEq40_2 : binaryFamily s40 (s40 1) (![false, true, false]) = e40_2 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert40_2 : Represented smallParityCensusNode (Subgroup.closure (Set.range e40_2)) := by
  refine ⟨63, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node63]
  exact closure_eq_words _ o63 (![[3, 4, 5], [], [0], [3, 5], [6], [1, 0, 6]]) (![[2], [2, 2, 5, 2], [2, 3, 2, 4], [2, 2, 2, 3, 2], [0, 3], [0, 2, 2, 2, 0, 2], [4]]) (by decide +kernel) (by decide +kernel)

private def e40_3 : Fin 6 → SylowModel := ![decode 0, decode 72, decode 1632, decode 0, decode 584, decode 1504]
set_option maxHeartbeats 1600000 in
private theorem edgeEq40_3 : binaryFamily s40 (s40 0) (![true, true, false]) = e40_3 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert40_3 : Represented smallParityCensusNode (Subgroup.closure (Set.range e40_3)) := by
  refine ⟨78, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node78]
  exact closure_eq_words _ o78 (![[], [0, 4, 5], [1], [], [0, 4], [4, 1]]) (![[2, 2, 1, 5, 2], [2], [2, 2], [1, 2, 1, 2, 5, 2], [2, 2, 2, 5], [1, 1, 1, 4], [1, 4]]) (by decide +kernel) (by decide +kernel)

private def e40_4 : Fin 6 → SylowModel := ![decode 64, decode 8, decode 0, decode 960, decode 24, decode 2240]
set_option maxHeartbeats 1600000 in
private theorem edgeEq40_4 : binaryFamily s40 (s40 2) (![false, false, true]) = e40_4 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert40_4 : Subgroup.closure (Set.range e40_4) ≤ character.ker := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨j, rfl⟩
  exact (show ∀ j, e40_4 j ∈ character.ker from by decide +kernel) j

private def e40_5 : Fin 6 → SylowModel := ![decode 0, decode 8, decode 1440, decode 0, decode 520, decode 1568]
set_option maxHeartbeats 1600000 in
private theorem edgeEq40_5 : binaryFamily s40 (s40 0) (![true, false, true]) = e40_5 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert40_5 : Represented smallParityCensusNode (Subgroup.closure (Set.range e40_5)) := by
  refine ⟨77, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node77]
  exact closure_eq_words _ o77 (![[], [0, 4, 6], [0, 1, 0], [], [0, 4, 5, 6], [1, 3, 4]]) (![[1, 2, 2, 5, 2], [1, 1, 1, 2, 1], [1, 4, 5, 5], [1, 2, 2, 5, 1, 5], [2, 2, 2, 5], [1, 1, 1, 4], [1, 1]]) (by decide +kernel) (by decide +kernel)

private def e40_6 : Fin 6 → SylowModel := ![decode 64, decode 0, decode 1912, decode 576, decode 256, decode 1640]
set_option maxHeartbeats 1600000 in
private theorem edgeEq40_6 : binaryFamily s40 (s40 1) (![false, true, true]) = e40_6 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert40_6 : Represented smallParityCensusNode (Subgroup.closure (Set.range e40_6)) := by
  refine ⟨71, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node71]
  exact closure_eq_words _ o71 (![[3, 5], [], [1, 5, 0], [3, 4, 5], [6], [0]]) (![[5], [0, 2, 2, 2, 3, 5], [2, 3, 2, 4], [2, 2, 2, 0, 2], [0, 3], [0, 2, 2, 2, 0, 2], [4]]) (by decide +kernel) (by decide +kernel)

private def e40_7 : Fin 6 → SylowModel := ![decode 0, decode 72, decode 1440, decode 0, decode 584, decode 1568]
set_option maxHeartbeats 1600000 in
private theorem edgeEq40_7 : binaryFamily s40 (s40 0) (![true, true, true]) = e40_7 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert40_7 : Represented smallParityCensusNode (Subgroup.closure (Set.range e40_7)) := by
  refine ⟨78, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node78]
  exact closure_eq_words _ o78 (![[], [0, 6], [1, 3, 6], [], [0, 0, 0], [1, 3, 4]]) (![[1, 1, 4], [1, 1, 1, 5, 1], [1, 1, 5, 5], [1, 2, 1, 2, 2, 5], [2, 2, 2, 5], [1, 1, 1, 4], [1, 4]]) (by decide +kernel) (by decide +kernel)

private def s41 : Fin 3 → SylowModel := ![rootOne ^ 3, root 6, root 3 * root 5 * root 8]
set_option maxHeartbeats 1600000 in
private theorem gen41 : Subgroup.closure (Set.range s41) = smallParityCensusNode 41 := by
  rw [node41]
  exact closure_eq_words s41 o41 (![[1], [4, 5, 6], [0]]) (![[2], [0], [0, 0], [0, 0, 0, 1, 2, 0, 2], [0, 0, 0, 2, 1, 2, 0], [0, 0, 1, 0, 1, 0], [1, 2, 1, 2, 2, 2], [2, 2]]) (by decide +kernel) (by decide +kernel)

private def e41_1 : Fin 6 → SylowModel := ![decode 0, decode 64, decode 296, decode 2048, decode 960, decode 632]
set_option maxHeartbeats 1600000 in
private theorem edgeEq41_1 : binaryFamily s41 (s41 0) (![true, false, false]) = e41_1 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert41_1 : Subgroup.closure (Set.range e41_1) ≤ character.ker := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨j, rfl⟩
  exact (show ∀ j, e41_1 j ∈ character.ker from by decide +kernel) j

private def e41_2 : Fin 6 → SylowModel := ![decode 1024, decode 0, decode 296, decode 1920, decode 0, decode 808]
set_option maxHeartbeats 1600000 in
private theorem edgeEq41_2 : binaryFamily s41 (s41 1) (![false, true, false]) = e41_2 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert41_2 : Represented smallParityCensusNode (Subgroup.closure (Set.range e41_2)) := by
  refine ⟨79, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node79]
  exact closure_eq_words _ o79 (![[1], [], [0], [5, 1], [], [0, 4]]) (![[2], [0], [0, 0], [0, 0, 2, 0, 2, 3], [2, 2, 2, 5], [0, 0, 3, 0], [2, 2]]) (by decide +kernel) (by decide +kernel)

private def e41_3 : Fin 6 → SylowModel := ![decode 0, decode 3136, decode 296, decode 2048, decode 1984, decode 632]
set_option maxHeartbeats 1600000 in
private theorem edgeEq41_3 : binaryFamily s41 (s41 0) (![true, true, false]) = e41_3 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert41_3 : Represented smallParityCensusNode (Subgroup.closure (Set.range e41_3)) := by
  refine ⟨79, root 2 * root 3 * root 4 * root 7, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node79]
  exact closure_eq_words _ o79 (![[], [1, 2, 3, 4], [0, 5, 6], [2], [3, 1, 4], [0, 3, 4, 6]]) (![[1, 1, 3, 2], [1, 2, 3, 5], [3], [1, 2, 4, 2], [1, 2, 3, 1, 5], [1, 3, 1], [2, 2]]) (by decide +kernel) (by decide +kernel)

private def e41_4 : Fin 6 → SylowModel := ![decode 1024, decode 64, decode 0, decode 1360, decode 576, decode 256]
set_option maxHeartbeats 1600000 in
private theorem edgeEq41_4 : binaryFamily s41 (s41 2) (![false, false, true]) = e41_4 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert41_4 : Represented smallParityCensusNode (Subgroup.closure (Set.range e41_4)) := by
  refine ⟨61, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node61]
  exact closure_eq_words _ o61 (![[0], [3, 4, 5], [], [0, 1, 3, 4, 6], [3, 5], [6]]) (![[0], [0, 0, 0, 1, 3], [0, 0], [0, 0, 3, 3, 4], [1, 4], [0, 0, 3, 3], [5]]) (by decide +kernel) (by decide +kernel)

private def e41_5 : Fin 6 → SylowModel := ![decode 0, decode 64, decode 3368, decode 2048, decode 960, decode 1656]
set_option maxHeartbeats 1600000 in
private theorem edgeEq41_5 : binaryFamily s41 (s41 0) (![true, false, true]) = e41_5 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert41_5 : Represented smallParityCensusNode (Subgroup.closure (Set.range e41_5)) := by
  refine ⟨71, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node71]
  exact closure_eq_words _ o71 (![[], [3, 5], [3, 0, 1, 2], [1, 2, 5], [3, 4], [1, 0, 5]]) (![[3, 4, 2], [2, 1, 3, 2], [4, 2, 2], [2, 1, 5], [1, 5, 4, 2], [1, 2, 1, 5], [2, 5]]) (by decide +kernel) (by decide +kernel)

private def e41_6 : Fin 6 → SylowModel := ![decode 1024, decode 0, decode 360, decode 1920, decode 0, decode 872]
set_option maxHeartbeats 1600000 in
private theorem edgeEq41_6 : binaryFamily s41 (s41 1) (![false, true, true]) = e41_6 := by decide +kernel
private def a41_6 (k : Fin 128) : SylowModel :=
  decode ((#[0, 1024, 2048, 384, 768, 512, 3072, 1152, 1792, 1536, 2432, 2816, 2560, 464, 640, 896, 256, 3200, 3840, 3584, 1872, 1920, 1664, 1280, 2256, 2688, 2944, 2304, 80, 720, 976, 128, 232, 3664, 3968, 3712, 3328, 2000, 1104, 1360, 1408, 2384, 3024, 2768, 2176, 848, 592, 208, 2664, 360, 1000, 744, 3792, 3408, 3152, 3456, 1232, 1488, 1616, 2640, 2896, 2512, 336, 1976, 1768, 3048, 2408, 2152, 824, 616, 872, 488, 3536, 3280, 3920, 1744, 2128, 3128, 3176, 1848, 1208, 1464, 1640, 1512, 1256, 2232, 2280, 2536, 2920, 696, 56, 312, 104, 4048, 3256, 3896, 3640, 3304, 3944, 3688, 1080, 1336, 1720, 1384, 1128, 2024, 2360, 3000, 2744, 2792, 440, 184, 568, 4024, 3768, 3384, 4072, 3816, 3432, 1592, 1896, 2616, 2872, 2488, 952, 3512, 3560, 2104] : Array ℕ).getD k.val 0)
private def next41_6 (k : Fin 128) (j : Fin 6) : Fin 128 :=
  Fin.ofNat 128 (((#[#[1, 0, 49, 21, 0, 70],
    #[2, 1, 81, 25, 1, 63],
    #[6, 2, 65, 34, 2, 87],
    #[40, 3, 32, 9, 3, 51],
    #[8, 4, 69, 7, 4, 92],
    #[9, 5, 70, 40, 5, 49],
    #[0, 6, 96, 14, 6, 77],
    #[44, 7, 101, 12, 7, 79],
    #[11, 8, 102, 10, 8, 80],
    #[12, 9, 63, 44, 9, 81],
    #[55, 10, 48, 19, 10, 67],
    #[18, 11, 86, 17, 11, 109],
    #[19, 12, 87, 55, 12, 65],
    #[57, 13, 89, 58, 13, 111],
    #[22, 14, 50, 23, 14, 71],
    #[21, 15, 51, 1, 15, 32],
    #[23, 16, 92, 22, 16, 69],
    #[31, 17, 114, 5, 17, 94],
    #[4, 18, 115, 3, 18, 95],
    #[5, 19, 77, 31, 19, 96],
    #[60, 20, 84, 61, 20, 64],
    #[26, 21, 119, 27, 21, 100],
    #[25, 22, 79, 2, 22, 101],
    #[27, 23, 80, 26, 23, 102],
    #[73, 24, 106, 74, 24, 122],
    #[35, 25, 66, 36, 25, 88],
    #[34, 26, 67, 6, 26, 48],
    #[36, 27, 109, 35, 27, 86],
    #[38, 28, 68, 37, 28, 91],
    #[75, 29, 110, 39, 29, 124],
    #[37, 30, 111, 38, 30, 89],
    #[7, 31, 71, 8, 31, 50],
    #[84, 32, 14, 120, 32, 31],
    #[46, 33, 99, 47, 33, 78],
    #[15, 34, 125, 16, 34, 113],
    #[14, 35, 94, 0, 35, 114],
    #[16, 36, 95, 15, 36, 115],
    #[42, 37, 104, 41, 37, 82],
    #[76, 38, 105, 43, 38, 83],
    #[41, 39, 64, 42, 39, 84],
    #[10, 40, 100, 11, 40, 119],
    #[53, 41, 85, 52, 41, 108],
    #[93, 42, 121, 54, 42, 127],
    #[52, 43, 122, 53, 43, 106],
    #[17, 44, 88, 18, 44, 66],
    #[20, 45, 90, 56, 45, 112],
    #[58, 46, 91, 57, 46, 68],
    #[56, 47, 124, 20, 47, 110],
    #[99, 48, 25, 126, 48, 44],
    #[103, 49, 4, 64, 49, 16],
    #[105, 50, 3, 104, 50, 15],
    #[64, 51, 31, 103, 51, 14],
    #[29, 52, 117, 28, 52, 97],
    #[62, 53, 118, 30, 53, 98],
    #[28, 54, 78, 29, 54, 99],
    #[3, 55, 113, 4, 55, 125],
    #[24, 56, 120, 59, 56, 103],
    #[61, 57, 82, 60, 57, 104],
    #[59, 58, 83, 24, 58, 105],
    #[33, 59, 107, 72, 59, 123],
    #[74, 60, 108, 73, 60, 85],
    #[72, 61, 127, 33, 61, 121],
    #[39, 62, 112, 75, 62, 90],
    #[107, 63, 23, 106, 63, 8],
    #[109, 64, 58, 67, 64, 38],
    #[116, 65, 11, 78, 65, 27],
    #[118, 66, 10, 117, 66, 26],
    #[78, 67, 44, 116, 67, 25],
    #[79, 68, 45, 80, 68, 62],
    #[82, 69, 0, 83, 69, 5],
    #[120, 70, 16, 84, 70, 4],
    #[83, 71, 15, 82, 71, 3],
    #[13, 72, 126, 45, 72, 116],
    #[47, 73, 97, 46, 73, 117],
    #[45, 74, 98, 13, 74, 118],
    #[43, 75, 103, 76, 75, 120],
    #[54, 76, 123, 93, 76, 107],
    #[90, 77, 36, 89, 77, 18],
    #[92, 78, 74, 51, 78, 53],
    #[122, 79, 40, 123, 79, 21],
    #[85, 80, 9, 121, 80, 1],
    #[123, 81, 8, 122, 81, 23],
    #[48, 82, 75, 86, 82, 56],
    #[87, 83, 39, 88, 83, 20],
    #[86, 84, 38, 48, 84, 58],
    #[94, 85, 59, 95, 85, 76],
    #[97, 86, 2, 98, 86, 12],
    #[126, 87, 27, 99, 87, 11],
    #[98, 88, 26, 97, 88, 10],
    #[102, 89, 29, 101, 89, 47],
    #[100, 90, 28, 63, 90, 46],
    #[101, 91, 62, 102, 91, 45],
    #[104, 92, 5, 105, 92, 0],
    #[30, 93, 116, 62, 93, 126],
    #[111, 94, 55, 112, 94, 34],
    #[68, 95, 19, 110, 95, 6],
    #[112, 96, 18, 111, 96, 36],
    #[32, 97, 93, 69, 97, 72],
    #[70, 98, 54, 71, 98, 33],
    #[69, 99, 53, 32, 99, 74],
    #[127, 100, 22, 108, 100, 7],
    #[106, 101, 21, 107, 101, 40],
    #[108, 102, 1, 127, 102, 9],
    #[66, 103, 57, 65, 103, 37],
    #[67, 104, 56, 109, 104, 75],
    #[65, 105, 20, 66, 105, 39],
    #[115, 106, 42, 114, 106, 61],
    #[113, 107, 41, 77, 107, 60],
    #[114, 108, 76, 115, 108, 59],
    #[117, 109, 12, 118, 109, 2],
    #[81, 110, 13, 119, 110, 30],
    #[80, 111, 47, 79, 111, 29],
    #[119, 112, 46, 81, 112, 28],
    #[124, 113, 35, 91, 113, 17],
    #[89, 114, 34, 90, 114, 55],
    #[91, 115, 6, 124, 115, 19],
    #[50, 116, 73, 49, 116, 52],
    #[51, 117, 72, 92, 117, 93],
    #[49, 118, 33, 50, 118, 54],
    #[121, 119, 7, 85, 119, 22],
    #[88, 120, 37, 87, 120, 57],
    #[96, 121, 24, 125, 121, 43],
    #[95, 122, 61, 94, 122, 42],
    #[125, 123, 60, 96, 123, 41],
    #[63, 124, 30, 100, 124, 13],
    #[110, 125, 17, 68, 125, 35],
    #[71, 126, 52, 70, 126, 73],
    #[77, 127, 43, 113, 127, 24]] : Array (Array ℕ)).getD k.val #[]).getD j.val 0)
private def prev41_6 (k : Fin 128) (j : Fin 6) : Fin 128 :=
  Fin.ofNat 128 (((#[#[6, 0, 69, 35, 0, 92],
    #[0, 1, 102, 15, 1, 80],
    #[1, 2, 86, 22, 2, 109],
    #[55, 3, 50, 18, 3, 71],
    #[18, 4, 49, 55, 4, 70],
    #[19, 5, 92, 17, 5, 69],
    #[2, 6, 115, 26, 6, 95],
    #[31, 7, 119, 4, 7, 100],
    #[4, 8, 81, 31, 8, 63],
    #[5, 9, 80, 3, 9, 102],
    #[40, 10, 66, 8, 10, 88],
    #[8, 11, 65, 40, 11, 87],
    #[9, 12, 109, 7, 12, 86],
    #[72, 13, 110, 74, 13, 124],
    #[35, 14, 32, 6, 14, 51],
    #[34, 15, 71, 36, 15, 50],
    #[36, 16, 70, 34, 16, 49],
    #[44, 17, 125, 11, 17, 113],
    #[11, 18, 96, 44, 18, 77],
    #[12, 19, 95, 10, 19, 115],
    #[45, 20, 105, 47, 20, 83],
    #[15, 21, 101, 0, 21, 79],
    #[14, 22, 100, 16, 22, 119],
    #[16, 23, 63, 14, 23, 81],
    #[56, 24, 121, 58, 24, 127],
    #[22, 25, 48, 1, 25, 67],
    #[21, 26, 88, 23, 26, 66],
    #[23, 27, 87, 21, 27, 65],
    #[54, 28, 90, 52, 28, 112],
    #[52, 29, 89, 54, 29, 111],
    #[93, 30, 124, 53, 30, 110],
    #[17, 31, 51, 19, 31, 32],
    #[97, 32, 3, 99, 32, 15],
    #[59, 33, 118, 61, 33, 98],
    #[26, 34, 114, 2, 34, 94],
    #[25, 35, 113, 27, 35, 125],
    #[27, 36, 77, 25, 36, 96],
    #[30, 37, 120, 28, 37, 103],
    #[28, 38, 84, 30, 38, 64],
    #[62, 39, 83, 29, 39, 105],
    #[3, 40, 79, 5, 40, 101],
    #[39, 41, 107, 37, 41, 123],
    #[37, 42, 106, 39, 42, 122],
    #[75, 43, 127, 38, 43, 121],
    #[7, 44, 67, 9, 44, 48],
    #[74, 45, 68, 72, 45, 91],
    #[33, 46, 112, 73, 46, 90],
    #[73, 47, 111, 33, 47, 89],
    #[82, 48, 10, 84, 48, 26],
    #[118, 49, 0, 116, 49, 5],
    #[116, 50, 14, 118, 50, 31],
    #[117, 51, 15, 78, 51, 3],
    #[43, 52, 126, 41, 52, 116],
    #[41, 53, 99, 43, 53, 78],
    #[76, 54, 98, 42, 54, 118],
    #[10, 55, 94, 12, 55, 114],
    #[47, 56, 104, 45, 56, 82],
    #[13, 57, 103, 46, 57, 120],
    #[46, 58, 64, 13, 58, 84],
    #[58, 59, 85, 56, 59, 108],
    #[20, 60, 123, 57, 60, 107],
    #[57, 61, 122, 20, 61, 106],
    #[53, 62, 91, 93, 62, 68],
    #[124, 63, 9, 90, 63, 1],
    #[51, 64, 39, 49, 64, 20],
    #[105, 65, 2, 103, 65, 12],
    #[103, 66, 25, 105, 66, 44],
    #[104, 67, 26, 64, 67, 10],
    #[95, 68, 28, 125, 68, 46],
    #[99, 69, 4, 97, 69, 16],
    #[98, 70, 5, 126, 70, 0],
    #[126, 71, 31, 98, 71, 14],
    #[61, 72, 117, 59, 72, 97],
    #[24, 73, 116, 60, 73, 126],
    #[60, 74, 78, 24, 74, 99],
    #[29, 75, 82, 62, 75, 104],
    #[38, 76, 108, 75, 76, 85],
    #[127, 77, 19, 107, 77, 6],
    #[67, 78, 54, 65, 78, 33],
    #[68, 79, 22, 111, 79, 7],
    #[111, 80, 23, 68, 80, 8],
    #[110, 81, 1, 112, 81, 9],
    #[69, 82, 57, 71, 82, 37],
    #[71, 83, 58, 69, 83, 38],
    #[32, 84, 20, 70, 84, 39],
    #[80, 85, 41, 119, 85, 60],
    #[84, 86, 11, 82, 86, 27],
    #[83, 87, 12, 120, 87, 2],
    #[120, 88, 44, 83, 88, 25],
    #[114, 89, 13, 77, 89, 30],
    #[77, 90, 45, 114, 90, 62],
    #[115, 91, 46, 113, 91, 28],
    #[78, 92, 16, 117, 92, 4],
    #[42, 93, 97, 76, 93, 117],
    #[85, 94, 35, 122, 94, 17],
    #[122, 95, 36, 85, 95, 18],
    #[121, 96, 6, 123, 96, 19],
    #[86, 97, 73, 88, 97, 52],
    #[88, 98, 74, 86, 98, 53],
    #[48, 99, 33, 87, 99, 54],
    #[90, 100, 40, 124, 100, 21],
    #[91, 101, 7, 89, 101, 22],
    #[89, 102, 8, 91, 102, 23],
    #[49, 103, 75, 51, 103, 56],
    #[92, 104, 37, 50, 104, 57],
    #[50, 105, 38, 92, 105, 58],
    #[101, 106, 24, 63, 106, 43],
    #[63, 107, 59, 101, 107, 76],
    #[102, 108, 60, 100, 108, 41],
    #[64, 109, 27, 104, 109, 11],
    #[125, 110, 29, 95, 110, 47],
    #[94, 111, 30, 96, 111, 13],
    #[96, 112, 62, 94, 112, 45],
    #[107, 113, 55, 127, 113, 34],
    #[108, 114, 17, 106, 114, 35],
    #[106, 115, 18, 108, 115, 36],
    #[65, 116, 93, 67, 116, 72],
    #[109, 117, 52, 66, 117, 73],
    #[66, 118, 53, 109, 118, 74],
    #[112, 119, 21, 110, 119, 40],
    #[70, 120, 56, 32, 120, 75],
    #[119, 121, 42, 80, 121, 61],
    #[79, 122, 43, 81, 122, 24],
    #[81, 123, 76, 79, 123, 59],
    #[113, 124, 47, 115, 124, 29],
    #[123, 125, 34, 121, 125, 55],
    #[87, 126, 72, 48, 126, 93],
    #[100, 127, 61, 102, 127, 42]] : Array (Array ℕ)).getD k.val #[]).getD j.val 0)
set_option maxHeartbeats 1600000 in
private theorem cert41_6 : ∃ c, c ∈ Subgroup.centralizer (Subgroup.closure (Set.range e41_6) : Set SylowModel) ∧ c ∉ Subgroup.closure (Set.range e41_6) := by
  refine ⟨rootOne ^ 2 * root 2 * root 4 * root 8, centralizes_generators e41_6 _ (by decide +kernel), ?_⟩
  exact outside_of_table e41_6 a41_6 0 next41_6 prev41_6
    (by decide +kernel) (by decide +kernel) (by decide +kernel) _ (by decide +kernel)

private def e41_7 : Fin 6 → SylowModel := ![decode 0, decode 3136, decode 3368, decode 2048, decode 1984, decode 1656]
set_option maxHeartbeats 1600000 in
private theorem edgeEq41_7 : binaryFamily s41 (s41 0) (![true, true, true]) = e41_7 := by decide +kernel
private def a41_7 (k : Fin 128) : SylowModel :=
  decode ((#[0, 2048, 384, 768, 512, 1168, 1984, 2432, 2816, 2560, 464, 640, 896, 256, 3216, 3776, 1040, 1936, 1680, 1856, 1216, 1472, 2256, 2688, 2944, 2304, 80, 720, 976, 128, 232, 3088, 3984, 3728, 3648, 3520, 3264, 1808, 1552, 1424, 1088, 1344, 1728, 2384, 3024, 2768, 2176, 848, 592, 208, 1320, 2664, 360, 1000, 744, 3856, 3600, 3472, 3392, 3136, 4032, 1296, 1600, 2640, 2896, 2512, 336, 3752, 1448, 1576, 1832, 3048, 2408, 2152, 824, 616, 872, 488, 3344, 3904, 2128, 3624, 3496, 3240, 1144, 1704, 1960, 1064, 2232, 2280, 2536, 2920, 696, 56, 312, 104, 3832, 3368, 3112, 4008, 1272, 1912, 1656, 1192, 2360, 3000, 2744, 2792, 440, 184, 568, 3704, 3576, 3320, 3880, 2040, 1784, 1400, 2616, 2872, 2488, 952, 3448, 3192, 4088, 1528, 2104, 3960] : Array ℕ).getD k.val 0)
private def next41_7 (k : Fin 128) (j : Fin 6) : Fin 128 :=
  Fin.ofNat 128 (((#[#[0, 59, 97, 1, 6, 102],
    #[1, 41, 85, 0, 15, 113],
    #[2, 35, 83, 7, 62, 115],
    #[3, 79, 81, 8, 20, 117],
    #[4, 34, 114, 9, 21, 84],
    #[5, 47, 54, 14, 65, 118],
    #[6, 0, 121, 60, 23, 91],
    #[7, 20, 70, 2, 79, 122],
    #[8, 62, 68, 3, 35, 124],
    #[9, 19, 103, 4, 36, 96],
    #[10, 57, 96, 65, 38, 68],
    #[11, 15, 99, 23, 41, 100],
    #[12, 60, 67, 24, 40, 125],
    #[13, 58, 98, 25, 42, 101],
    #[14, 63, 73, 5, 49, 108],
    #[15, 1, 126, 42, 11, 77],
    #[16, 28, 75, 31, 43, 106],
    #[17, 26, 77, 32, 45, 104],
    #[18, 66, 30, 33, 44, 126],
    #[19, 29, 74, 79, 9, 71],
    #[20, 3, 109, 36, 7, 73],
    #[21, 4, 108, 35, 46, 72],
    #[22, 39, 84, 49, 56, 81],
    #[23, 6, 87, 11, 59, 111],
    #[24, 42, 50, 12, 58, 127],
    #[25, 40, 86, 13, 60, 112],
    #[26, 31, 127, 80, 17, 87],
    #[27, 33, 112, 45, 61, 85],
    #[28, 32, 113, 44, 16, 86],
    #[29, 36, 82, 46, 19, 116],
    #[30, 83, 15, 89, 70, 17],
    #[31, 45, 89, 16, 26, 94],
    #[32, 43, 91, 17, 28, 92],
    #[33, 80, 51, 18, 27, 121],
    #[34, 46, 88, 62, 4, 52],
    #[35, 8, 119, 21, 2, 54],
    #[36, 9, 118, 20, 29, 53],
    #[37, 49, 52, 55, 63, 120],
    #[38, 10, 95, 56, 64, 88],
    #[39, 48, 53, 57, 22, 119],
    #[40, 12, 93, 59, 25, 89],
    #[41, 11, 94, 58, 1, 90],
    #[42, 13, 92, 15, 24, 51],
    #[43, 16, 125, 66, 32, 99],
    #[44, 18, 101, 28, 78, 97],
    #[45, 17, 102, 27, 31, 98],
    #[46, 21, 69, 29, 34, 123],
    #[47, 55, 123, 64, 5, 70],
    #[48, 56, 122, 63, 39, 69],
    #[49, 14, 124, 22, 37, 103],
    #[50, 54, 26, 97, 73, 23],
    #[51, 70, 6, 75, 83, 32],
    #[52, 97, 79, 72, 85, 38],
    #[53, 99, 35, 71, 87, 5],
    #[54, 67, 36, 107, 50, 39],
    #[55, 65, 71, 37, 47, 110],
    #[56, 22, 107, 38, 48, 74],
    #[57, 64, 72, 39, 10, 109],
    #[58, 24, 105, 41, 13, 75],
    #[59, 23, 106, 40, 0, 76],
    #[60, 25, 104, 6, 12, 30],
    #[61, 27, 76, 78, 80, 105],
    #[62, 2, 110, 34, 8, 107],
    #[63, 37, 116, 48, 14, 83],
    #[64, 38, 115, 47, 57, 82],
    #[65, 5, 117, 10, 55, 114],
    #[66, 78, 111, 43, 18, 50],
    #[67, 73, 43, 85, 54, 11],
    #[68, 75, 49, 82, 89, 9],
    #[69, 77, 47, 81, 91, 7],
    #[70, 30, 48, 114, 51, 46],
    #[71, 85, 62, 53, 97, 56],
    #[72, 87, 20, 52, 99, 14],
    #[73, 50, 21, 95, 67, 57],
    #[74, 127, 55, 119, 100, 62],
    #[75, 81, 59, 51, 68, 61],
    #[76, 114, 58, 91, 103, 16],
    #[77, 82, 60, 90, 69, 18],
    #[78, 44, 90, 61, 66, 93],
    #[79, 7, 120, 19, 3, 95],
    #[80, 61, 100, 26, 33, 67],
    #[81, 89, 65, 69, 75, 4],
    #[82, 91, 63, 68, 77, 2],
    #[83, 51, 64, 103, 30, 29],
    #[84, 121, 3, 123, 104, 65],
    #[85, 52, 28, 67, 71, 25],
    #[86, 95, 27, 99, 107, 1],
    #[87, 53, 66, 98, 72, 24],
    #[88, 125, 37, 109, 111, 79],
    #[89, 68, 41, 30, 81, 78],
    #[90, 103, 40, 77, 114, 31],
    #[91, 69, 42, 76, 82, 33],
    #[92, 96, 33, 106, 117, 6],
    #[93, 123, 31, 126, 115, 41],
    #[94, 122, 78, 104, 116, 40],
    #[95, 98, 34, 73, 86, 37],
    #[96, 126, 8, 116, 92, 49],
    #[97, 71, 45, 50, 52, 13],
    #[98, 107, 44, 87, 95, 0],
    #[99, 72, 80, 86, 53, 12],
    #[100, 74, 12, 113, 120, 43],
    #[101, 109, 0, 127, 118, 45],
    #[102, 108, 13, 111, 119, 44],
    #[103, 76, 10, 83, 90, 8],
    #[104, 84, 18, 94, 124, 15],
    #[105, 116, 16, 121, 122, 59],
    #[106, 115, 61, 92, 123, 58],
    #[107, 86, 19, 54, 98, 55],
    #[108, 112, 57, 120, 102, 20],
    #[109, 113, 14, 88, 101, 21],
    #[110, 111, 56, 118, 125, 19],
    #[111, 88, 24, 102, 110, 26],
    #[112, 119, 1, 125, 108, 28],
    #[113, 118, 25, 100, 109, 27],
    #[114, 90, 22, 70, 76, 3],
    #[115, 93, 29, 124, 106, 63],
    #[116, 94, 2, 96, 105, 64],
    #[117, 92, 4, 122, 126, 22],
    #[118, 101, 39, 110, 113, 35],
    #[119, 102, 5, 74, 112, 36],
    #[120, 100, 38, 108, 127, 34],
    #[121, 124, 32, 105, 84, 42],
    #[122, 105, 46, 117, 94, 47],
    #[123, 106, 7, 84, 93, 48],
    #[124, 104, 9, 115, 121, 10],
    #[125, 110, 11, 112, 88, 80],
    #[126, 117, 17, 93, 96, 60],
    #[127, 120, 23, 101, 74, 66]] : Array (Array ℕ)).getD k.val #[]).getD j.val 0)
private def prev41_7 (k : Fin 128) (j : Fin 6) : Fin 128 :=
  Fin.ofNat 128 (((#[#[0, 6, 101, 1, 59, 98],
    #[1, 15, 112, 0, 41, 86],
    #[2, 62, 116, 7, 35, 82],
    #[3, 20, 84, 8, 79, 114],
    #[4, 21, 117, 9, 34, 81],
    #[5, 65, 119, 14, 47, 53],
    #[6, 23, 51, 60, 0, 92],
    #[7, 79, 123, 2, 20, 69],
    #[8, 35, 96, 3, 62, 103],
    #[9, 36, 124, 4, 19, 68],
    #[10, 38, 103, 65, 57, 124],
    #[11, 41, 125, 23, 15, 67],
    #[12, 40, 100, 24, 60, 99],
    #[13, 42, 102, 25, 58, 97],
    #[14, 49, 109, 5, 63, 72],
    #[15, 11, 30, 42, 1, 104],
    #[16, 43, 105, 31, 28, 76],
    #[17, 45, 126, 32, 26, 30],
    #[18, 44, 104, 33, 66, 77],
    #[19, 9, 107, 79, 29, 110],
    #[20, 7, 72, 36, 3, 108],
    #[21, 46, 73, 35, 4, 109],
    #[22, 56, 114, 49, 39, 117],
    #[23, 59, 127, 11, 6, 50],
    #[24, 58, 111, 12, 42, 87],
    #[25, 60, 113, 13, 40, 85],
    #[26, 17, 50, 80, 31, 111],
    #[27, 61, 86, 45, 33, 113],
    #[28, 16, 85, 44, 32, 112],
    #[29, 19, 115, 46, 36, 83],
    #[30, 70, 18, 89, 83, 60],
    #[31, 26, 93, 16, 45, 90],
    #[32, 28, 121, 17, 43, 51],
    #[33, 27, 92, 18, 80, 91],
    #[34, 4, 95, 62, 46, 120],
    #[35, 2, 53, 21, 8, 118],
    #[36, 29, 54, 20, 9, 119],
    #[37, 63, 88, 55, 49, 95],
    #[38, 64, 120, 56, 10, 52],
    #[39, 22, 118, 57, 48, 54],
    #[40, 25, 90, 59, 12, 94],
    #[41, 1, 89, 58, 11, 93],
    #[42, 24, 91, 15, 13, 121],
    #[43, 32, 67, 66, 16, 100],
    #[44, 78, 98, 28, 18, 102],
    #[45, 31, 97, 27, 17, 101],
    #[46, 34, 122, 29, 21, 70],
    #[47, 5, 69, 64, 55, 122],
    #[48, 39, 70, 63, 56, 123],
    #[49, 37, 68, 22, 14, 96],
    #[50, 73, 24, 97, 54, 66],
    #[51, 83, 33, 75, 70, 42],
    #[52, 85, 37, 72, 97, 34],
    #[53, 87, 39, 71, 99, 36],
    #[54, 50, 5, 107, 67, 35],
    #[55, 47, 74, 37, 65, 107],
    #[56, 48, 110, 38, 22, 71],
    #[57, 10, 108, 39, 64, 73],
    #[58, 13, 76, 41, 24, 106],
    #[59, 0, 75, 40, 23, 105],
    #[60, 12, 77, 6, 25, 126],
    #[61, 80, 106, 78, 27, 75],
    #[62, 8, 71, 34, 2, 74],
    #[63, 14, 82, 48, 37, 115],
    #[64, 57, 83, 47, 38, 116],
    #[65, 55, 81, 10, 5, 84],
    #[66, 18, 87, 43, 78, 127],
    #[67, 54, 12, 85, 73, 80],
    #[68, 89, 8, 82, 75, 10],
    #[69, 91, 46, 81, 77, 48],
    #[70, 51, 7, 114, 30, 47],
    #[71, 97, 55, 53, 85, 19],
    #[72, 99, 57, 52, 87, 21],
    #[73, 67, 14, 95, 50, 20],
    #[74, 100, 19, 119, 127, 56],
    #[75, 68, 16, 51, 81, 58],
    #[76, 103, 61, 91, 114, 59],
    #[77, 69, 17, 90, 82, 15],
    #[78, 66, 94, 61, 44, 89],
    #[79, 3, 52, 19, 7, 88],
    #[80, 33, 99, 26, 61, 125],
    #[81, 75, 3, 69, 89, 22],
    #[82, 77, 29, 68, 91, 64],
    #[83, 30, 2, 103, 51, 63],
    #[84, 104, 22, 123, 121, 4],
    #[85, 71, 1, 67, 52, 27],
    #[86, 107, 25, 99, 95, 28],
    #[87, 72, 23, 98, 53, 26],
    #[88, 111, 34, 109, 125, 38],
    #[89, 81, 31, 30, 68, 40],
    #[90, 114, 78, 77, 103, 41],
    #[91, 82, 32, 76, 69, 6],
    #[92, 117, 42, 106, 96, 32],
    #[93, 115, 40, 126, 123, 78],
    #[94, 116, 41, 104, 122, 31],
    #[95, 86, 38, 73, 98, 79],
    #[96, 92, 10, 116, 126, 9],
    #[97, 52, 0, 50, 71, 44],
    #[98, 95, 13, 87, 107, 45],
    #[99, 53, 11, 86, 72, 43],
    #[100, 120, 80, 113, 74, 11],
    #[101, 118, 44, 127, 109, 13],
    #[102, 119, 45, 111, 108, 0],
    #[103, 90, 9, 83, 76, 49],
    #[104, 124, 60, 94, 84, 17],
    #[105, 122, 58, 121, 116, 61],
    #[106, 123, 59, 92, 115, 16],
    #[107, 98, 56, 54, 86, 62],
    #[108, 102, 21, 120, 112, 14],
    #[109, 101, 20, 88, 113, 57],
    #[110, 125, 62, 118, 111, 55],
    #[111, 110, 66, 102, 88, 23],
    #[112, 108, 27, 125, 119, 25],
    #[113, 109, 28, 100, 118, 1],
    #[114, 76, 4, 70, 90, 65],
    #[115, 106, 64, 124, 93, 2],
    #[116, 105, 63, 96, 94, 29],
    #[117, 126, 65, 122, 92, 3],
    #[118, 113, 36, 110, 101, 5],
    #[119, 112, 35, 74, 102, 39],
    #[120, 127, 79, 108, 100, 37],
    #[121, 84, 6, 105, 124, 33],
    #[122, 94, 48, 117, 105, 7],
    #[123, 93, 47, 84, 106, 46],
    #[124, 121, 49, 115, 104, 8],
    #[125, 88, 43, 112, 110, 12],
    #[126, 96, 15, 93, 117, 18],
    #[127, 74, 26, 101, 120, 24]] : Array (Array ℕ)).getD k.val #[]).getD j.val 0)
set_option maxHeartbeats 1600000 in
private theorem cert41_7 : ∃ c, c ∈ Subgroup.centralizer (Subgroup.closure (Set.range e41_7) : Set SylowModel) ∧ c ∉ Subgroup.closure (Set.range e41_7) := by
  refine ⟨rootOne ^ 2 * root 2 * root 4 * root 7, centralizes_generators e41_7 _ (by decide +kernel), ?_⟩
  exact outside_of_table e41_7 a41_7 0 next41_7 prev41_7
    (by decide +kernel) (by decide +kernel) (by decide +kernel) _ (by decide +kernel)

private def s42 : Fin 3 → SylowModel := ![root 6, rootOne ^ 3 * root 5 * root 8, root 3 * root 5 * root 8]
set_option maxHeartbeats 1600000 in
private theorem gen42 : Subgroup.closure (Set.range s42) = smallParityCensusNode 42 := by
  rw [node42]
  exact closure_eq_words s42 o42 (![[4, 5, 6], [1], [0]]) (![[2], [1], [0, 2, 1, 1, 2], [0, 1, 1, 2, 1, 2, 1], [0, 1, 1, 2, 1, 1, 2], [0, 1, 1, 1, 0, 1], [0, 2, 0, 2, 2, 2], [2, 2]]) (by decide +kernel) (by decide +kernel)

private def e42_1 : Fin 6 → SylowModel := ![decode 0, decode 1632, decode 296, decode 0, decode 1504, decode 808]
set_option maxHeartbeats 1600000 in
private theorem edgeEq42_1 : binaryFamily s42 (s42 0) (![true, false, false]) = e42_1 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert42_1 : Represented smallParityCensusNode (Subgroup.closure (Set.range e42_1)) := by
  refine ⟨80, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node80]
  exact closure_eq_words _ o80 (![[], [1], [0], [], [4, 5, 1], [0, 4]]) (![[2], [1], [1, 1], [1, 1, 1, 2, 1, 2], [2, 2, 2, 5], [1, 1, 2, 1, 1, 2], [2, 2]]) (by decide +kernel) (by decide +kernel)

private def e42_2 : Fin 6 → SylowModel := ![decode 64, decode 0, decode 296, decode 960, decode 2240, decode 632]
set_option maxHeartbeats 1600000 in
private theorem edgeEq42_2 : binaryFamily s42 (s42 1) (![false, true, false]) = e42_2 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert42_2 : Subgroup.closure (Set.range e42_2) ≤ character.ker := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨j, rfl⟩
  exact (show ∀ j, e42_2 j ∈ character.ker from by decide +kernel) j

private def e42_3 : Fin 6 → SylowModel := ![decode 0, decode 1440, decode 296, decode 0, decode 1568, decode 808]
set_option maxHeartbeats 1600000 in
private theorem edgeEq42_3 : binaryFamily s42 (s42 0) (![true, true, false]) = e42_3 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert42_3 : Represented smallParityCensusNode (Subgroup.closure (Set.range e42_3)) := by
  refine ⟨80, root 2 * root 3 * root 4 * root 7, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node80]
  exact closure_eq_words _ o80 (![[], [3, 1, 4], [0, 4, 5, 6], [], [0, 1, 0], [0, 5, 6]]) (![[1, 1, 4, 1, 2], [2, 2, 2, 4, 2], [2, 1, 1, 2], [1, 1, 2, 1, 5, 4], [2, 2, 2, 5], [1, 1, 2, 1, 1, 2], [2, 2]]) (by decide +kernel) (by decide +kernel)

private def e42_4 : Fin 6 → SylowModel := ![decode 64, decode 1632, decode 0, decode 576, decode 1840, decode 256]
set_option maxHeartbeats 1600000 in
private theorem edgeEq42_4 : binaryFamily s42 (s42 2) (![false, false, true]) = e42_4 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert42_4 : Represented smallParityCensusNode (Subgroup.closure (Set.range e42_4)) := by
  refine ⟨63, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node63]
  exact closure_eq_words _ o63 (![[3, 4, 5], [0], [], [3, 5], [0, 1, 3, 6], [6]]) (![[1], [0, 1, 1, 4, 1], [4, 4, 0], [0, 1, 4, 4, 1], [0, 3], [0, 1, 0, 4, 1, 4], [5]]) (by decide +kernel) (by decide +kernel)

private def e42_5 : Fin 6 → SylowModel := ![decode 0, decode 1632, decode 360, decode 0, decode 1504, decode 872]
set_option maxHeartbeats 1600000 in
private theorem edgeEq42_5 : binaryFamily s42 (s42 0) (![true, false, true]) = e42_5 := by decide +kernel
private def a42_5 (k : Fin 128) : SylowModel :=
  decode ((#[0, 384, 768, 512, 2448, 2368, 464, 640, 896, 256, 1032, 2064, 2704, 2960, 2240, 2624, 2880, 80, 720, 976, 128, 1160, 1800, 1544, 232, 3744, 1968, 1760, 2832, 2576, 2192, 3008, 2752, 2112, 848, 592, 208, 3224, 3784, 1880, 1928, 1672, 1288, 360, 1000, 744, 3616, 3488, 3232, 1840, 1200, 1456, 1632, 1504, 1248, 2320, 2496, 336, 3096, 3992, 3736, 3656, 3528, 3272, 2008, 1112, 1368, 1416, 2552, 2856, 824, 616, 872, 488, 3824, 3360, 3104, 4000, 1072, 1328, 1712, 1376, 1120, 2016, 3864, 3608, 3480, 3400, 3144, 4040, 1240, 1496, 1624, 2168, 2808, 3064, 2728, 2088, 2344, 696, 56, 312, 104, 3696, 3568, 3312, 3872, 1584, 1888, 3352, 3912, 1752, 2936, 2680, 2296, 2472, 2216, 2600, 440, 184, 568, 3440, 3184, 4080, 2424, 2984, 952, 3952] : Array ℕ).getD k.val 0)
private def next42_5 (k : Fin 128) (j : Fin 6) : Fin 128 :=
  Fin.ofNat 128 (((#[#[0, 52, 43, 0, 53, 72],
    #[1, 83, 24, 1, 82, 45],
    #[2, 81, 71, 2, 27, 102],
    #[3, 82, 72, 3, 83, 43],
    #[4, 121, 113, 4, 74, 93],
    #[5, 47, 116, 5, 46, 96],
    #[6, 26, 99, 6, 78, 119],
    #[7, 54, 44, 7, 108, 73],
    #[8, 53, 45, 8, 52, 24],
    #[9, 108, 102, 9, 54, 71],
    #[10, 96, 50, 10, 97, 80],
    #[11, 105, 95, 11, 127, 68],
    #[12, 103, 124, 12, 104, 112],
    #[13, 127, 93, 13, 105, 113],
    #[14, 76, 98, 14, 77, 69],
    #[15, 25, 125, 15, 75, 115],
    #[16, 77, 96, 16, 76, 116],
    #[17, 107, 70, 17, 51, 101],
    #[18, 50, 118, 18, 49, 126],
    #[19, 51, 119, 19, 107, 99],
    #[20, 27, 73, 20, 81, 44],
    #[21, 117, 78, 21, 116, 107],
    #[22, 115, 26, 22, 69, 51],
    #[23, 116, 80, 23, 117, 50],
    #[24, 41, 7, 24, 42, 20],
    #[25, 8, 60, 25, 9, 37],
    #[26, 55, 10, 26, 13, 23],
    #[27, 33, 39, 27, 32, 66],
    #[28, 123, 114, 28, 122, 94],
    #[29, 74, 68, 29, 121, 95],
    #[30, 122, 112, 30, 123, 124],
    #[31, 106, 117, 31, 48, 97],
    #[32, 46, 69, 32, 47, 98],
    #[33, 48, 115, 33, 106, 125],
    #[34, 79, 100, 34, 80, 120],
    #[35, 78, 101, 35, 26, 70],
    #[36, 80, 126, 36, 79, 118],
    #[37, 118, 77, 37, 70, 47],
    #[38, 44, 123, 38, 43, 104],
    #[39, 68, 53, 39, 112, 83],
    #[40, 98, 49, 40, 125, 79],
    #[41, 97, 107, 41, 96, 78],
    #[42, 125, 51, 42, 98, 26],
    #[43, 22, 2, 43, 21, 9],
    #[44, 67, 1, 44, 23, 8],
    #[45, 21, 20, 45, 22, 7],
    #[46, 2, 85, 46, 1, 58],
    #[47, 20, 86, 47, 3, 59],
    #[48, 1, 37, 48, 2, 60],
    #[49, 4, 21, 49, 28, 41],
    #[50, 29, 22, 50, 30, 42],
    #[51, 28, 23, 51, 4, 10],
    #[52, 14, 64, 52, 15, 91],
    #[53, 16, 65, 53, 56, 92],
    #[54, 15, 66, 54, 14, 39],
    #[55, 104, 94, 55, 103, 114],
    #[56, 75, 97, 56, 25, 117],
    #[57, 49, 120, 57, 50, 100],
    #[58, 101, 106, 58, 126, 75],
    #[59, 99, 48, 59, 100, 25],
    #[60, 126, 47, 60, 101, 77],
    #[61, 72, 127, 61, 73, 121],
    #[62, 24, 105, 62, 71, 74],
    #[63, 73, 104, 63, 72, 123],
    #[64, 124, 81, 64, 95, 108],
    #[65, 94, 27, 65, 93, 54],
    #[66, 95, 83, 66, 124, 53],
    #[67, 69, 79, 67, 115, 49],
    #[68, 109, 55, 68, 60, 28],
    #[69, 89, 56, 69, 88, 31],
    #[70, 66, 34, 70, 111, 57],
    #[71, 10, 0, 71, 40, 3],
    #[72, 42, 9, 72, 41, 2],
    #[73, 40, 8, 73, 10, 1],
    #[74, 19, 63, 74, 57, 38],
    #[75, 0, 109, 75, 7, 84],
    #[76, 9, 58, 76, 8, 85],
    #[77, 7, 59, 77, 0, 86],
    #[78, 12, 40, 78, 11, 67],
    #[79, 13, 41, 79, 55, 21],
    #[80, 11, 42, 80, 12, 22],
    #[81, 31, 90, 81, 5, 111],
    #[82, 32, 91, 82, 33, 64],
    #[83, 5, 92, 83, 31, 65],
    #[84, 120, 76, 84, 119, 46],
    #[85, 70, 75, 85, 118, 106],
    #[86, 119, 25, 86, 120, 48],
    #[87, 102, 122, 87, 45, 103],
    #[88, 43, 121, 88, 44, 127],
    #[89, 45, 74, 89, 102, 105],
    #[90, 113, 52, 90, 114, 82],
    #[91, 112, 108, 91, 68, 81],
    #[92, 114, 54, 92, 113, 27],
    #[93, 37, 30, 93, 84, 12],
    #[94, 85, 29, 94, 86, 11],
    #[95, 84, 28, 95, 37, 55],
    #[96, 61, 33, 96, 62, 15],
    #[97, 63, 32, 97, 110, 14],
    #[98, 62, 31, 98, 61, 56],
    #[99, 90, 18, 99, 39, 36],
    #[100, 92, 17, 100, 91, 35],
    #[101, 39, 57, 101, 90, 34],
    #[102, 23, 3, 102, 67, 0],
    #[103, 34, 88, 103, 6, 61],
    #[104, 36, 89, 104, 35, 62],
    #[105, 6, 38, 105, 34, 63],
    #[106, 3, 84, 106, 20, 109],
    #[107, 30, 67, 107, 29, 40],
    #[108, 56, 111, 108, 16, 90],
    #[109, 100, 46, 109, 99, 76],
    #[110, 71, 103, 110, 24, 122],
    #[111, 93, 82, 111, 94, 52],
    #[112, 59, 13, 112, 58, 4],
    #[113, 60, 12, 113, 109, 30],
    #[114, 58, 11, 114, 59, 29],
    #[115, 87, 16, 115, 38, 5],
    #[116, 88, 15, 116, 89, 33],
    #[117, 38, 14, 117, 87, 32],
    #[118, 64, 6, 118, 65, 19],
    #[119, 111, 36, 119, 66, 18],
    #[120, 65, 35, 120, 64, 17],
    #[121, 17, 110, 121, 18, 87],
    #[122, 57, 61, 122, 19, 88],
    #[123, 18, 62, 123, 17, 89],
    #[124, 86, 4, 124, 85, 13],
    #[125, 110, 5, 125, 63, 16],
    #[126, 91, 19, 126, 92, 6],
    #[127, 35, 87, 127, 36, 110]] : Array (Array ℕ)).getD k.val #[]).getD j.val 0)
private def prev42_5 (k : Fin 128) (j : Fin 6) : Fin 128 :=
  Fin.ofNat 128 (((#[#[0, 75, 71, 0, 77, 102],
    #[1, 48, 44, 1, 46, 73],
    #[2, 46, 43, 2, 48, 72],
    #[3, 106, 102, 3, 47, 71],
    #[4, 49, 124, 4, 51, 112],
    #[5, 83, 125, 5, 81, 115],
    #[6, 105, 118, 6, 103, 126],
    #[7, 77, 24, 7, 75, 45],
    #[8, 25, 73, 8, 76, 44],
    #[9, 76, 72, 9, 25, 43],
    #[10, 71, 26, 10, 73, 51],
    #[11, 80, 114, 11, 78, 94],
    #[12, 78, 113, 12, 80, 93],
    #[13, 79, 112, 13, 26, 124],
    #[14, 52, 117, 14, 54, 97],
    #[15, 54, 116, 15, 52, 96],
    #[16, 53, 115, 16, 108, 125],
    #[17, 121, 100, 17, 123, 120],
    #[18, 123, 99, 18, 121, 119],
    #[19, 74, 126, 19, 122, 118],
    #[20, 47, 45, 20, 106, 24],
    #[21, 45, 49, 21, 43, 79],
    #[22, 43, 50, 22, 45, 80],
    #[23, 102, 51, 23, 44, 26],
    #[24, 62, 1, 24, 110, 8],
    #[25, 15, 86, 25, 56, 59],
    #[26, 6, 22, 26, 35, 42],
    #[27, 20, 65, 27, 2, 92],
    #[28, 51, 95, 28, 49, 68],
    #[29, 50, 94, 29, 107, 114],
    #[30, 107, 93, 30, 50, 113],
    #[31, 81, 98, 31, 83, 69],
    #[32, 82, 97, 32, 27, 117],
    #[33, 27, 96, 33, 82, 116],
    #[34, 103, 70, 34, 105, 101],
    #[35, 127, 120, 35, 104, 100],
    #[36, 104, 119, 36, 127, 99],
    #[37, 93, 48, 37, 95, 25],
    #[38, 117, 105, 38, 115, 74],
    #[39, 101, 27, 39, 99, 54],
    #[40, 73, 78, 40, 71, 107],
    #[41, 24, 79, 41, 72, 49],
    #[42, 72, 80, 42, 24, 50],
    #[43, 88, 0, 43, 38, 3],
    #[44, 38, 7, 44, 88, 20],
    #[45, 89, 8, 45, 87, 1],
    #[46, 32, 109, 46, 5, 84],
    #[47, 5, 60, 47, 32, 37],
    #[48, 33, 59, 48, 31, 86],
    #[49, 57, 40, 49, 18, 67],
    #[50, 18, 10, 50, 57, 23],
    #[51, 19, 42, 51, 17, 22],
    #[52, 0, 90, 52, 8, 111],
    #[53, 8, 39, 53, 0, 66],
    #[54, 7, 92, 54, 9, 65],
    #[55, 26, 68, 55, 79, 95],
    #[56, 108, 69, 56, 53, 98],
    #[57, 122, 101, 57, 74, 70],
    #[58, 114, 76, 58, 112, 46],
    #[59, 112, 77, 59, 114, 47],
    #[60, 113, 25, 60, 68, 48],
    #[61, 96, 122, 61, 98, 103],
    #[62, 98, 123, 62, 96, 104],
    #[63, 97, 74, 63, 125, 105],
    #[64, 118, 52, 64, 120, 82],
    #[65, 120, 53, 65, 118, 83],
    #[66, 70, 54, 66, 119, 27],
    #[67, 44, 107, 67, 102, 78],
    #[68, 39, 29, 68, 91, 11],
    #[69, 67, 32, 69, 22, 14],
    #[70, 85, 17, 70, 37, 35],
    #[71, 110, 2, 71, 62, 9],
    #[72, 61, 3, 72, 63, 0],
    #[73, 63, 20, 73, 61, 7],
    #[74, 29, 89, 74, 4, 62],
    #[75, 56, 85, 75, 15, 58],
    #[76, 14, 84, 76, 16, 109],
    #[77, 16, 37, 77, 14, 60],
    #[78, 35, 21, 78, 6, 41],
    #[79, 34, 67, 79, 36, 40],
    #[80, 36, 23, 80, 34, 10],
    #[81, 2, 64, 81, 20, 91],
    #[82, 3, 111, 82, 1, 90],
    #[83, 1, 66, 83, 3, 39],
    #[84, 95, 106, 84, 93, 75],
    #[85, 94, 46, 85, 124, 76],
    #[86, 124, 47, 86, 94, 77],
    #[87, 115, 127, 87, 117, 121],
    #[88, 116, 103, 88, 69, 122],
    #[89, 69, 104, 89, 116, 123],
    #[90, 99, 81, 90, 101, 108],
    #[91, 126, 82, 91, 100, 52],
    #[92, 100, 83, 92, 126, 53],
    #[93, 111, 13, 93, 65, 4],
    #[94, 65, 55, 94, 111, 28],
    #[95, 66, 11, 95, 64, 29],
    #[96, 10, 16, 96, 41, 5],
    #[97, 41, 56, 97, 10, 31],
    #[98, 40, 14, 98, 42, 32],
    #[99, 59, 6, 99, 109, 19],
    #[100, 109, 34, 100, 59, 57],
    #[101, 58, 35, 101, 60, 17],
    #[102, 87, 9, 102, 89, 2],
    #[103, 12, 110, 103, 55, 87],
    #[104, 55, 63, 104, 12, 38],
    #[105, 11, 62, 105, 13, 89],
    #[106, 31, 58, 106, 33, 85],
    #[107, 17, 41, 107, 19, 21],
    #[108, 9, 91, 108, 7, 64],
    #[109, 68, 75, 109, 113, 106],
    #[110, 125, 121, 110, 97, 127],
    #[111, 119, 108, 111, 70, 81],
    #[112, 91, 30, 112, 39, 12],
    #[113, 90, 4, 113, 92, 13],
    #[114, 92, 28, 114, 90, 55],
    #[115, 22, 33, 115, 67, 15],
    #[116, 23, 5, 116, 21, 16],
    #[117, 21, 31, 117, 23, 56],
    #[118, 37, 18, 118, 85, 36],
    #[119, 86, 19, 119, 84, 6],
    #[120, 84, 57, 120, 86, 34],
    #[121, 4, 88, 121, 29, 61],
    #[122, 30, 87, 122, 28, 110],
    #[123, 28, 38, 123, 30, 63],
    #[124, 64, 12, 124, 66, 30],
    #[125, 42, 15, 125, 40, 33],
    #[126, 60, 36, 126, 58, 18],
    #[127, 13, 61, 127, 11, 88]] : Array (Array ℕ)).getD k.val #[]).getD j.val 0)
set_option maxHeartbeats 1600000 in
private theorem cert42_5 : ∃ c, c ∈ Subgroup.centralizer (Subgroup.closure (Set.range e42_5) : Set SylowModel) ∧ c ∉ Subgroup.closure (Set.range e42_5) := by
  refine ⟨rootOne ^ 2 * root 2 * root 6 * root 7, centralizes_generators e42_5 _ (by decide +kernel), ?_⟩
  exact outside_of_table e42_5 a42_5 0 next42_5 prev42_5
    (by decide +kernel) (by decide +kernel) (by decide +kernel) _ (by decide +kernel)

private def e42_6 : Fin 6 → SylowModel := ![decode 64, decode 0, decode 3080, decode 960, decode 2240, decode 1048]
set_option maxHeartbeats 1600000 in
private theorem edgeEq42_6 : binaryFamily s42 (s42 1) (![false, true, true]) = e42_6 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert42_6 : Represented smallParityCensusNode (Subgroup.closure (Set.range e42_6)) := by
  refine ⟨69, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node69]
  exact closure_eq_words _ o69 (![[3, 5], [], [0, 1, 2, 5], [3, 4], [0, 3, 0, 1], [1, 0, 5]]) (![[0, 2, 0, 4, 0], [0, 2, 2, 4], [2, 2], [2, 0, 5], [0, 5, 3, 2], [0, 2, 0, 5], [2, 5]]) (by decide +kernel) (by decide +kernel)

private def e42_7 : Fin 6 → SylowModel := ![decode 0, decode 1440, decode 360, decode 0, decode 1568, decode 872]
set_option maxHeartbeats 1600000 in
private theorem edgeEq42_7 : binaryFamily s42 (s42 0) (![true, true, true]) = e42_7 := by decide +kernel
private def a42_7 (k : Fin 128) : SylowModel :=
  decode ((#[0, 384, 768, 512, 2448, 2368, 464, 640, 896, 256, 1312, 2064, 2704, 2960, 2240, 2624, 2880, 80, 720, 976, 128, 3080, 1176, 1992, 232, 1440, 1568, 1824, 2832, 2576, 2192, 3008, 2752, 2112, 848, 592, 208, 3208, 3848, 3592, 1048, 1944, 1688, 1864, 1224, 1480, 360, 1000, 744, 3120, 3168, 1136, 1696, 1952, 1056, 2320, 2496, 336, 3672, 3976, 3720, 3336, 1816, 1560, 1432, 1096, 1352, 1736, 2552, 2856, 824, 616, 872, 488, 3248, 3888, 3632, 3296, 3936, 3680, 1264, 1904, 1648, 1184, 3800, 3416, 3160, 3464, 1304, 1608, 2168, 2808, 3064, 2728, 2088, 2344, 696, 56, 312, 104, 4016, 3760, 3376, 4064, 3808, 3424, 2032, 1776, 1392, 3544, 3288, 3928, 2936, 2680, 2296, 2472, 2216, 2600, 440, 184, 568, 3504, 3552, 1520, 4056, 2424, 2984, 952] : Array ℕ).getD k.val 0)
private def next42_7 (k : Fin 128) (j : Fin 6) : Fin 128 :=
  Fin.ofNat 128 (((#[#[0, 25, 46, 0, 26, 72],
    #[1, 54, 24, 1, 53, 48],
    #[2, 52, 71, 2, 10, 99],
    #[3, 53, 72, 3, 54, 46],
    #[4, 100, 113, 4, 49, 90],
    #[5, 78, 116, 5, 77, 93],
    #[6, 51, 96, 6, 106, 119],
    #[7, 27, 47, 7, 83, 73],
    #[8, 26, 48, 8, 25, 24],
    #[9, 83, 99, 9, 27, 71],
    #[10, 32, 42, 10, 33, 22],
    #[11, 76, 92, 11, 121, 68],
    #[12, 74, 125, 12, 75, 112],
    #[13, 121, 90, 13, 76, 113],
    #[14, 104, 95, 14, 105, 69],
    #[15, 50, 126, 15, 103, 115],
    #[16, 105, 93, 16, 104, 116],
    #[17, 123, 70, 17, 82, 98],
    #[18, 81, 118, 18, 80, 127],
    #[19, 82, 119, 19, 123, 96],
    #[20, 10, 73, 20, 52, 47],
    #[21, 46, 75, 21, 47, 102],
    #[22, 112, 54, 22, 68, 26],
    #[23, 94, 108, 23, 93, 81],
    #[24, 66, 7, 24, 67, 20],
    #[25, 15, 63, 25, 14, 40],
    #[26, 56, 64, 26, 16, 41],
    #[27, 14, 22, 27, 15, 42],
    #[28, 102, 114, 28, 101, 91],
    #[29, 49, 68, 29, 100, 92],
    #[30, 101, 112, 30, 102, 125],
    #[31, 122, 117, 31, 79, 94],
    #[32, 77, 69, 32, 78, 95],
    #[33, 79, 115, 33, 122, 126],
    #[34, 107, 97, 34, 108, 120],
    #[35, 106, 98, 35, 51, 70],
    #[36, 108, 127, 36, 107, 118],
    #[37, 73, 100, 37, 72, 121],
    #[38, 71, 49, 38, 24, 76],
    #[39, 72, 102, 39, 73, 75],
    #[40, 92, 83, 40, 125, 52],
    #[41, 90, 27, 41, 91, 10],
    #[42, 125, 26, 42, 92, 54],
    #[43, 116, 123, 43, 117, 106],
    #[44, 69, 82, 44, 115, 51],
    #[45, 117, 81, 45, 116, 108],
    #[46, 44, 2, 46, 43, 9],
    #[47, 89, 1, 47, 45, 8],
    #[48, 43, 20, 48, 44, 7],
    #[49, 57, 21, 49, 19, 39],
    #[50, 9, 58, 50, 8, 86],
    #[51, 13, 45, 51, 55, 23],
    #[52, 5, 88, 52, 31, 62],
    #[53, 33, 40, 53, 32, 63],
    #[54, 31, 41, 54, 5, 64],
    #[55, 75, 91, 55, 74, 114],
    #[56, 103, 94, 56, 50, 117],
    #[57, 80, 120, 57, 81, 97],
    #[58, 70, 78, 58, 118, 105],
    #[59, 48, 74, 59, 99, 101],
    #[60, 47, 121, 60, 46, 100],
    #[61, 99, 76, 61, 48, 49],
    #[62, 114, 53, 62, 113, 25],
    #[63, 68, 52, 63, 112, 83],
    #[64, 113, 10, 64, 114, 27],
    #[65, 126, 107, 65, 95, 80],
    #[66, 93, 106, 66, 94, 123],
    #[67, 95, 51, 67, 126, 82],
    #[68, 124, 55, 68, 86, 28],
    #[69, 61, 56, 69, 60, 31],
    #[70, 42, 34, 70, 88, 57],
    #[71, 23, 0, 71, 65, 3],
    #[72, 67, 9, 72, 66, 2],
    #[73, 65, 8, 73, 23, 1],
    #[74, 6, 37, 74, 34, 60],
    #[75, 35, 38, 75, 36, 61],
    #[76, 34, 39, 76, 6, 21],
    #[77, 1, 84, 77, 2, 110],
    #[78, 3, 85, 78, 20, 111],
    #[79, 2, 86, 79, 1, 58],
    #[80, 28, 66, 80, 4, 43],
    #[81, 30, 67, 81, 29, 44],
    #[82, 4, 23, 82, 28, 45],
    #[83, 16, 62, 83, 56, 88],
    #[84, 127, 103, 84, 98, 122],
    #[85, 97, 50, 85, 96, 79],
    #[86, 98, 105, 86, 127, 78],
    #[87, 24, 101, 87, 71, 74],
    #[88, 91, 25, 88, 90, 53],
    #[89, 115, 80, 89, 69, 107],
    #[90, 58, 30, 90, 109, 12],
    #[91, 110, 29, 91, 111, 11],
    #[92, 109, 28, 92, 58, 55],
    #[93, 37, 33, 93, 38, 15],
    #[94, 39, 32, 94, 87, 14],
    #[95, 38, 31, 95, 37, 56],
    #[96, 62, 18, 96, 22, 36],
    #[97, 64, 17, 97, 63, 35],
    #[98, 22, 57, 98, 62, 34],
    #[99, 45, 3, 99, 89, 0],
    #[100, 18, 59, 100, 17, 87],
    #[101, 19, 60, 101, 57, 37],
    #[102, 17, 61, 102, 18, 38],
    #[103, 7, 109, 103, 0, 124],
    #[104, 8, 110, 104, 9, 84],
    #[105, 0, 111, 105, 7, 85],
    #[106, 11, 89, 106, 12, 65],
    #[107, 55, 43, 107, 13, 66],
    #[108, 12, 44, 108, 11, 67],
    #[109, 119, 77, 109, 120, 104],
    #[110, 118, 122, 110, 70, 103],
    #[111, 120, 79, 111, 119, 50],
    #[112, 85, 13, 112, 84, 4],
    #[113, 86, 12, 113, 124, 30],
    #[114, 84, 11, 114, 85, 29],
    #[115, 59, 16, 115, 21, 5],
    #[116, 60, 15, 116, 61, 33],
    #[117, 21, 14, 117, 59, 32],
    #[118, 40, 6, 118, 41, 19],
    #[119, 88, 36, 119, 42, 18],
    #[120, 41, 35, 120, 40, 17],
    #[121, 36, 87, 121, 35, 59],
    #[122, 20, 124, 122, 3, 109],
    #[123, 29, 65, 123, 30, 89],
    #[124, 96, 104, 124, 97, 77],
    #[125, 111, 4, 125, 110, 13],
    #[126, 87, 5, 126, 39, 16],
    #[127, 63, 19, 127, 64, 6]] : Array (Array ℕ)).getD k.val #[]).getD j.val 0)
private def prev42_7 (k : Fin 128) (j : Fin 6) : Fin 128 :=
  Fin.ofNat 128 (((#[#[0, 105, 71, 0, 103, 99],
    #[1, 77, 47, 1, 79, 73],
    #[2, 79, 46, 2, 77, 72],
    #[3, 78, 99, 3, 122, 71],
    #[4, 82, 125, 4, 80, 112],
    #[5, 52, 126, 5, 54, 115],
    #[6, 74, 118, 6, 76, 127],
    #[7, 103, 24, 7, 105, 48],
    #[8, 104, 73, 8, 50, 47],
    #[9, 50, 72, 9, 104, 46],
    #[10, 20, 64, 10, 2, 41],
    #[11, 106, 114, 11, 108, 91],
    #[12, 108, 113, 12, 106, 90],
    #[13, 51, 112, 13, 107, 125],
    #[14, 27, 117, 14, 25, 94],
    #[15, 25, 116, 15, 27, 93],
    #[16, 83, 115, 16, 26, 126],
    #[17, 102, 97, 17, 100, 120],
    #[18, 100, 96, 18, 102, 119],
    #[19, 101, 127, 19, 49, 118],
    #[20, 122, 48, 20, 78, 24],
    #[21, 117, 49, 21, 115, 76],
    #[22, 98, 27, 22, 96, 10],
    #[23, 71, 82, 23, 73, 51],
    #[24, 87, 1, 24, 38, 8],
    #[25, 0, 88, 25, 8, 62],
    #[26, 8, 42, 26, 0, 22],
    #[27, 7, 41, 27, 9, 64],
    #[28, 80, 92, 28, 82, 68],
    #[29, 123, 91, 29, 81, 114],
    #[30, 81, 90, 30, 123, 113],
    #[31, 54, 95, 31, 52, 69],
    #[32, 10, 94, 32, 53, 117],
    #[33, 53, 93, 33, 10, 116],
    #[34, 76, 70, 34, 74, 98],
    #[35, 75, 120, 35, 121, 97],
    #[36, 121, 119, 36, 75, 96],
    #[37, 93, 74, 37, 95, 101],
    #[38, 95, 75, 38, 93, 102],
    #[39, 94, 76, 39, 126, 49],
    #[40, 118, 53, 40, 120, 25],
    #[41, 120, 54, 41, 118, 26],
    #[42, 70, 10, 42, 119, 27],
    #[43, 48, 107, 43, 46, 80],
    #[44, 46, 108, 44, 48, 81],
    #[45, 99, 51, 45, 47, 82],
    #[46, 21, 0, 46, 60, 3],
    #[47, 60, 7, 47, 21, 20],
    #[48, 59, 8, 48, 61, 1],
    #[49, 29, 38, 49, 4, 61],
    #[50, 15, 85, 50, 56, 111],
    #[51, 6, 67, 51, 35, 44],
    #[52, 2, 63, 52, 20, 40],
    #[53, 3, 62, 53, 1, 88],
    #[54, 1, 22, 54, 3, 42],
    #[55, 107, 68, 55, 51, 92],
    #[56, 26, 69, 56, 83, 95],
    #[57, 49, 98, 57, 101, 70],
    #[58, 90, 50, 58, 92, 79],
    #[59, 115, 100, 59, 117, 121],
    #[60, 116, 101, 60, 69, 74],
    #[61, 69, 102, 61, 116, 75],
    #[62, 96, 83, 62, 98, 52],
    #[63, 127, 25, 63, 97, 53],
    #[64, 97, 26, 64, 127, 54],
    #[65, 73, 123, 65, 71, 106],
    #[66, 24, 80, 66, 72, 107],
    #[67, 72, 81, 67, 24, 108],
    #[68, 63, 29, 68, 22, 11],
    #[69, 44, 32, 69, 89, 14],
    #[70, 58, 17, 70, 110, 35],
    #[71, 38, 2, 71, 87, 9],
    #[72, 39, 3, 72, 37, 0],
    #[73, 37, 20, 73, 39, 7],
    #[74, 12, 59, 74, 55, 87],
    #[75, 55, 21, 75, 12, 39],
    #[76, 11, 61, 76, 13, 38],
    #[77, 32, 109, 77, 5, 124],
    #[78, 5, 58, 78, 32, 86],
    #[79, 33, 111, 79, 31, 85],
    #[80, 57, 89, 80, 18, 65],
    #[81, 18, 45, 81, 57, 23],
    #[82, 19, 44, 82, 17, 67],
    #[83, 9, 40, 83, 7, 63],
    #[84, 114, 77, 84, 112, 104],
    #[85, 112, 78, 85, 114, 105],
    #[86, 113, 79, 86, 68, 50],
    #[87, 126, 121, 87, 94, 100],
    #[88, 119, 52, 88, 70, 83],
    #[89, 47, 106, 89, 99, 123],
    #[90, 41, 13, 90, 88, 4],
    #[91, 88, 55, 91, 41, 28],
    #[92, 40, 11, 92, 42, 29],
    #[93, 66, 16, 93, 23, 5],
    #[94, 23, 56, 94, 66, 31],
    #[95, 67, 14, 95, 65, 32],
    #[96, 124, 6, 96, 85, 19],
    #[97, 85, 34, 97, 124, 57],
    #[98, 86, 35, 98, 84, 17],
    #[99, 61, 9, 99, 59, 2],
    #[100, 4, 37, 100, 29, 60],
    #[101, 30, 87, 101, 28, 59],
    #[102, 28, 39, 102, 30, 21],
    #[103, 56, 84, 103, 15, 110],
    #[104, 14, 124, 104, 16, 109],
    #[105, 16, 86, 105, 14, 58],
    #[106, 35, 66, 106, 6, 43],
    #[107, 34, 65, 107, 36, 89],
    #[108, 36, 23, 108, 34, 45],
    #[109, 92, 103, 109, 90, 122],
    #[110, 91, 104, 110, 125, 77],
    #[111, 125, 105, 111, 91, 78],
    #[112, 22, 30, 112, 63, 12],
    #[113, 64, 4, 113, 62, 13],
    #[114, 62, 28, 114, 64, 55],
    #[115, 89, 33, 115, 44, 15],
    #[116, 43, 5, 116, 45, 16],
    #[117, 45, 31, 117, 43, 56],
    #[118, 110, 18, 118, 58, 36],
    #[119, 109, 19, 119, 111, 6],
    #[120, 111, 57, 120, 109, 34],
    #[121, 13, 60, 121, 11, 37],
    #[122, 31, 110, 122, 33, 84],
    #[123, 17, 43, 123, 19, 66],
    #[124, 68, 122, 124, 113, 103],
    #[125, 42, 12, 125, 40, 30],
    #[126, 65, 15, 126, 67, 33],
    #[127, 84, 36, 127, 86, 18]] : Array (Array ℕ)).getD k.val #[]).getD j.val 0)
set_option maxHeartbeats 1600000 in
private theorem cert42_7 : ∃ c, c ∈ Subgroup.centralizer (Subgroup.closure (Set.range e42_7) : Set SylowModel) ∧ c ∉ Subgroup.closure (Set.range e42_7) := by
  refine ⟨rootOne ^ 2 * root 2 * root 6 * root 8, centralizes_generators e42_7 _ (by decide +kernel), ?_⟩
  exact outside_of_table e42_7 a42_7 0 next42_7 prev42_7
    (by decide +kernel) (by decide +kernel) (by decide +kernel) _ (by decide +kernel)

private def s43 : Fin 3 → SylowModel := ![rootOne ^ 3, root 2 * root 3 * root 4 * root 7, root 3]
set_option maxHeartbeats 1600000 in
private theorem gen43 : Subgroup.closure (Set.range s43) = smallParityCensusNode 43 := by
  rw [node43]
  exact closure_eq_words s43 o43 (![[1], [2], [0]]) (![[2], [0], [1], [0, 0], [0, 0, 0, 1, 0, 1, 1, 1], [1, 1, 1, 2, 1, 2, 2, 2], [1, 2, 1, 2, 2, 2], [2, 2]]) (by decide +kernel) (by decide +kernel)

private def e43_1 : Fin 6 → SylowModel := ![decode 0, decode 156, decode 8, decode 2048, decode 396, decode 24]
set_option maxHeartbeats 1600000 in
private theorem edgeEq43_1 : binaryFamily s43 (s43 0) (![true, false, false]) = e43_1 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert43_1 : Subgroup.closure (Set.range e43_1) ≤ character.ker := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨j, rfl⟩
  exact (show ∀ j, e43_1 j ∈ character.ker from by decide +kernel) j

private def e43_2 : Fin 6 → SylowModel := ![decode 1024, decode 0, decode 8, decode 1040, decode 640, decode 136]
set_option maxHeartbeats 1600000 in
private theorem edgeEq43_2 : binaryFamily s43 (s43 1) (![false, true, false]) = e43_2 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert43_2 : Represented smallParityCensusNode (Subgroup.closure (Set.range e43_2)) := by
  refine ⟨75, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node75]
  exact closure_eq_words _ o75 (![[1], [], [0], [1, 3], [4, 6], [0, 4, 5, 6]]) (![[2], [0], [0, 0], [0, 0, 0, 3], [2, 2, 4], [2, 2, 2, 4, 5], [2, 2]]) (by decide +kernel) (by decide +kernel)

private def e43_3 : Fin 6 → SylowModel := ![decode 0, decode 3228, decode 8, decode 2048, decode 1420, decode 24]
set_option maxHeartbeats 1600000 in
private theorem edgeEq43_3 : binaryFamily s43 (s43 0) (![true, true, false]) = e43_3 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert43_3 : Represented smallParityCensusNode (Subgroup.closure (Set.range e43_3)) := by
  refine ⟨75, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node75]
  exact closure_eq_words _ o75 (![[], [1, 2], [0, 5], [2, 3, 5], [4, 1, 5], [0, 3, 4, 5]]) (![[1, 5, 4], [1, 1, 1], [1, 1], [1, 1, 1, 5, 1, 5], [1, 1, 1, 5, 1, 2], [1, 2, 4, 5], [2, 2]]) (by decide +kernel) (by decide +kernel)

private def e43_4 : Fin 6 → SylowModel := ![decode 1024, decode 156, decode 0, decode 1040, decode 28, decode 256]
set_option maxHeartbeats 1600000 in
private theorem edgeEq43_4 : binaryFamily s43 (s43 2) (![false, false, true]) = e43_4 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert43_4 : Represented smallParityCensusNode (Subgroup.closure (Set.range e43_4)) := by
  refine ⟨64, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node64]
  exact closure_eq_words _ o64 (![[0], [1], [], [0, 3, 6], [1, 4, 5], [6]]) (![[0], [1], [0, 0], [0, 0, 0, 3, 5], [1, 1], [1, 4], [5]]) (by decide +kernel) (by decide +kernel)

private def e43_5 : Fin 6 → SylowModel := ![decode 0, decode 156, decode 3080, decode 2048, decode 396, decode 1048]
set_option maxHeartbeats 1600000 in
private theorem edgeEq43_5 : binaryFamily s43 (s43 0) (![true, false, true]) = e43_5 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert43_5 : Represented smallParityCensusNode (Subgroup.closure (Set.range e43_5)) := by
  refine ⟨72, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node72]
  exact closure_eq_words _ o72 (![[], [1, 5, 6], [0, 2, 3, 4, 5], [2, 3, 4, 5], [3, 1, 4], [1, 0, 1, 5]]) (![[2, 3], [1, 1, 5, 4, 2], [2, 2], [1, 1, 1, 2, 1, 5], [1, 1], [1, 2, 4, 5], [2, 5]]) (by decide +kernel) (by decide +kernel)

private def e43_6 : Fin 6 → SylowModel := ![decode 1024, decode 0, decode 916, decode 1040, decode 640, decode 404]
set_option maxHeartbeats 1600000 in
private theorem edgeEq43_6 : binaryFamily s43 (s43 1) (![false, true, true]) = e43_6 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert43_6 : Represented smallParityCensusNode (Subgroup.closure (Set.range e43_6)) := by
  refine ⟨81, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node81]
  exact closure_eq_words _ o81 (![[1], [], [0, 4, 5], [1, 3], [4, 5], [0, 4]]) (![[2, 4], [0], [0, 0], [0, 0, 0, 3], [2, 2, 2, 4, 5], [2, 2, 2, 5], [2, 5]]) (by decide +kernel) (by decide +kernel)

private def e43_7 : Fin 6 → SylowModel := ![decode 0, decode 3228, decode 3080, decode 2048, decode 1420, decode 1048]
set_option maxHeartbeats 1600000 in
private theorem edgeEq43_7 : binaryFamily s43 (s43 0) (![true, true, true]) = e43_7 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert43_7 : Represented smallParityCensusNode (Subgroup.closure (Set.range e43_7)) := by
  refine ⟨82, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node82]
  exact closure_eq_words _ o82 (![[], [2, 3, 1], [0, 1, 1, 1], [2], [1], [1, 0, 5]]) (![[2, 4], [4], [3], [1, 1, 3, 4, 1], [1, 1, 1, 2, 4, 2], [1, 2, 1, 2], [2, 5]]) (by decide +kernel) (by decide +kernel)

private def s44 : Fin 3 → SylowModel := ![rootOne ^ 3, root 2 * root 3 * root 4 * root 7, root 3 * root 6 * root 7 * root 8]
set_option maxHeartbeats 1600000 in
private theorem gen44 : Subgroup.closure (Set.range s44) = smallParityCensusNode 44 := by
  rw [node44]
  exact closure_eq_words s44 o44 (![[1], [2], [0]]) (![[2], [0], [1], [0, 0], [0, 0, 0, 1, 0, 1, 1, 1], [0, 0, 0, 1, 1, 0, 2, 2], [0, 0, 2, 0, 0, 2], [0, 0, 0, 1, 1, 0, 1, 1]]) (by decide +kernel) (by decide +kernel)

private def e44_1 : Fin 6 → SylowModel := ![decode 0, decode 156, decode 456, decode 2048, decode 396, decode 856]
set_option maxHeartbeats 1600000 in
private theorem edgeEq44_1 : binaryFamily s44 (s44 0) (![true, false, false]) = e44_1 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert44_1 : Subgroup.closure (Set.range e44_1) ≤ character.ker := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨j, rfl⟩
  exact (show ∀ j, e44_1 j ∈ character.ker from by decide +kernel) j

private def e44_2 : Fin 6 → SylowModel := ![decode 1024, decode 0, decode 456, decode 1040, decode 640, decode 840]
set_option maxHeartbeats 1600000 in
private theorem edgeEq44_2 : binaryFamily s44 (s44 1) (![false, true, false]) = e44_2 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert44_2 : Represented smallParityCensusNode (Subgroup.closure (Set.range e44_2)) := by
  refine ⟨76, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node76]
  exact closure_eq_words _ o76 (![[1], [], [0], [1, 3], [4, 6], [0, 4, 6]]) (![[2], [0], [0, 0], [0, 0, 0, 3], [0, 0, 0, 4, 0], [0, 0, 0, 2, 3, 5], [0, 0, 0, 4, 0, 4]]) (by decide +kernel) (by decide +kernel)

private def e44_3 : Fin 6 → SylowModel := ![decode 0, decode 3228, decode 456, decode 2048, decode 1420, decode 856]
set_option maxHeartbeats 1600000 in
private theorem edgeEq44_3 : binaryFamily s44 (s44 0) (![true, true, false]) = e44_3 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert44_3 : Represented smallParityCensusNode (Subgroup.closure (Set.range e44_3)) := by
  refine ⟨76, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node76]
  exact closure_eq_words _ o76 (![[], [1, 2], [0, 5], [2, 3, 5], [4, 1, 5], [0, 3, 6]]) (![[2, 2, 3, 2, 3], [1, 1, 1], [1, 1], [2, 5], [1, 2, 2, 4], [2, 3, 2, 3], [1, 1, 4, 4]]) (by decide +kernel) (by decide +kernel)

private def e44_4 : Fin 6 → SylowModel := ![decode 1024, decode 156, decode 0, decode 1680, decode 540, decode 768]
set_option maxHeartbeats 1600000 in
private theorem edgeEq44_4 : binaryFamily s44 (s44 2) (![false, false, true]) = e44_4 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert44_4 : Represented smallParityCensusNode (Subgroup.closure (Set.range e44_4)) := by
  refine ⟨64, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node64]
  exact closure_eq_words _ o64 (![[0], [1], [], [0, 3, 4], [1, 4], [5, 6]]) (![[0], [1], [0, 0], [0, 0, 0, 3, 1, 1], [1, 1], [0, 0, 3, 3, 5], [0, 0, 3, 3]]) (by decide +kernel) (by decide +kernel)

private def e44_5 : Fin 6 → SylowModel := ![decode 0, decode 156, decode 3528, decode 2048, decode 396, decode 1880]
set_option maxHeartbeats 1600000 in
private theorem edgeEq44_5 : binaryFamily s44 (s44 0) (![true, false, true]) = e44_5 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert44_5 : Represented smallParityCensusNode (Subgroup.closure (Set.range e44_5)) := by
  refine ⟨72, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node72]
  exact closure_eq_words _ o72 (![[], [1, 5, 6], [0, 2, 6], [2, 3, 5], [3, 1, 4, 5], [0, 5, 6]]) (![[1, 2, 2, 2, 4], [2, 1, 3, 2], [2, 2], [1, 4], [1, 1], [2, 5], [1, 1, 4, 4]]) (by decide +kernel) (by decide +kernel)

private def e44_6 : Fin 6 → SylowModel := ![decode 1024, decode 0, decode 84, decode 1040, decode 640, decode 84]
set_option maxHeartbeats 1600000 in
private theorem edgeEq44_6 : binaryFamily s44 (s44 1) (![false, true, true]) = e44_6 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert44_6 : Represented smallParityCensusNode (Subgroup.closure (Set.range e44_6)) := by
  refine ⟨82, root 1 * root 2 * root 4 * root 6 * root 7 * root 9, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node82]
  exact closure_eq_words _ o82 (![[3, 1, 5], [], [0, 4], [0, 1, 0], [4], [0, 4]]) (![[2, 4], [2, 2, 3, 4], [0, 2, 2, 3], [0, 0, 0, 3, 4], [4], [0, 0, 2, 0, 0, 2], [0, 0, 0, 4, 0, 4]]) (by decide +kernel) (by decide +kernel)

private def e44_7 : Fin 6 → SylowModel := ![decode 0, decode 3228, decode 3528, decode 2048, decode 1420, decode 1880]
set_option maxHeartbeats 1600000 in
private theorem edgeEq44_7 : binaryFamily s44 (s44 0) (![true, true, true]) = e44_7 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert44_7 : Represented smallParityCensusNode (Subgroup.closure (Set.range e44_7)) := by
  refine ⟨81, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node81]
  exact closure_eq_words _ o81 (![[], [1, 2], [0, 1, 2, 5], [2, 3, 5], [1, 4], [0, 1, 5]]) (![[1, 2, 2, 3, 2, 3], [1, 1, 1], [1, 1], [2, 3, 2], [1, 4], [2, 2, 4, 4], [1, 1, 4, 4]]) (by decide +kernel) (by decide +kernel)

private def s45 : Fin 4 → SylowModel := ![rootOne ^ 3, root 4 * root 7 * root 8, root 6, root 2 * root 4 * root 8]
set_option maxHeartbeats 1600000 in
private theorem gen45 : Subgroup.closure (Set.range s45) = smallParityCensusNode 45 := by
  rw [node45]
  exact closure_eq_words s45 o45 (![[1], [4, 5, 7], [2, 5, 7], [0]]) (![[3], [0], [0, 0, 0, 2, 0, 3, 3], [0, 0], [0, 0, 0, 2, 0, 1, 2, 3, 3], [0, 0, 2, 0, 2, 0, 3, 3], [1, 3, 1, 3], [0, 0, 0, 1, 0, 1]]) (by decide +kernel) (by decide +kernel)

private def e45_1 : Fin 8 → SylowModel := ![decode 0, decode 400, decode 64, decode 276, decode 2048, decode 144, decode 960, decode 276]
set_option maxHeartbeats 1600000 in
private theorem edgeEq45_1 : binaryFamily s45 (s45 0) (![true, false, false, false]) = e45_1 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert45_1 : Subgroup.closure (Set.range e45_1) ≤ character.ker := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨j, rfl⟩
  exact (show ∀ j, e45_1 j ∈ character.ker from by decide +kernel) j

private def e45_2 : Fin 8 → SylowModel := ![decode 1024, decode 0, decode 64, decode 276, decode 1280, decode 0, decode 64, decode 20]
set_option maxHeartbeats 1600000 in
private theorem edgeEq45_2 : binaryFamily s45 (s45 1) (![false, true, false, false]) = e45_2 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert45_2 : Represented smallParityCensusNode (Subgroup.closure (Set.range e45_2)) := by
  refine ⟨83, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node83]
  exact closure_eq_words _ o83 (![[1], [], [2, 4, 5, 6], [0], [1, 6], [], [2, 4, 5, 6], [0, 6]]) (![[3], [0], [0, 0, 0, 2, 0, 3, 3], [0, 0], [0, 0, 0, 2, 4, 2], [3, 3], [0, 0, 0, 4]]) (by decide +kernel) (by decide +kernel)

private def e45_3 : Fin 8 → SylowModel := ![decode 0, decode 3472, decode 64, decode 276, decode 2048, decode 1168, decode 960, decode 276]
set_option maxHeartbeats 1600000 in
private theorem edgeEq45_3 : binaryFamily s45 (s45 0) (![true, true, false, false]) = e45_3 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert45_3 : Represented smallParityCensusNode (Subgroup.closure (Set.range e45_3)) := by
  refine ⟨83, root 2 * root 3 * root 4 * root 7, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node83]
  exact closure_eq_words _ o83 (![[], [3, 4, 1, 5], [2, 4], [0, 4, 5], [3], [1, 4, 5], [2], [0, 4, 5]]) (![[2, 3, 3, 3, 6], [2, 3, 5, 2, 3], [6], [4], [2, 6], [3, 3], [1, 1, 4]]) (by decide +kernel) (by decide +kernel)

private def e45_4 : Fin 8 → SylowModel := ![decode 1024, decode 400, decode 0, decode 276, decode 1920, decode 400, decode 0, decode 276]
set_option maxHeartbeats 1600000 in
private theorem edgeEq45_4 : binaryFamily s45 (s45 2) (![false, false, true, false]) = e45_4 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert45_4 : Represented smallParityCensusNode (Subgroup.closure (Set.range e45_4)) := by
  refine ⟨81, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node81]
  exact closure_eq_words _ o81 (![[1], [3, 4, 6], [], [0], [1, 4, 5], [3, 4, 6], [], [0]]) (![[3], [0], [0, 0], [0, 0, 0, 3, 1, 3, 4], [0, 0, 3, 3, 4, 0], [1, 3, 1, 3], [0, 0, 4, 4]]) (by decide +kernel) (by decide +kernel)

private def e45_5 : Fin 8 → SylowModel := ![decode 0, decode 400, decode 3136, decode 276, decode 2048, decode 144, decode 1984, decode 276]
set_option maxHeartbeats 1600000 in
private theorem edgeEq45_5 : binaryFamily s45 (s45 0) (![true, false, true, false]) = e45_5 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert45_5 : Represented smallParityCensusNode (Subgroup.closure (Set.range e45_5)) := by
  refine ⟨81, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node81]
  exact closure_eq_words _ o81 (![[], [3, 4, 5], [0, 0, 1, 2, 3], [0, 4, 5], [2, 4, 5], [0, 0, 3, 4], [0, 0, 1, 3], [0, 4, 5]]) (![[2, 2, 3, 4], [1, 3, 3, 4, 2], [2, 2], [1, 2, 2, 4], [2, 3, 3, 4, 2], [1, 3, 1, 3], [1, 5]]) (by decide +kernel) (by decide +kernel)

private def e45_6 : Fin 8 → SylowModel := ![decode 1024, decode 0, decode 464, decode 276, decode 1280, decode 0, decode 464, decode 20]
set_option maxHeartbeats 1600000 in
private theorem edgeEq45_6 : binaryFamily s45 (s45 1) (![false, true, true, false]) = e45_6 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert45_6 : Represented smallParityCensusNode (Subgroup.closure (Set.range e45_6)) := by
  refine ⟨84, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node84]
  exact closure_eq_words _ o84 (![[1], [], [2], [0], [1, 6], [], [2], [0, 6]]) (![[3], [0], [2], [0, 0], [0, 0, 0, 2, 0, 2], [3, 3], [0, 0, 0, 4]]) (by decide +kernel) (by decide +kernel)

private def e45_7 : Fin 8 → SylowModel := ![decode 0, decode 3472, decode 3136, decode 276, decode 2048, decode 1168, decode 1984, decode 276]
set_option maxHeartbeats 1600000 in
private theorem edgeEq45_7 : binaryFamily s45 (s45 0) (![true, true, true, false]) = e45_7 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert45_7 : Represented smallParityCensusNode (Subgroup.closure (Set.range e45_7)) := by
  refine ⟨84, root 2 * root 3 * root 4 * root 7, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node84]
  exact closure_eq_words _ o84 (![[], [3, 4, 1, 5], [1, 3, 2], [0, 4, 5], [3], [1, 4, 5], [2, 1], [0, 4, 5]]) (![[2, 3, 3, 3, 4, 2], [1, 2, 2, 3, 3], [1, 3, 3, 6], [4], [2, 4, 2], [3, 3], [1, 1, 4]]) (by decide +kernel) (by decide +kernel)

private def e45_8 : Fin 8 → SylowModel := ![decode 1024, decode 400, decode 64, decode 0, decode 1024, decode 144, decode 64, decode 768]
set_option maxHeartbeats 1600000 in
private theorem edgeEq45_8 : binaryFamily s45 (s45 3) (![false, false, false, true]) = e45_8 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert45_8 : Represented smallParityCensusNode (Subgroup.closure (Set.range e45_8)) := by
  refine ⟨61, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node61]
  exact closure_eq_words _ o61 (![[0], [1, 4, 5, 6], [3, 4, 5], [], [0], [1, 4, 5], [3, 4, 5], [4, 6]]) (![[0], [0, 0, 0, 1, 2, 0, 2, 7], [0, 0], [0, 0, 0, 2, 0, 7], [1, 5, 7], [0, 0, 2, 0, 2, 0], [1, 5]]) (by decide +kernel) (by decide +kernel)

private def e45_9 : Fin 8 → SylowModel := ![decode 0, decode 400, decode 64, decode 3348, decode 2048, decode 144, decode 960, decode 1300]
set_option maxHeartbeats 1600000 in
private theorem edgeEq45_9 : binaryFamily s45 (s45 0) (![true, false, false, true]) = e45_9 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert45_9 : Represented smallParityCensusNode (Subgroup.closure (Set.range e45_9)) := by
  refine ⟨69, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node69]
  exact closure_eq_words _ o69 (![[], [1, 5, 6], [3, 4, 5], [0, 1, 2, 4, 5], [2, 4, 6], [1, 5], [3, 4], [1, 0, 5]]) (![[1, 7], [2, 5, 6], [3, 3], [3, 2, 7], [1, 3, 5, 7], [2, 6], [1, 5]]) (by decide +kernel) (by decide +kernel)

private def e45_10 : Fin 8 → SylowModel := ![decode 1024, decode 0, decode 64, decode 132, decode 1280, decode 0, decode 64, decode 388]
set_option maxHeartbeats 1600000 in
private theorem edgeEq45_10 : binaryFamily s45 (s45 1) (![false, true, false, true]) = e45_10 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert45_10 : Represented smallParityCensusNode (Subgroup.closure (Set.range e45_10)) := by
  refine ⟨85, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node85]
  exact closure_eq_words _ o85 (![[1], [], [0, 0, 2, 4], [0, 0, 0, 4], [1, 6], [], [0, 0, 2, 4], [0, 4, 5]]) (![[0, 0, 0, 2, 0, 2, 3, 3, 7], [0], [0, 0, 0, 2, 0, 3, 7], [0, 0], [0, 0, 0, 2, 4, 2], [3, 7], [0, 0, 0, 4]]) (by decide +kernel) (by decide +kernel)

private def e45_11 : Fin 8 → SylowModel := ![decode 0, decode 3472, decode 64, decode 3348, decode 2048, decode 1168, decode 960, decode 1300]
set_option maxHeartbeats 1600000 in
private theorem edgeEq45_11 : binaryFamily s45 (s45 0) (![true, true, false, true]) = e45_11 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert45_11 : Represented smallParityCensusNode (Subgroup.closure (Set.range e45_11)) := by
  refine ⟨85, root 2 * root 3 * root 4 * root 7, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node85]
  exact closure_eq_words _ o85 (![[], [3, 4, 1, 5], [2, 4], [0, 3, 4, 1, 5], [3], [1, 4, 5], [2], [0, 4, 1, 5]]) (![[3, 5], [1, 2, 3, 2, 3], [6], [4], [2, 6], [3, 7], [1, 1, 4]]) (by decide +kernel) (by decide +kernel)

private def e45_12 : Fin 8 → SylowModel := ![decode 1024, decode 400, decode 0, decode 340, decode 1920, decode 400, decode 0, decode 340]
set_option maxHeartbeats 1600000 in
private theorem edgeEq45_12 : binaryFamily s45 (s45 2) (![false, false, true, true]) = e45_12 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert45_12 : Represented smallParityCensusNode (Subgroup.closure (Set.range e45_12)) := by
  refine ⟨82, root 1 * root 2 * root 4 * root 6 * root 7 * root 9, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node82]
  exact closure_eq_words _ o82 (![[3, 1, 5], [0, 0, 3], [], [0, 4, 6], [0, 1, 0, 3], [0, 0, 3], [], [0, 4, 6]]) (![[0, 0, 3, 0, 4], [0, 1], [0, 4, 1], [1, 3, 3], [0, 0, 0, 4], [1, 3, 1, 3], [0, 0, 4, 4]]) (by decide +kernel) (by decide +kernel)

private def e45_13 : Fin 8 → SylowModel := ![decode 0, decode 400, decode 3136, decode 3348, decode 2048, decode 144, decode 1984, decode 1300]
set_option maxHeartbeats 1600000 in
private theorem edgeEq45_13 : binaryFamily s45 (s45 0) (![true, false, true, true]) = e45_13 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert45_13 : Represented smallParityCensusNode (Subgroup.closure (Set.range e45_13)) := by
  refine ⟨82, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node82]
  exact closure_eq_words _ o82 (![[], [3], [1, 1, 1, 6], [1, 0, 2, 3], [1, 1, 4], [3, 6], [1, 6], [1, 0, 5]]) (![[2, 3, 3, 3], [1, 5, 6], [3, 3, 5], [1], [2, 2, 4], [1, 3, 5, 7], [1, 5]]) (by decide +kernel) (by decide +kernel)

private def e45_14 : Fin 8 → SylowModel := ![decode 1024, decode 0, decode 464, decode 132, decode 1280, decode 0, decode 464, decode 388]
set_option maxHeartbeats 1600000 in
private theorem edgeEq45_14 : binaryFamily s45 (s45 1) (![false, true, true, true]) = e45_14 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert45_14 : Represented smallParityCensusNode (Subgroup.closure (Set.range e45_14)) := by
  refine ⟨86, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node86]
  exact closure_eq_words _ o86 (![[1], [], [2], [0, 0, 0, 4], [1, 6], [], [2], [0, 4, 5]]) (![[0, 0, 0, 2, 0, 2, 3, 3, 3], [0], [2], [0, 0], [0, 0, 0, 2, 0, 2], [3, 7], [0, 0, 0, 4]]) (by decide +kernel) (by decide +kernel)

private def e45_15 : Fin 8 → SylowModel := ![decode 0, decode 3472, decode 3136, decode 3348, decode 2048, decode 1168, decode 1984, decode 1300]
set_option maxHeartbeats 1600000 in
private theorem edgeEq45_15 : binaryFamily s45 (s45 0) (![true, true, true, true]) = e45_15 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert45_15 : Represented smallParityCensusNode (Subgroup.closure (Set.range e45_15)) := by
  refine ⟨86, root 2 * root 3 * root 4 * root 7, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node86]
  exact closure_eq_words _ o86 (![[], [3, 4, 1, 5], [1, 3, 2], [0, 3, 4, 1, 5], [3], [1, 4, 5], [2, 1], [0, 4, 1, 5]]) (![[3, 5], [1, 2, 2, 3, 7], [1, 3, 7, 6], [4], [2, 4, 2], [3, 7], [1, 1, 4]]) (by decide +kernel) (by decide +kernel)

private def s46 : Fin 3 → SylowModel := ![rootOne ^ 3, root 4 * root 7 * root 8, root 2 * root 4 * root 5 * root 9]
set_option maxHeartbeats 1600000 in
private theorem gen46 : Subgroup.closure (Set.range s46) = smallParityCensusNode 46 := by
  rw [node46]
  exact closure_eq_words s46 o46 (![[1], [3, 5, 6], [0]]) (![[2], [0], [0, 0], [0, 0, 2, 0, 0, 1, 2], [0, 2, 0, 2, 0, 0], [0, 2, 0, 0, 2, 0], [1, 2, 1, 2], [2, 2]]) (by decide +kernel) (by decide +kernel)

private def e46_1 : Fin 6 → SylowModel := ![decode 0, decode 400, decode 564, decode 2048, decode 144, decode 372]
set_option maxHeartbeats 1600000 in
private theorem edgeEq46_1 : binaryFamily s46 (s46 0) (![true, false, false]) = e46_1 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert46_1 : Subgroup.closure (Set.range e46_1) ≤ character.ker := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨j, rfl⟩
  exact (show ∀ j, e46_1 j ∈ character.ker from by decide +kernel) j

private def e46_2 : Fin 6 → SylowModel := ![decode 1024, decode 0, decode 564, decode 1280, decode 0, decode 308]
set_option maxHeartbeats 1600000 in
private theorem edgeEq46_2 : binaryFamily s46 (s46 1) (![false, true, false]) = e46_2 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert46_2 : Represented smallParityCensusNode (Subgroup.closure (Set.range e46_2)) := by
  refine ⟨87, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node87]
  exact closure_eq_words _ o87 (![[1], [], [0], [1, 6], [], [0, 4]]) (![[2], [0], [0, 0], [0, 0, 0, 2, 3, 2], [2, 2, 2, 5], [0, 0, 2, 0, 3, 2], [2, 2]]) (by decide +kernel) (by decide +kernel)

private def e46_3 : Fin 6 → SylowModel := ![decode 0, decode 3472, decode 564, decode 2048, decode 1168, decode 372]
set_option maxHeartbeats 1600000 in
private theorem edgeEq46_3 : binaryFamily s46 (s46 0) (![true, true, false]) = e46_3 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert46_3 : Represented smallParityCensusNode (Subgroup.closure (Set.range e46_3)) := by
  refine ⟨87, root 2 * root 3 * root 4 * root 7, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node87]
  exact closure_eq_words _ o87 (![[], [2, 4, 5, 1], [0, 5, 6], [2], [1, 4, 5], [0, 3, 4, 6]]) (![[1, 1, 2, 3], [2, 4, 5], [3], [1, 2, 4, 2], [1, 2, 1, 5, 3], [3, 5, 3, 5], [2, 2]]) (by decide +kernel) (by decide +kernel)

private def e46_4 : Fin 6 → SylowModel := ![decode 1024, decode 400, decode 0, decode 1856, decode 656, decode 256]
set_option maxHeartbeats 1600000 in
private theorem edgeEq46_4 : binaryFamily s46 (s46 2) (![false, false, true]) = e46_4 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert46_4 : Represented smallParityCensusNode (Subgroup.closure (Set.range e46_4)) := by
  refine ⟨61, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node61]
  exact closure_eq_words _ o61 (![[0], [1, 4, 5, 6], [], [0, 3], [1, 5], [6]]) (![[0], [0, 0, 3, 3, 4], [0, 0], [0, 0, 0, 3], [1, 4, 5], [0, 0, 3, 3], [5]]) (by decide +kernel) (by decide +kernel)

private def e46_5 : Fin 6 → SylowModel := ![decode 0, decode 400, decode 3636, decode 2048, decode 144, decode 1396]
set_option maxHeartbeats 1600000 in
private theorem edgeEq46_5 : binaryFamily s46 (s46 0) (![true, false, true]) = e46_5 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert46_5 : Represented smallParityCensusNode (Subgroup.closure (Set.range e46_5)) := by
  refine ⟨71, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node71]
  exact closure_eq_words _ o71 (![[], [1, 5, 6], [1, 2, 0, 3], [2, 4, 6], [1, 5], [5, 0, 1]]) (![[5, 1], [1, 2, 3, 5, 3], [1, 2, 1, 5, 3], [3, 2, 2], [1, 2, 4, 5], [3, 5, 3, 2], [1, 4]]) (by decide +kernel) (by decide +kernel)

private def e46_6 : Fin 6 → SylowModel := ![decode 1024, decode 0, decode 420, decode 1280, decode 0, decode 676]
set_option maxHeartbeats 1600000 in
private theorem edgeEq46_6 : binaryFamily s46 (s46 1) (![false, true, true]) = e46_6 := by decide +kernel
private def a46_6 (k : Fin 128) : SylowModel :=
  decode ((#[0, 1024, 2048, 64, 384, 768, 512, 3072, 1984, 1152, 1792, 1536, 2368, 2432, 2816, 2560, 448, 832, 576, 640, 896, 256, 3776, 3200, 3840, 3584, 1856, 1216, 1472, 1920, 1664, 1280, 2240, 2624, 2880, 2688, 2944, 2304, 704, 960, 320, 128, 1700, 228, 3648, 3520, 3264, 3968, 3712, 3328, 1088, 1344, 1728, 1408, 3008, 2752, 2112, 2176, 192, 3364, 1380, 1572, 1444, 1188, 2660, 164, 356, 996, 740, 3392, 3136, 4032, 3456, 1600, 2496, 4068, 3492, 3620, 3876, 1508, 1636, 1892, 1316, 1060, 1956, 2852, 3044, 2404, 2148, 292, 932, 676, 612, 868, 484, 3904, 3940, 3300, 3556, 3748, 4004, 3108, 1764, 2020, 1124, 1828, 2724, 2084, 2340, 2276, 2532, 2916, 548, 804, 420, 100, 3172, 3428, 3812, 3236, 1252, 2468, 2212, 2596, 2788, 36, 3684, 2980] : Array ℕ).getD k.val 0)
private def next46_6 (k : Fin 128) (j : Fin 6) : Fin 128 :=
  Fin.ofNat 128 (((#[#[1, 0, 114, 31, 0, 91],
    #[2, 1, 103, 37, 1, 120],
    #[7, 2, 123, 49, 2, 108],
    #[50, 3, 94, 51, 3, 68],
    #[53, 4, 125, 9, 4, 113],
    #[10, 5, 91, 11, 5, 114],
    #[11, 6, 90, 10, 6, 65],
    #[0, 7, 117, 21, 7, 126],
    #[54, 8, 83, 55, 8, 105],
    #[57, 9, 81, 13, 9, 104],
    #[14, 10, 120, 15, 10, 103],
    #[15, 11, 79, 14, 11, 102],
    #[69, 12, 111, 70, 12, 88],
    #[72, 13, 127, 23, 13, 122],
    #[24, 14, 108, 25, 14, 123],
    #[25, 15, 107, 24, 15, 85],
    #[28, 16, 115, 27, 16, 93],
    #[26, 17, 68, 73, 17, 94],
    #[73, 18, 67, 26, 18, 43],
    #[30, 19, 113, 29, 19, 125],
    #[29, 20, 112, 30, 20, 89],
    #[31, 21, 65, 1, 21, 90],
    #[38, 22, 100, 39, 22, 119],
    #[41, 23, 98, 4, 23, 118],
    #[5, 24, 126, 6, 24, 117],
    #[6, 25, 96, 5, 25, 116],
    #[34, 26, 63, 33, 26, 84],
    #[32, 27, 105, 74, 27, 83],
    #[74, 28, 61, 32, 28, 82],
    #[36, 29, 104, 35, 29, 81],
    #[35, 30, 60, 36, 30, 80],
    #[37, 31, 102, 2, 31, 79],
    #[46, 32, 124, 45, 32, 110],
    #[44, 33, 88, 95, 33, 111],
    #[95, 34, 87, 44, 34, 64],
    #[48, 35, 122, 47, 35, 127],
    #[47, 36, 121, 48, 36, 106],
    #[49, 37, 85, 7, 37, 107],
    #[52, 38, 93, 8, 38, 115],
    #[8, 39, 92, 52, 39, 66],
    #[51, 40, 43, 50, 40, 67],
    #[9, 41, 89, 53, 41, 112],
    #[106, 42, 26, 127, 42, 50],
    #[120, 43, 17, 79, 43, 3],
    #[18, 44, 78, 17, 44, 101],
    #[16, 45, 119, 58, 45, 100],
    #[58, 46, 76, 16, 46, 99],
    #[20, 47, 118, 19, 47, 98],
    #[19, 48, 75, 20, 48, 97],
    #[21, 49, 116, 0, 49, 96],
    #[56, 50, 84, 12, 50, 63],
    #[12, 51, 42, 56, 51, 62],
    #[55, 52, 82, 54, 52, 61],
    #[13, 53, 80, 57, 53, 60],
    #[71, 54, 110, 22, 54, 124],
    #[22, 55, 109, 71, 55, 86],
    #[70, 56, 64, 69, 56, 87],
    #[23, 57, 106, 72, 57, 121],
    #[27, 58, 66, 28, 58, 92],
    #[89, 59, 44, 125, 59, 69],
    #[87, 60, 9, 88, 60, 29],
    #[123, 61, 8, 85, 61, 27],
    #[121, 62, 50, 122, 62, 26],
    #[122, 63, 51, 121, 63, 73],
    #[126, 64, 33, 96, 64, 12],
    #[63, 65, 5, 62, 65, 0],
    #[60, 66, 38, 104, 66, 16],
    #[103, 67, 3, 102, 67, 17],
    #[102, 68, 40, 103, 68, 18],
    #[40, 69, 101, 3, 69, 78],
    #[3, 70, 59, 40, 70, 77],
    #[39, 71, 99, 38, 71, 76],
    #[4, 72, 97, 41, 72, 75],
    #[33, 73, 62, 34, 73, 42],
    #[45, 74, 86, 46, 74, 109],
    #[67, 75, 23, 68, 75, 47],
    #[114, 76, 22, 65, 76, 45],
    #[112, 77, 69, 113, 77, 44],
    #[113, 78, 70, 112, 78, 95],
    #[110, 79, 1, 109, 79, 10],
    #[64, 80, 29, 111, 80, 9],
    #[111, 81, 30, 64, 81, 53],
    #[108, 82, 27, 107, 82, 8],
    #[107, 83, 28, 108, 83, 52],
    #[127, 84, 73, 106, 84, 51],
    #[78, 85, 14, 77, 85, 2],
    #[75, 86, 54, 118, 86, 32],
    #[117, 87, 12, 116, 87, 33],
    #[116, 88, 56, 117, 88, 34],
    #[82, 89, 19, 83, 89, 4],
    #[84, 90, 0, 42, 90, 5],
    #[42, 91, 21, 84, 91, 6],
    #[80, 92, 16, 81, 92, 38],
    #[81, 93, 58, 80, 93, 39],
    #[79, 94, 18, 120, 94, 40],
    #[17, 95, 77, 18, 95, 59],
    #[93, 96, 7, 92, 96, 24],
    #[43, 97, 47, 94, 97, 23],
    #[94, 98, 48, 43, 98, 72],
    #[91, 99, 45, 90, 99, 22],
    #[90, 100, 46, 91, 100, 71],
    #[125, 101, 95, 89, 101, 70],
    #[124, 102, 10, 86, 102, 1],
    #[86, 103, 11, 124, 103, 31],
    #[88, 104, 53, 87, 104, 30],
    #[85, 105, 52, 123, 105, 28],
    #[99, 106, 35, 100, 106, 13],
    #[101, 107, 2, 59, 107, 14],
    #[59, 108, 37, 101, 108, 15],
    #[97, 109, 32, 98, 109, 54],
    #[98, 110, 74, 97, 110, 55],
    #[96, 111, 34, 126, 111, 56],
    #[61, 112, 4, 105, 112, 19],
    #[105, 113, 41, 61, 113, 20],
    #[62, 114, 6, 63, 114, 21],
    #[104, 115, 39, 60, 115, 58],
    #[115, 116, 24, 66, 116, 7],
    #[66, 117, 25, 115, 117, 49],
    #[68, 118, 72, 67, 118, 48],
    #[65, 119, 71, 114, 119, 46],
    #[109, 120, 31, 110, 120, 11],
    #[76, 121, 13, 119, 121, 35],
    #[119, 122, 57, 76, 122, 36],
    #[77, 123, 15, 78, 123, 37],
    #[118, 124, 55, 75, 124, 74],
    #[83, 125, 20, 82, 125, 41],
    #[92, 126, 49, 93, 126, 25],
    #[100, 127, 36, 99, 127, 57]] : Array (Array ℕ)).getD k.val #[]).getD j.val 0)
private def prev46_6 (k : Fin 128) (j : Fin 6) : Fin 128 :=
  Fin.ofNat 128 (((#[#[7, 0, 90, 49, 0, 65],
    #[0, 1, 79, 21, 1, 102],
    #[1, 2, 107, 31, 2, 85],
    #[70, 3, 67, 69, 3, 43],
    #[72, 4, 112, 23, 4, 89],
    #[24, 5, 65, 25, 5, 90],
    #[25, 6, 114, 24, 6, 91],
    #[2, 7, 96, 37, 7, 116],
    #[39, 8, 61, 38, 8, 82],
    #[41, 9, 60, 4, 9, 80],
    #[5, 10, 102, 6, 10, 79],
    #[6, 11, 103, 5, 11, 120],
    #[51, 12, 87, 50, 12, 64],
    #[53, 13, 121, 9, 13, 106],
    #[10, 14, 85, 11, 14, 107],
    #[11, 15, 123, 10, 15, 108],
    #[45, 16, 92, 46, 16, 66],
    #[95, 17, 43, 44, 17, 67],
    #[44, 18, 94, 95, 18, 68],
    #[48, 19, 89, 47, 19, 112],
    #[47, 20, 125, 48, 20, 113],
    #[49, 21, 91, 7, 21, 114],
    #[55, 22, 76, 54, 22, 99],
    #[57, 23, 75, 13, 23, 97],
    #[14, 24, 116, 15, 24, 96],
    #[15, 25, 117, 14, 25, 126],
    #[17, 26, 42, 18, 26, 62],
    #[58, 27, 82, 16, 27, 61],
    #[16, 28, 83, 58, 28, 105],
    #[20, 29, 80, 19, 29, 60],
    #[19, 30, 81, 20, 30, 104],
    #[21, 31, 120, 0, 31, 103],
    #[27, 32, 109, 28, 32, 86],
    #[73, 33, 64, 26, 33, 87],
    #[26, 34, 111, 73, 34, 88],
    #[30, 35, 106, 29, 35, 121],
    #[29, 36, 127, 30, 36, 122],
    #[31, 37, 108, 1, 37, 123],
    #[22, 38, 66, 71, 38, 92],
    #[71, 39, 115, 22, 39, 93],
    #[69, 40, 68, 70, 40, 94],
    #[23, 41, 113, 72, 41, 125],
    #[91, 42, 51, 90, 42, 73],
    #[97, 43, 40, 98, 43, 18],
    #[33, 44, 59, 34, 44, 77],
    #[74, 45, 99, 32, 45, 76],
    #[32, 46, 100, 74, 46, 119],
    #[36, 47, 97, 35, 47, 75],
    #[35, 48, 98, 36, 48, 118],
    #[37, 49, 126, 2, 49, 117],
    #[3, 50, 62, 40, 50, 42],
    #[40, 51, 63, 3, 51, 84],
    #[38, 52, 105, 39, 52, 83],
    #[4, 53, 104, 41, 53, 81],
    #[8, 54, 86, 52, 54, 109],
    #[52, 55, 124, 8, 55, 110],
    #[50, 56, 88, 51, 56, 111],
    #[9, 57, 122, 53, 57, 127],
    #[46, 58, 93, 45, 58, 115],
    #[108, 59, 70, 107, 59, 95],
    #[66, 60, 30, 115, 60, 53],
    #[112, 61, 28, 113, 61, 52],
    #[114, 62, 73, 65, 62, 51],
    #[65, 63, 26, 114, 63, 50],
    #[80, 64, 56, 81, 64, 34],
    #[119, 65, 21, 76, 65, 6],
    #[117, 66, 58, 116, 66, 39],
    #[75, 67, 18, 118, 67, 40],
    #[118, 68, 17, 75, 68, 3],
    #[12, 69, 77, 56, 69, 59],
    #[56, 70, 78, 12, 70, 101],
    #[54, 71, 119, 55, 71, 100],
    #[13, 72, 118, 57, 72, 98],
    #[18, 73, 84, 17, 73, 63],
    #[28, 74, 110, 27, 74, 124],
    #[86, 75, 48, 124, 75, 72],
    #[121, 76, 46, 122, 76, 71],
    #[123, 77, 95, 85, 77, 70],
    #[85, 78, 44, 123, 78, 69],
    #[94, 79, 11, 43, 79, 31],
    #[92, 80, 53, 93, 80, 30],
    #[93, 81, 9, 92, 81, 29],
    #[89, 82, 52, 125, 82, 28],
    #[125, 83, 8, 89, 83, 27],
    #[90, 84, 50, 91, 84, 26],
    #[105, 85, 37, 61, 85, 15],
    #[103, 86, 74, 102, 86, 55],
    #[60, 87, 34, 104, 87, 56],
    #[104, 88, 33, 60, 88, 12],
    #[59, 89, 41, 101, 89, 20],
    #[100, 90, 6, 99, 90, 21],
    #[99, 91, 5, 100, 91, 0],
    #[126, 92, 39, 96, 92, 58],
    #[96, 93, 38, 126, 93, 16],
    #[98, 94, 3, 97, 94, 17],
    #[34, 95, 101, 33, 95, 78],
    #[111, 96, 25, 64, 96, 49],
    #[109, 97, 72, 110, 97, 48],
    #[110, 98, 23, 109, 98, 47],
    #[106, 99, 71, 127, 99, 46],
    #[127, 100, 22, 106, 100, 45],
    #[107, 101, 69, 108, 101, 44],
    #[68, 102, 31, 67, 102, 11],
    #[67, 103, 1, 68, 103, 10],
    #[115, 104, 29, 66, 104, 9],
    #[113, 105, 27, 112, 105, 8],
    #[42, 106, 57, 84, 106, 36],
    #[83, 107, 15, 82, 107, 37],
    #[82, 108, 14, 83, 108, 2],
    #[120, 109, 55, 79, 109, 74],
    #[79, 110, 54, 120, 110, 32],
    #[81, 111, 12, 80, 111, 33],
    #[77, 112, 20, 78, 112, 41],
    #[78, 113, 19, 77, 113, 4],
    #[76, 114, 0, 119, 114, 5],
    #[116, 115, 16, 117, 115, 38],
    #[88, 116, 49, 87, 116, 25],
    #[87, 117, 7, 88, 117, 24],
    #[124, 118, 47, 86, 118, 23],
    #[122, 119, 45, 121, 119, 22],
    #[43, 120, 10, 94, 120, 1],
    #[62, 121, 36, 63, 121, 57],
    #[63, 122, 35, 62, 122, 13],
    #[61, 123, 2, 105, 123, 14],
    #[102, 124, 32, 103, 124, 54],
    #[101, 125, 4, 59, 125, 19],
    #[64, 126, 24, 111, 126, 7],
    #[84, 127, 13, 42, 127, 35]] : Array (Array ℕ)).getD k.val #[]).getD j.val 0)
set_option maxHeartbeats 1600000 in
private theorem cert46_6 : ∃ c, c ∈ Subgroup.centralizer (Subgroup.closure (Set.range e46_6) : Set SylowModel) ∧ c ∉ Subgroup.closure (Set.range e46_6) := by
  refine ⟨root 2 * root 8, centralizes_generators e46_6 _ (by decide +kernel), ?_⟩
  exact outside_of_table e46_6 a46_6 0 next46_6 prev46_6
    (by decide +kernel) (by decide +kernel) (by decide +kernel) _ (by decide +kernel)

private def e46_7 : Fin 6 → SylowModel := ![decode 0, decode 3472, decode 3636, decode 2048, decode 1168, decode 1396]
set_option maxHeartbeats 1600000 in
private theorem edgeEq46_7 : binaryFamily s46 (s46 0) (![true, true, true]) = e46_7 := by decide +kernel
private def a46_7 (k : Fin 128) : SylowModel :=
  decode ((#[0, 2048, 64, 384, 768, 512, 1168, 2368, 2432, 2816, 2560, 448, 832, 576, 640, 896, 256, 3216, 1872, 1040, 1936, 1680, 2240, 2624, 2880, 2688, 2944, 2304, 704, 960, 320, 128, 228, 3664, 3088, 3984, 3728, 2000, 1104, 1360, 1808, 1552, 1424, 3008, 2752, 2112, 2176, 192, 1076, 2660, 164, 356, 996, 740, 3792, 3408, 3152, 3856, 3600, 3472, 1232, 1488, 1616, 1296, 2496, 4020, 2036, 1204, 1844, 1588, 2852, 3044, 2404, 2148, 292, 932, 676, 612, 868, 484, 3536, 3280, 3920, 3344, 1744, 3444, 3892, 3252, 3508, 1908, 1268, 1524, 1972, 1716, 1332, 2724, 2084, 2340, 2276, 2532, 2916, 548, 804, 420, 100, 4048, 3572, 3700, 3956, 3124, 3380, 3764, 1140, 1396, 1780, 1460, 2468, 2212, 2596, 2788, 36, 3828, 4084, 3188, 3636, 1652, 2980, 3316] : Array ℕ).getD k.val 0)
private def next46_7 (k : Fin 128) (j : Fin 6) : Fin 128 :=
  Fin.ofNat 128 (((#[#[0, 59, 124, 1, 6, 113],
    #[1, 42, 115, 0, 17, 122],
    #[2, 80, 107, 45, 60, 94],
    #[3, 34, 65, 8, 63, 90],
    #[4, 36, 110, 9, 20, 125],
    #[5, 35, 109, 10, 21, 89],
    #[6, 0, 32, 17, 27, 96],
    #[7, 60, 90, 30, 80, 111],
    #[8, 19, 48, 3, 83, 107],
    #[9, 21, 93, 4, 35, 127],
    #[10, 20, 92, 5, 36, 106],
    #[11, 56, 122, 64, 39, 67],
    #[12, 54, 85, 24, 37, 69],
    #[13, 105, 123, 23, 84, 68],
    #[14, 57, 87, 25, 41, 66],
    #[15, 58, 88, 26, 40, 114],
    #[16, 17, 86, 27, 42, 112],
    #[17, 1, 49, 6, 16, 75],
    #[18, 29, 102, 82, 44, 71],
    #[19, 31, 104, 34, 8, 117],
    #[20, 4, 52, 35, 10, 70],
    #[21, 5, 53, 36, 9, 118],
    #[22, 39, 113, 47, 56, 86],
    #[23, 37, 66, 13, 54, 88],
    #[24, 84, 114, 12, 105, 87],
    #[25, 40, 68, 14, 58, 85],
    #[26, 41, 69, 15, 57, 123],
    #[27, 6, 67, 16, 59, 121],
    #[28, 82, 127, 44, 62, 92],
    #[29, 33, 106, 43, 18, 93],
    #[30, 81, 108, 7, 61, 48],
    #[31, 83, 111, 46, 19, 91],
    #[32, 108, 54, 98, 125, 42],
    #[33, 44, 117, 62, 29, 51],
    #[34, 46, 119, 19, 3, 102],
    #[35, 9, 72, 20, 5, 50],
    #[36, 10, 73, 21, 4, 103],
    #[37, 12, 75, 105, 23, 100],
    #[38, 47, 120, 56, 64, 98],
    #[39, 11, 74, 55, 22, 99],
    #[40, 15, 78, 57, 25, 126],
    #[41, 14, 77, 58, 26, 95],
    #[42, 16, 79, 59, 1, 97],
    #[43, 62, 125, 29, 82, 109],
    #[44, 18, 89, 28, 33, 110],
    #[45, 61, 91, 2, 81, 65],
    #[46, 63, 94, 31, 34, 108],
    #[47, 55, 121, 22, 38, 115],
    #[48, 76, 2, 109, 126, 46],
    #[49, 91, 37, 77, 127, 59],
    #[50, 86, 36, 117, 69, 61],
    #[51, 121, 82, 72, 66, 19],
    #[52, 123, 80, 71, 113, 21],
    #[53, 85, 81, 119, 112, 20],
    #[54, 23, 96, 84, 12, 79],
    #[55, 64, 126, 39, 47, 77],
    #[56, 22, 95, 38, 11, 78],
    #[57, 26, 99, 40, 14, 120],
    #[58, 25, 98, 41, 15, 74],
    #[59, 27, 100, 42, 0, 76],
    #[60, 2, 50, 81, 7, 73],
    #[61, 30, 103, 80, 45, 72],
    #[62, 28, 101, 33, 43, 119],
    #[63, 3, 51, 83, 46, 116],
    #[64, 38, 112, 11, 55, 124],
    #[65, 97, 7, 92, 120, 31],
    #[66, 51, 15, 122, 73, 24],
    #[67, 101, 47, 87, 70, 1],
    #[68, 103, 12, 86, 117, 26],
    #[69, 50, 13, 124, 116, 25],
    #[70, 67, 21, 102, 88, 81],
    #[71, 112, 62, 52, 85, 34],
    #[72, 114, 60, 51, 122, 36],
    #[73, 66, 61, 104, 121, 35],
    #[74, 111, 57, 97, 92, 38],
    #[75, 109, 59, 126, 94, 84],
    #[76, 110, 17, 95, 48, 37],
    #[77, 106, 56, 49, 90, 40],
    #[78, 127, 55, 100, 91, 41],
    #[79, 107, 105, 99, 89, 6],
    #[80, 7, 70, 61, 2, 53],
    #[81, 45, 118, 60, 30, 52],
    #[82, 43, 116, 18, 28, 104],
    #[83, 8, 71, 63, 31, 101],
    #[84, 13, 76, 54, 24, 49],
    #[85, 71, 26, 113, 53, 13],
    #[86, 116, 64, 68, 50, 0],
    #[87, 118, 23, 67, 102, 15],
    #[88, 70, 24, 115, 101, 14],
    #[89, 79, 4, 108, 98, 43],
    #[90, 77, 31, 127, 100, 45],
    #[91, 78, 3, 106, 49, 7],
    #[92, 74, 29, 65, 96, 9],
    #[93, 120, 28, 111, 97, 10],
    #[94, 75, 30, 110, 95, 8],
    #[95, 94, 40, 76, 109, 55],
    #[96, 92, 42, 120, 111, 105],
    #[97, 93, 6, 74, 65, 54],
    #[98, 89, 39, 32, 107, 57],
    #[99, 125, 38, 79, 108, 58],
    #[100, 90, 84, 78, 106, 17],
    #[101, 88, 34, 118, 67, 18],
    #[102, 87, 83, 70, 115, 62],
    #[103, 124, 35, 116, 68, 60],
    #[104, 122, 33, 73, 114, 63],
    #[105, 24, 97, 37, 13, 32],
    #[106, 100, 9, 91, 77, 28],
    #[107, 98, 46, 125, 79, 30],
    #[108, 99, 8, 89, 32, 2],
    #[109, 95, 44, 48, 75, 4],
    #[110, 126, 43, 94, 76, 5],
    #[111, 96, 45, 93, 74, 3],
    #[112, 53, 0, 123, 71, 22],
    #[113, 52, 16, 85, 119, 64],
    #[114, 104, 14, 121, 72, 23],
    #[115, 102, 11, 88, 118, 27],
    #[116, 69, 19, 103, 86, 33],
    #[117, 68, 63, 50, 124, 82],
    #[118, 115, 20, 101, 87, 80],
    #[119, 113, 18, 53, 123, 83],
    #[120, 65, 58, 96, 93, 39],
    #[121, 73, 1, 114, 51, 11],
    #[122, 72, 27, 66, 104, 47],
    #[123, 119, 25, 112, 52, 12],
    #[124, 117, 22, 69, 103, 16],
    #[125, 32, 5, 107, 99, 44],
    #[126, 48, 41, 75, 110, 56],
    #[127, 49, 10, 90, 78, 29]] : Array (Array ℕ)).getD k.val #[]).getD j.val 0)
private def prev46_7 (k : Fin 128) (j : Fin 6) : Fin 128 :=
  Fin.ofNat 128 (((#[#[0, 6, 112, 1, 59, 86],
    #[1, 17, 121, 0, 42, 67],
    #[2, 60, 48, 45, 80, 108],
    #[3, 63, 91, 8, 34, 111],
    #[4, 20, 89, 9, 36, 109],
    #[5, 21, 125, 10, 35, 110],
    #[6, 27, 97, 17, 0, 79],
    #[7, 80, 65, 30, 60, 91],
    #[8, 83, 108, 3, 19, 94],
    #[9, 35, 106, 4, 21, 92],
    #[10, 36, 127, 5, 20, 93],
    #[11, 39, 115, 64, 56, 121],
    #[12, 37, 68, 24, 54, 123],
    #[13, 84, 69, 23, 105, 85],
    #[14, 41, 114, 25, 57, 88],
    #[15, 40, 66, 26, 58, 87],
    #[16, 42, 113, 27, 17, 124],
    #[17, 16, 76, 6, 1, 100],
    #[18, 44, 119, 82, 29, 101],
    #[19, 8, 116, 34, 31, 51],
    #[20, 10, 118, 35, 4, 53],
    #[21, 9, 70, 36, 5, 52],
    #[22, 56, 124, 47, 39, 112],
    #[23, 54, 87, 13, 37, 114],
    #[24, 105, 88, 12, 84, 66],
    #[25, 58, 123, 14, 40, 69],
    #[26, 57, 85, 15, 41, 68],
    #[27, 59, 122, 16, 6, 115],
    #[28, 62, 93, 44, 82, 106],
    #[29, 18, 92, 43, 33, 127],
    #[30, 61, 94, 7, 81, 107],
    #[31, 19, 90, 46, 83, 65],
    #[32, 125, 6, 98, 108, 105],
    #[33, 29, 104, 62, 44, 116],
    #[34, 3, 101, 19, 46, 71],
    #[35, 5, 103, 20, 9, 73],
    #[36, 4, 50, 21, 10, 72],
    #[37, 23, 49, 105, 12, 76],
    #[38, 64, 99, 56, 47, 74],
    #[39, 22, 98, 55, 11, 120],
    #[40, 25, 95, 57, 15, 77],
    #[41, 26, 126, 58, 14, 78],
    #[42, 1, 96, 59, 16, 32],
    #[43, 82, 110, 29, 62, 89],
    #[44, 33, 109, 28, 18, 125],
    #[45, 81, 111, 2, 61, 90],
    #[46, 34, 107, 31, 63, 48],
    #[47, 38, 67, 22, 55, 122],
    #[48, 126, 8, 109, 76, 30],
    #[49, 127, 17, 77, 91, 84],
    #[50, 69, 60, 117, 86, 35],
    #[51, 66, 63, 72, 121, 33],
    #[52, 113, 20, 71, 123, 81],
    #[53, 112, 21, 119, 85, 80],
    #[54, 12, 32, 84, 23, 97],
    #[55, 47, 78, 39, 64, 95],
    #[56, 11, 77, 38, 22, 126],
    #[57, 14, 74, 40, 26, 98],
    #[58, 15, 120, 41, 25, 99],
    #[59, 0, 75, 42, 27, 49],
    #[60, 7, 72, 81, 2, 103],
    #[61, 45, 73, 80, 30, 50],
    #[62, 43, 71, 33, 28, 102],
    #[63, 46, 117, 83, 3, 104],
    #[64, 55, 86, 11, 38, 113],
    #[65, 120, 3, 92, 97, 45],
    #[66, 73, 23, 122, 51, 14],
    #[67, 70, 27, 87, 101, 11],
    #[68, 117, 25, 86, 103, 13],
    #[69, 116, 26, 124, 50, 12],
    #[70, 88, 80, 102, 67, 20],
    #[71, 85, 83, 52, 112, 18],
    #[72, 122, 35, 51, 114, 61],
    #[73, 121, 36, 104, 66, 60],
    #[74, 92, 39, 97, 111, 58],
    #[75, 94, 37, 126, 109, 17],
    #[76, 48, 84, 95, 110, 59],
    #[77, 90, 41, 49, 106, 55],
    #[78, 91, 40, 100, 127, 56],
    #[79, 89, 42, 99, 107, 54],
    #[80, 2, 52, 61, 7, 118],
    #[81, 30, 53, 60, 45, 70],
    #[82, 28, 51, 18, 43, 117],
    #[83, 31, 102, 63, 8, 119],
    #[84, 24, 100, 54, 13, 75],
    #[85, 53, 12, 113, 71, 25],
    #[86, 50, 16, 68, 116, 22],
    #[87, 102, 14, 67, 118, 24],
    #[88, 101, 15, 115, 70, 23],
    #[89, 98, 44, 108, 79, 5],
    #[90, 100, 7, 127, 77, 3],
    #[91, 49, 45, 106, 78, 31],
    #[92, 96, 10, 65, 74, 28],
    #[93, 97, 9, 111, 120, 29],
    #[94, 95, 46, 110, 75, 2],
    #[95, 109, 56, 76, 94, 41],
    #[96, 111, 54, 120, 92, 6],
    #[97, 65, 105, 74, 93, 42],
    #[98, 107, 58, 32, 89, 38],
    #[99, 108, 57, 79, 125, 39],
    #[100, 106, 59, 78, 90, 37],
    #[101, 67, 62, 118, 88, 83],
    #[102, 115, 18, 70, 87, 34],
    #[103, 68, 61, 116, 124, 36],
    #[104, 114, 19, 73, 122, 82],
    #[105, 13, 79, 37, 24, 96],
    #[106, 77, 29, 91, 100, 10],
    #[107, 79, 2, 125, 98, 8],
    #[108, 32, 30, 89, 99, 46],
    #[109, 75, 5, 48, 95, 43],
    #[110, 76, 4, 94, 126, 44],
    #[111, 74, 31, 93, 96, 7],
    #[112, 71, 64, 123, 53, 16],
    #[113, 119, 22, 85, 52, 0],
    #[114, 72, 24, 121, 104, 15],
    #[115, 118, 1, 88, 102, 47],
    #[116, 86, 82, 103, 69, 63],
    #[117, 124, 33, 50, 68, 19],
    #[118, 87, 81, 101, 115, 21],
    #[119, 123, 34, 53, 113, 62],
    #[120, 93, 38, 96, 65, 57],
    #[121, 51, 47, 114, 73, 27],
    #[122, 104, 11, 66, 72, 1],
    #[123, 52, 13, 112, 119, 26],
    #[124, 103, 0, 69, 117, 64],
    #[125, 99, 43, 107, 32, 4],
    #[126, 110, 55, 75, 48, 40],
    #[127, 78, 28, 90, 49, 9]] : Array (Array ℕ)).getD k.val #[]).getD j.val 0)
set_option maxHeartbeats 1600000 in
private theorem cert46_7 : ∃ c, c ∈ Subgroup.centralizer (Subgroup.closure (Set.range e46_7) : Set SylowModel) ∧ c ∉ Subgroup.closure (Set.range e46_7) := by
  refine ⟨root 2 * root 7, centralizes_generators e46_7 _ (by decide +kernel), ?_⟩
  exact outside_of_table e46_7 a46_7 0 next46_7 prev46_7
    (by decide +kernel) (by decide +kernel) (by decide +kernel) _ (by decide +kernel)

private def s47 : Fin 3 → SylowModel := ![root 4 * root 7 * root 8, rootOne ^ 3 * root 2 * root 3 * root 4 * root 5 * root 7 * root 8 * root 9, root 2 * root 4 * root 5 * root 9]
set_option maxHeartbeats 1600000 in
private theorem gen47 : Subgroup.closure (Set.range s47) = smallParityCensusNode 47 := by
  rw [node47]
  exact closure_eq_words s47 o47 (![[3, 5, 6], [1], [0]]) (![[2], [1], [0, 2, 1, 2, 1], [0, 1, 2, 1, 1, 2, 1], [0, 1, 0, 1, 2, 1, 2, 1], [0, 1, 0, 2, 1, 1, 2, 1], [0, 2, 0, 2], [2, 2]]) (by decide +kernel) (by decide +kernel)

private def e47_1 : Fin 6 → SylowModel := ![decode 0, decode 1516, decode 564, decode 0, decode 2028, decode 308]
set_option maxHeartbeats 1600000 in
private theorem edgeEq47_1 : binaryFamily s47 (s47 0) (![true, false, false]) = e47_1 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert47_1 : Represented smallParityCensusNode (Subgroup.closure (Set.range e47_1)) := by
  refine ⟨88, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node88]
  exact closure_eq_words _ o88 (![[], [1], [0], [], [1, 4, 6], [0, 4]]) (![[2], [1], [1, 1], [1, 1, 1, 2, 1, 2], [1, 1, 1, 4], [1, 1, 2, 1, 1, 2], [2, 2]]) (by decide +kernel) (by decide +kernel)

private def e47_2 : Fin 6 → SylowModel := ![decode 400, decode 0, decode 564, decode 912, decode 2640, decode 244]
set_option maxHeartbeats 1600000 in
private theorem edgeEq47_2 : binaryFamily s47 (s47 1) (![false, true, false]) = e47_2 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert47_2 : Subgroup.closure (Set.range e47_2) ≤ character.ker := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨j, rfl⟩
  exact (show ∀ j, e47_2 j ∈ character.ker from by decide +kernel) j

private def e47_3 : Fin 6 → SylowModel := ![decode 0, decode 1916, decode 564, decode 0, decode 1404, decode 308]
set_option maxHeartbeats 1600000 in
private theorem edgeEq47_3 : binaryFamily s47 (s47 0) (![true, true, false]) = e47_3 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert47_3 : Represented smallParityCensusNode (Subgroup.closure (Set.range e47_3)) := by
  refine ⟨88, root 2 * root 3 * root 4 * root 7, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node88]
  exact closure_eq_words _ o88 (![[], [5, 1], [0, 4, 5, 6], [], [1, 4, 5], [0, 5, 6]]) (![[1, 1, 5, 1, 1], [1, 1, 1, 2, 1, 4, 5], [1, 1, 2, 2], [1, 1, 1, 2, 4, 5], [1, 1, 1, 4], [1, 1, 2, 1, 1, 2], [2, 2]]) (by decide +kernel) (by decide +kernel)

private def e47_4 : Fin 6 → SylowModel := ![decode 400, decode 1516, decode 0, decode 656, decode 1324, decode 256]
set_option maxHeartbeats 1600000 in
private theorem edgeEq47_4 : binaryFamily s47 (s47 2) (![false, false, true]) = e47_4 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert47_4 : Represented smallParityCensusNode (Subgroup.closure (Set.range e47_4)) := by
  refine ⟨63, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node63]
  exact closure_eq_words _ o63 (![[1, 6], [5, 0], [], [1, 4], [0, 3, 4], [6]]) (![[1, 1, 4, 4, 1], [0, 5], [0, 3, 4, 1], [0, 1, 0, 4, 4, 4], [0, 3, 5], [1, 1, 4, 4], [5]]) (by decide +kernel) (by decide +kernel)

private def e47_5 : Fin 6 → SylowModel := ![decode 0, decode 1516, decode 420, decode 0, decode 2028, decode 676]
set_option maxHeartbeats 1600000 in
private theorem edgeEq47_5 : binaryFamily s47 (s47 0) (![true, false, true]) = e47_5 := by decide +kernel
private def a47_5 (k : Fin 128) : SylowModel :=
  decode ((#[0, 64, 384, 768, 512, 1836, 2448, 448, 832, 576, 640, 896, 256, 1032, 1260, 1964, 1068, 1324, 2256, 2064, 2704, 2960, 704, 960, 320, 128, 1992, 1160, 1800, 1544, 2548, 228, 3644, 1132, 2028, 1772, 1196, 1452, 1580, 2384, 3024, 2768, 2832, 2576, 2192, 192, 3224, 1864, 1224, 1480, 1928, 1672, 1288, 2228, 2164, 2804, 3060, 164, 356, 996, 740, 3324, 3772, 3388, 3132, 1900, 1644, 1516, 1708, 2640, 2896, 2512, 2320, 3672, 3096, 3992, 3736, 1096, 1352, 1736, 1416, 2356, 2996, 2740, 2932, 2676, 2292, 292, 932, 676, 612, 868, 484, 3196, 4092, 3836, 3516, 3260, 3900, 1388, 2128, 3800, 3416, 3160, 3864, 3608, 3480, 1608, 2612, 2868, 2484, 2420, 548, 804, 420, 100, 3964, 3708, 3580, 4028, 3544, 3288, 3928, 3352, 2100, 36, 3452, 4056] : Array ℕ).getD k.val 0)
private def next47_5 (k : Fin 128) (j : Fin 6) : Fin 128 :=
  Fin.ofNat 128 (((#[#[0, 67, 114, 0, 34, 89],
    #[1, 15, 92, 1, 37, 60],
    #[2, 33, 125, 2, 66, 113],
    #[3, 35, 89, 3, 14, 114],
    #[4, 34, 88, 4, 67, 57],
    #[5, 20, 107, 5, 44, 78],
    #[6, 94, 83, 6, 118, 110],
    #[7, 38, 115, 7, 16, 91],
    #[8, 36, 60, 8, 68, 92],
    #[9, 37, 59, 9, 15, 31],
    #[10, 65, 113, 10, 99, 125],
    #[11, 66, 112, 11, 33, 87],
    #[12, 14, 57, 12, 35, 88],
    #[13, 110, 65, 13, 82, 33],
    #[14, 70, 80, 14, 39, 51],
    #[15, 43, 79, 15, 19, 49],
    #[16, 6, 78, 16, 21, 107],
    #[17, 44, 77, 17, 20, 47],
    #[18, 97, 56, 18, 62, 86],
    #[19, 117, 109, 19, 93, 124],
    #[20, 61, 110, 20, 95, 83],
    #[21, 118, 53, 21, 94, 82],
    #[22, 17, 91, 22, 5, 115],
    #[23, 16, 90, 23, 38, 58],
    #[24, 68, 31, 24, 36, 59],
    #[25, 99, 87, 25, 65, 112],
    #[26, 54, 36, 26, 85, 15],
    #[27, 81, 34, 27, 109, 14],
    #[28, 83, 33, 28, 53, 65],
    #[29, 82, 99, 29, 110, 66],
    #[30, 75, 18, 30, 106, 40],
    #[31, 52, 8, 31, 28, 1],
    #[32, 12, 121, 32, 3, 127],
    #[33, 40, 52, 33, 71, 29],
    #[34, 100, 51, 34, 69, 80],
    #[35, 39, 50, 35, 70, 27],
    #[36, 72, 49, 36, 42, 79],
    #[37, 19, 48, 37, 43, 26],
    #[38, 21, 47, 38, 6, 77],
    #[39, 63, 85, 39, 98, 111],
    #[40, 119, 86, 40, 96, 56],
    #[41, 62, 30, 41, 97, 55],
    #[42, 126, 124, 42, 116, 109],
    #[43, 93, 81, 43, 117, 108],
    #[44, 95, 82, 44, 61, 53],
    #[45, 5, 58, 45, 17, 90],
    #[46, 88, 93, 46, 114, 116],
    #[47, 86, 16, 47, 55, 5],
    #[48, 84, 15, 48, 111, 36],
    #[49, 85, 68, 49, 54, 37],
    #[50, 108, 14, 50, 124, 34],
    #[51, 109, 67, 51, 81, 35],
    #[52, 53, 66, 52, 83, 99],
    #[53, 121, 6, 53, 101, 20],
    #[54, 105, 39, 54, 74, 69],
    #[55, 46, 40, 55, 76, 18],
    #[56, 106, 41, 56, 75, 71],
    #[57, 47, 3, 57, 78, 0],
    #[58, 27, 22, 58, 51, 7],
    #[59, 29, 1, 59, 13, 8],
    #[60, 28, 24, 60, 52, 9],
    #[61, 7, 105, 61, 23, 123],
    #[62, 2, 103, 62, 11, 122],
    #[63, 4, 127, 63, 0, 121],
    #[64, 3, 101, 64, 12, 120],
    #[65, 18, 29, 65, 41, 52],
    #[66, 71, 28, 66, 40, 13],
    #[67, 69, 27, 67, 100, 50],
    #[68, 42, 26, 68, 72, 48],
    #[69, 32, 111, 69, 64, 85],
    #[70, 98, 54, 70, 63, 84],
    #[71, 96, 55, 71, 119, 30],
    #[72, 116, 108, 72, 126, 81],
    #[73, 91, 62, 73, 58, 96],
    #[74, 113, 61, 74, 87, 94],
    #[75, 57, 116, 75, 89, 93],
    #[76, 114, 117, 76, 88, 126],
    #[77, 56, 5, 77, 30, 16],
    #[78, 55, 38, 78, 86, 17],
    #[79, 111, 37, 79, 84, 68],
    #[80, 124, 35, 80, 108, 67],
    #[81, 102, 19, 81, 122, 42],
    #[82, 127, 20, 82, 120, 6],
    #[83, 101, 21, 83, 121, 44],
    #[84, 123, 69, 84, 104, 39],
    #[85, 74, 70, 85, 105, 100],
    #[86, 76, 71, 86, 46, 41],
    #[87, 79, 10, 87, 48, 2],
    #[88, 77, 0, 88, 107, 3],
    #[89, 78, 12, 89, 47, 4],
    #[90, 50, 7, 90, 80, 22],
    #[91, 51, 45, 91, 27, 23],
    #[92, 13, 9, 92, 29, 24],
    #[93, 24, 76, 93, 8, 106],
    #[94, 22, 123, 94, 45, 105],
    #[95, 23, 74, 95, 7, 104],
    #[96, 10, 122, 96, 25, 103],
    #[97, 11, 73, 97, 2, 102],
    #[98, 0, 120, 98, 4, 101],
    #[99, 41, 13, 99, 18, 28],
    #[100, 64, 84, 100, 32, 54],
    #[101, 59, 32, 101, 92, 63],
    #[102, 115, 96, 102, 90, 62],
    #[103, 58, 97, 103, 91, 119],
    #[104, 125, 94, 104, 112, 61],
    #[105, 87, 95, 105, 113, 118],
    #[106, 89, 126, 106, 57, 117],
    #[107, 30, 17, 107, 56, 38],
    #[108, 73, 42, 108, 103, 19],
    #[109, 122, 43, 109, 102, 72],
    #[110, 120, 44, 110, 127, 21],
    #[111, 104, 100, 111, 123, 70],
    #[112, 49, 2, 112, 26, 10],
    #[113, 48, 25, 113, 79, 11],
    #[114, 107, 4, 114, 77, 12],
    #[115, 80, 23, 115, 50, 45],
    #[116, 9, 106, 116, 1, 76],
    #[117, 8, 46, 117, 24, 75],
    #[118, 45, 104, 118, 22, 74],
    #[119, 25, 102, 119, 10, 73],
    #[120, 31, 63, 120, 60, 32],
    #[121, 92, 64, 121, 59, 98],
    #[122, 90, 119, 122, 115, 97],
    #[123, 112, 118, 123, 125, 95],
    #[124, 103, 72, 124, 73, 43],
    #[125, 26, 11, 125, 49, 25],
    #[126, 1, 75, 126, 9, 46],
    #[127, 60, 98, 127, 31, 64]] : Array (Array ℕ)).getD k.val #[]).getD j.val 0)
private def prev47_5 (k : Fin 128) (j : Fin 6) : Fin 128 :=
  Fin.ofNat 128 (((#[#[0, 98, 88, 0, 63, 57],
    #[1, 126, 59, 1, 116, 31],
    #[2, 62, 112, 2, 97, 87],
    #[3, 64, 57, 3, 32, 88],
    #[4, 63, 114, 4, 98, 89],
    #[5, 45, 77, 5, 22, 47],
    #[6, 16, 53, 6, 38, 82],
    #[7, 61, 90, 7, 95, 58],
    #[8, 117, 31, 8, 93, 59],
    #[9, 116, 92, 9, 126, 60],
    #[10, 96, 87, 10, 119, 112],
    #[11, 97, 125, 11, 62, 113],
    #[12, 32, 89, 12, 64, 114],
    #[13, 92, 99, 13, 59, 66],
    #[14, 12, 50, 14, 3, 27],
    #[15, 1, 48, 15, 9, 26],
    #[16, 23, 47, 16, 7, 77],
    #[17, 22, 107, 17, 45, 78],
    #[18, 65, 30, 18, 99, 55],
    #[19, 37, 81, 19, 15, 108],
    #[20, 5, 82, 20, 17, 53],
    #[21, 38, 83, 21, 16, 110],
    #[22, 94, 58, 22, 118, 90],
    #[23, 95, 115, 23, 61, 91],
    #[24, 93, 60, 24, 117, 92],
    #[25, 119, 113, 25, 96, 125],
    #[26, 125, 68, 26, 112, 37],
    #[27, 58, 67, 27, 91, 35],
    #[28, 60, 66, 28, 31, 99],
    #[29, 59, 65, 29, 92, 33],
    #[30, 107, 41, 30, 77, 71],
    #[31, 120, 24, 31, 127, 9],
    #[32, 69, 101, 32, 100, 120],
    #[33, 2, 28, 33, 11, 13],
    #[34, 4, 27, 34, 0, 50],
    #[35, 3, 80, 35, 12, 51],
    #[36, 8, 26, 36, 24, 48],
    #[37, 9, 79, 37, 1, 49],
    #[38, 7, 78, 38, 23, 107],
    #[39, 35, 54, 39, 14, 84],
    #[40, 33, 55, 40, 66, 30],
    #[41, 99, 56, 41, 65, 86],
    #[42, 68, 108, 42, 36, 81],
    #[43, 15, 109, 43, 37, 124],
    #[44, 17, 110, 44, 5, 83],
    #[45, 118, 91, 45, 94, 115],
    #[46, 55, 117, 46, 86, 126],
    #[47, 57, 38, 47, 89, 17],
    #[48, 113, 37, 48, 87, 68],
    #[49, 112, 36, 49, 125, 15],
    #[50, 90, 35, 50, 115, 67],
    #[51, 91, 34, 51, 58, 14],
    #[52, 31, 33, 52, 60, 65],
    #[53, 52, 21, 53, 28, 44],
    #[54, 26, 70, 54, 49, 100],
    #[55, 78, 71, 55, 47, 41],
    #[56, 77, 18, 56, 107, 40],
    #[57, 75, 12, 57, 106, 4],
    #[58, 103, 45, 58, 73, 23],
    #[59, 101, 9, 59, 121, 24],
    #[60, 127, 8, 60, 120, 1],
    #[61, 20, 74, 61, 44, 104],
    #[62, 41, 73, 62, 18, 102],
    #[63, 39, 120, 63, 70, 101],
    #[64, 100, 121, 64, 69, 127],
    #[65, 10, 13, 65, 25, 28],
    #[66, 11, 52, 66, 2, 29],
    #[67, 0, 51, 67, 4, 80],
    #[68, 24, 49, 68, 8, 79],
    #[69, 67, 84, 69, 34, 54],
    #[70, 14, 85, 70, 35, 111],
    #[71, 66, 86, 71, 33, 56],
    #[72, 36, 124, 72, 68, 109],
    #[73, 108, 97, 73, 124, 119],
    #[74, 85, 95, 74, 54, 118],
    #[75, 30, 126, 75, 56, 117],
    #[76, 86, 93, 76, 55, 116],
    #[77, 88, 17, 77, 114, 38],
    #[78, 89, 16, 78, 57, 5],
    #[79, 87, 15, 79, 113, 36],
    #[80, 115, 14, 80, 90, 34],
    #[81, 27, 43, 81, 51, 72],
    #[82, 29, 44, 82, 13, 21],
    #[83, 28, 6, 83, 52, 20],
    #[84, 48, 100, 84, 79, 70],
    #[85, 49, 39, 85, 26, 69],
    #[86, 47, 40, 86, 78, 18],
    #[87, 105, 25, 87, 74, 11],
    #[88, 46, 4, 88, 76, 12],
    #[89, 106, 3, 89, 75, 0],
    #[90, 122, 23, 90, 102, 45],
    #[91, 73, 22, 91, 103, 7],
    #[92, 121, 1, 92, 101, 8],
    #[93, 43, 46, 93, 19, 75],
    #[94, 6, 104, 94, 21, 74],
    #[95, 44, 105, 95, 20, 123],
    #[96, 71, 102, 96, 40, 73],
    #[97, 18, 103, 97, 41, 122],
    #[98, 70, 127, 98, 39, 121],
    #[99, 25, 29, 99, 10, 52],
    #[100, 34, 111, 100, 67, 85],
    #[101, 83, 64, 101, 53, 98],
    #[102, 81, 119, 102, 109, 97],
    #[103, 124, 62, 103, 108, 96],
    #[104, 111, 118, 104, 84, 95],
    #[105, 54, 61, 105, 85, 94],
    #[106, 56, 116, 106, 30, 93],
    #[107, 114, 5, 107, 88, 16],
    #[108, 50, 72, 108, 80, 43],
    #[109, 51, 19, 109, 27, 42],
    #[110, 13, 20, 110, 29, 6],
    #[111, 79, 69, 111, 48, 39],
    #[112, 123, 11, 112, 104, 25],
    #[113, 74, 10, 113, 105, 2],
    #[114, 76, 0, 114, 46, 3],
    #[115, 102, 7, 115, 122, 22],
    #[116, 72, 75, 116, 42, 46],
    #[117, 19, 76, 117, 43, 106],
    #[118, 21, 123, 118, 6, 105],
    #[119, 40, 122, 119, 71, 103],
    #[120, 110, 98, 120, 82, 64],
    #[121, 53, 32, 121, 83, 63],
    #[122, 109, 96, 122, 81, 62],
    #[123, 84, 94, 123, 111, 61],
    #[124, 80, 42, 124, 50, 19],
    #[125, 104, 2, 125, 123, 10],
    #[126, 42, 106, 126, 72, 76],
    #[127, 82, 63, 127, 110, 32]] : Array (Array ℕ)).getD k.val #[]).getD j.val 0)
set_option maxHeartbeats 1600000 in
private theorem cert47_5 : ∃ c, c ∈ Subgroup.centralizer (Subgroup.closure (Set.range e47_5) : Set SylowModel) ∧ c ∉ Subgroup.closure (Set.range e47_5) := by
  refine ⟨root 2 * root 6 * root 7, centralizes_generators e47_5 _ (by decide +kernel), ?_⟩
  exact outside_of_table e47_5 a47_5 0 next47_5 prev47_5
    (by decide +kernel) (by decide +kernel) (by decide +kernel) _ (by decide +kernel)

private def e47_6 : Fin 6 → SylowModel := ![decode 400, decode 0, decode 3080, decode 912, decode 2640, decode 1048]
set_option maxHeartbeats 1600000 in
private theorem edgeEq47_6 : binaryFamily s47 (s47 1) (![false, true, true]) = e47_6 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert47_6 : Represented smallParityCensusNode (Subgroup.closure (Set.range e47_6)) := by
  refine ⟨69, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node69]
  exact closure_eq_words _ o69 (![[1, 6], [], [0, 1, 2, 5], [1, 4, 6], [0, 3, 0, 4], [1, 0, 5]]) (![[4, 5, 0, 4], [0, 2, 5], [2, 2], [0, 2, 4, 2, 3], [0, 3], [4, 5, 4, 2], [2, 5]]) (by decide +kernel) (by decide +kernel)

private def e47_7 : Fin 6 → SylowModel := ![decode 0, decode 1916, decode 420, decode 0, decode 1404, decode 676]
set_option maxHeartbeats 1600000 in
private theorem edgeEq47_7 : binaryFamily s47 (s47 0) (![true, true, true]) = e47_7 := by decide +kernel
private def a47_7 (k : Fin 128) : SylowModel :=
  decode ((#[0, 64, 384, 768, 512, 2448, 448, 832, 576, 640, 896, 256, 3244, 1468, 2256, 2064, 2704, 2960, 704, 960, 320, 128, 3080, 1176, 2548, 228, 3692, 3116, 4012, 3756, 1660, 1340, 1724, 1980, 2384, 3024, 2768, 2832, 2576, 2192, 192, 3784, 3208, 3848, 3592, 1880, 1048, 1944, 1688, 2228, 2164, 2804, 3060, 164, 356, 996, 740, 3820, 3436, 3180, 3884, 3628, 3500, 1788, 1404, 1148, 1596, 1852, 1212, 2640, 2896, 2512, 2320, 3656, 3528, 3272, 3976, 3720, 3336, 2008, 1112, 1368, 1816, 1560, 1432, 2356, 2996, 2740, 2932, 2676, 2292, 292, 932, 676, 612, 868, 484, 3564, 3308, 3948, 3372, 1532, 1276, 1916, 1084, 2128, 3400, 3144, 4040, 3464, 1240, 1496, 1624, 1304, 2612, 2868, 2484, 2420, 548, 804, 420, 100, 4076, 2044, 3912, 1752, 2100, 36] : Array ℕ).getD k.val 0)
private def next47_7 (k : Fin 128) (j : Fin 6) : Fin 128 :=
  Fin.ofNat 128 (((#[#[0, 103, 120, 0, 64, 93],
    #[1, 31, 96, 1, 67, 56],
    #[2, 63, 127, 2, 102, 119],
    #[3, 65, 93, 3, 30, 120],
    #[4, 64, 92, 4, 103, 53],
    #[5, 58, 87, 5, 99, 116],
    #[6, 68, 121, 6, 32, 95],
    #[7, 66, 56, 7, 104, 96],
    #[8, 67, 55, 8, 31, 25],
    #[9, 101, 119, 9, 123, 127],
    #[10, 102, 118, 10, 63, 91],
    #[11, 30, 53, 11, 65, 92],
    #[12, 3, 124, 12, 11, 107],
    #[13, 39, 111, 13, 16, 125],
    #[14, 61, 52, 14, 27, 90],
    #[15, 98, 115, 15, 57, 126],
    #[16, 26, 116, 16, 59, 87],
    #[17, 99, 49, 17, 58, 86],
    #[18, 33, 95, 18, 13, 121],
    #[19, 32, 94, 19, 68, 54],
    #[20, 104, 25, 20, 66, 55],
    #[21, 123, 91, 21, 101, 118],
    #[22, 120, 97, 22, 92, 57],
    #[23, 86, 63, 23, 116, 101],
    #[24, 43, 14, 24, 78, 35],
    #[25, 84, 7, 25, 47, 1],
    #[26, 19, 109, 26, 6, 77],
    #[27, 10, 108, 27, 2, 75],
    #[28, 0, 107, 28, 4, 124],
    #[29, 11, 106, 29, 3, 73],
    #[30, 34, 83, 30, 70, 113],
    #[31, 15, 81, 31, 38, 112],
    #[32, 17, 125, 32, 5, 111],
    #[33, 16, 79, 33, 39, 110],
    #[34, 28, 89, 34, 62, 117],
    #[35, 100, 90, 35, 60, 52],
    #[36, 27, 24, 36, 61, 51],
    #[37, 122, 126, 37, 97, 115],
    #[38, 57, 85, 38, 98, 114],
    #[39, 59, 86, 39, 26, 49],
    #[40, 13, 54, 40, 33, 94],
    #[41, 54, 60, 41, 95, 27],
    #[42, 91, 58, 42, 119, 26],
    #[43, 93, 57, 43, 53, 97],
    #[44, 92, 122, 44, 120, 98],
    #[45, 89, 31, 45, 50, 66],
    #[46, 115, 30, 46, 85, 64],
    #[47, 49, 101, 47, 87, 63],
    #[48, 116, 102, 48, 86, 123],
    #[49, 107, 5, 49, 73, 16],
    #[50, 77, 34, 50, 42, 69],
    #[51, 22, 35, 51, 44, 14],
    #[52, 78, 36, 52, 43, 71],
    #[53, 79, 3, 53, 111, 0],
    #[54, 46, 18, 54, 83, 6],
    #[55, 48, 1, 55, 23, 7],
    #[56, 47, 20, 56, 84, 8],
    #[57, 7, 78, 57, 20, 44],
    #[58, 40, 77, 58, 18, 109],
    #[59, 6, 76, 59, 19, 42],
    #[60, 21, 75, 60, 9, 108],
    #[61, 2, 74, 61, 10, 41],
    #[62, 4, 73, 62, 0, 106],
    #[63, 71, 48, 63, 35, 84],
    #[64, 69, 113, 64, 105, 83],
    #[65, 70, 46, 65, 34, 82],
    #[66, 37, 112, 66, 72, 81],
    #[67, 38, 45, 67, 15, 80],
    #[68, 5, 110, 68, 17, 79],
    #[69, 12, 117, 69, 29, 89],
    #[70, 62, 50, 70, 28, 88],
    #[71, 60, 51, 71, 100, 24],
    #[72, 97, 114, 72, 122, 85],
    #[73, 96, 28, 73, 55, 12],
    #[74, 94, 27, 74, 121, 60],
    #[75, 95, 100, 75, 54, 61],
    #[76, 118, 26, 76, 127, 58],
    #[77, 119, 99, 77, 91, 59],
    #[78, 53, 98, 78, 93, 122],
    #[79, 51, 13, 79, 90, 32],
    #[80, 117, 66, 80, 88, 31],
    #[81, 50, 67, 81, 89, 104],
    #[82, 126, 64, 82, 114, 30],
    #[83, 85, 65, 83, 115, 103],
    #[84, 87, 123, 84, 49, 102],
    #[85, 74, 15, 85, 108, 37],
    #[86, 124, 16, 86, 106, 5],
    #[87, 73, 17, 87, 107, 39],
    #[88, 109, 69, 88, 76, 34],
    #[89, 42, 70, 89, 77, 105],
    #[90, 44, 71, 90, 22, 36],
    #[91, 112, 9, 91, 80, 2],
    #[92, 110, 0, 92, 125, 3],
    #[93, 111, 11, 93, 79, 4],
    #[94, 82, 6, 94, 113, 18],
    #[95, 83, 40, 95, 46, 19],
    #[96, 23, 8, 96, 48, 20],
    #[97, 1, 44, 97, 8, 78],
    #[98, 20, 43, 98, 7, 22],
    #[99, 18, 42, 99, 40, 76],
    #[100, 9, 41, 100, 21, 74],
    #[101, 36, 84, 101, 14, 48],
    #[102, 35, 23, 102, 71, 47],
    #[103, 105, 82, 103, 69, 46],
    #[104, 72, 80, 104, 37, 45],
    #[105, 29, 88, 105, 12, 50],
    #[106, 56, 12, 106, 25, 28],
    #[107, 55, 62, 107, 96, 29],
    #[108, 121, 61, 108, 94, 100],
    #[109, 127, 59, 109, 118, 99],
    #[110, 24, 32, 110, 52, 13],
    #[111, 90, 33, 111, 51, 68],
    #[112, 88, 104, 112, 117, 67],
    #[113, 114, 103, 113, 126, 65],
    #[114, 41, 37, 114, 75, 15],
    #[115, 108, 38, 115, 74, 72],
    #[116, 106, 39, 116, 124, 17],
    #[117, 76, 105, 117, 109, 70],
    #[118, 81, 2, 118, 45, 9],
    #[119, 80, 21, 119, 112, 10],
    #[120, 125, 4, 120, 110, 11],
    #[121, 113, 19, 121, 82, 40],
    #[122, 8, 22, 122, 1, 43],
    #[123, 14, 47, 123, 36, 23],
    #[124, 25, 29, 124, 56, 62],
    #[125, 52, 68, 125, 24, 33],
    #[126, 75, 72, 126, 41, 38],
    #[127, 45, 10, 127, 81, 21]] : Array (Array ℕ)).getD k.val #[]).getD j.val 0)
private def prev47_7 (k : Fin 128) (j : Fin 6) : Fin 128 :=
  Fin.ofNat 128 (((#[#[0, 28, 92, 0, 62, 53],
    #[1, 97, 55, 1, 122, 25],
    #[2, 61, 118, 2, 27, 91],
    #[3, 12, 53, 3, 29, 92],
    #[4, 62, 120, 4, 28, 93],
    #[5, 68, 49, 5, 32, 86],
    #[6, 59, 94, 6, 26, 54],
    #[7, 57, 25, 7, 98, 55],
    #[8, 122, 96, 8, 97, 56],
    #[9, 100, 91, 9, 60, 118],
    #[10, 27, 127, 10, 61, 119],
    #[11, 29, 93, 11, 12, 120],
    #[12, 69, 106, 12, 105, 73],
    #[13, 40, 79, 13, 18, 110],
    #[14, 123, 24, 14, 101, 51],
    #[15, 31, 85, 15, 67, 114],
    #[16, 33, 86, 16, 13, 49],
    #[17, 32, 87, 17, 68, 116],
    #[18, 99, 54, 18, 58, 94],
    #[19, 26, 121, 19, 59, 95],
    #[20, 98, 56, 20, 57, 96],
    #[21, 60, 119, 21, 100, 127],
    #[22, 51, 122, 22, 90, 98],
    #[23, 96, 102, 23, 55, 123],
    #[24, 110, 36, 24, 125, 71],
    #[25, 124, 20, 25, 106, 8],
    #[26, 16, 76, 26, 39, 42],
    #[27, 36, 74, 27, 14, 41],
    #[28, 34, 73, 28, 70, 106],
    #[29, 105, 124, 29, 69, 107],
    #[30, 11, 46, 30, 3, 82],
    #[31, 1, 45, 31, 8, 80],
    #[32, 19, 110, 32, 6, 79],
    #[33, 18, 111, 33, 40, 125],
    #[34, 30, 50, 34, 65, 88],
    #[35, 102, 51, 35, 63, 24],
    #[36, 101, 52, 36, 123, 90],
    #[37, 66, 114, 37, 104, 85],
    #[38, 67, 115, 38, 31, 126],
    #[39, 13, 116, 39, 33, 87],
    #[40, 58, 95, 40, 99, 121],
    #[41, 114, 100, 41, 126, 61],
    #[42, 89, 99, 42, 50, 59],
    #[43, 24, 98, 43, 52, 122],
    #[44, 90, 97, 44, 51, 57],
    #[45, 127, 67, 45, 118, 104],
    #[46, 54, 65, 46, 95, 103],
    #[47, 56, 123, 47, 25, 102],
    #[48, 55, 63, 48, 96, 101],
    #[49, 47, 17, 49, 84, 39],
    #[50, 81, 70, 50, 45, 105],
    #[51, 79, 71, 51, 111, 36],
    #[52, 125, 14, 52, 110, 35],
    #[53, 78, 11, 53, 43, 4],
    #[54, 41, 40, 54, 75, 19],
    #[55, 107, 8, 55, 73, 20],
    #[56, 106, 7, 56, 124, 1],
    #[57, 38, 43, 57, 15, 22],
    #[58, 5, 42, 58, 17, 76],
    #[59, 39, 109, 59, 16, 77],
    #[60, 71, 41, 60, 35, 74],
    #[61, 14, 108, 61, 36, 75],
    #[62, 70, 107, 62, 34, 124],
    #[63, 2, 23, 63, 10, 47],
    #[64, 4, 82, 64, 0, 46],
    #[65, 3, 83, 65, 11, 113],
    #[66, 7, 80, 66, 20, 45],
    #[67, 8, 81, 67, 1, 112],
    #[68, 6, 125, 68, 19, 111],
    #[69, 64, 88, 69, 103, 50],
    #[70, 65, 89, 70, 30, 117],
    #[71, 63, 90, 71, 102, 52],
    #[72, 104, 126, 72, 66, 115],
    #[73, 87, 62, 73, 49, 29],
    #[74, 85, 61, 74, 115, 100],
    #[75, 126, 60, 75, 114, 27],
    #[76, 117, 59, 76, 88, 99],
    #[77, 50, 58, 77, 89, 26],
    #[78, 52, 57, 78, 24, 97],
    #[79, 53, 33, 79, 93, 68],
    #[80, 119, 104, 80, 91, 67],
    #[81, 118, 31, 81, 127, 66],
    #[82, 94, 103, 82, 121, 65],
    #[83, 95, 30, 83, 54, 64],
    #[84, 25, 101, 84, 56, 63],
    #[85, 83, 38, 85, 46, 72],
    #[86, 23, 39, 86, 48, 17],
    #[87, 84, 5, 87, 47, 16],
    #[88, 112, 105, 88, 80, 70],
    #[89, 45, 34, 89, 81, 69],
    #[90, 111, 35, 90, 79, 14],
    #[91, 42, 21, 91, 77, 10],
    #[92, 44, 4, 92, 22, 11],
    #[93, 43, 3, 93, 78, 0],
    #[94, 74, 19, 94, 108, 40],
    #[95, 75, 18, 95, 41, 6],
    #[96, 73, 1, 96, 107, 7],
    #[97, 72, 22, 97, 37, 43],
    #[98, 15, 78, 98, 38, 44],
    #[99, 17, 77, 99, 5, 109],
    #[100, 35, 75, 100, 71, 108],
    #[101, 9, 47, 101, 21, 23],
    #[102, 10, 48, 102, 2, 84],
    #[103, 0, 113, 103, 4, 83],
    #[104, 20, 112, 104, 7, 81],
    #[105, 103, 117, 105, 64, 89],
    #[106, 116, 29, 106, 86, 62],
    #[107, 49, 28, 107, 87, 12],
    #[108, 115, 27, 108, 85, 60],
    #[109, 88, 26, 109, 117, 58],
    #[110, 92, 68, 110, 120, 33],
    #[111, 93, 13, 111, 53, 32],
    #[112, 91, 66, 112, 119, 31],
    #[113, 121, 64, 113, 94, 30],
    #[114, 113, 72, 114, 82, 38],
    #[115, 46, 15, 115, 83, 37],
    #[116, 48, 16, 116, 23, 5],
    #[117, 80, 69, 117, 112, 34],
    #[118, 76, 10, 118, 109, 21],
    #[119, 77, 9, 119, 42, 2],
    #[120, 22, 0, 120, 44, 3],
    #[121, 108, 6, 121, 74, 18],
    #[122, 37, 44, 122, 72, 78],
    #[123, 21, 84, 123, 9, 48],
    #[124, 86, 12, 124, 116, 28],
    #[125, 120, 32, 125, 92, 13],
    #[126, 82, 37, 126, 113, 15],
    #[127, 109, 2, 127, 76, 9]] : Array (Array ℕ)).getD k.val #[]).getD j.val 0)
set_option maxHeartbeats 1600000 in
private theorem cert47_7 : ∃ c, c ∈ Subgroup.centralizer (Subgroup.closure (Set.range e47_7) : Set SylowModel) ∧ c ∉ Subgroup.closure (Set.range e47_7) := by
  refine ⟨root 2 * root 6 * root 8, centralizes_generators e47_7 _ (by decide +kernel), ?_⟩
  exact outside_of_table e47_7 a47_7 0 next47_7 prev47_7
    (by decide +kernel) (by decide +kernel) (by decide +kernel) _ (by decide +kernel)

private def s48 : Fin 3 → SylowModel := ![root 2 * root 3 * root 4 * root 7, root 3, rootOne ^ 3 * root 5 * root 8]
set_option maxHeartbeats 1600000 in
private theorem gen48 : Subgroup.closure (Set.range s48) = smallParityCensusNode 48 := by
  rw [node48]
  exact closure_eq_words s48 o48 (![[2], [0], [1]]) (![[1], [2], [0], [2, 2], [1, 2, 2, 2, 1, 2], [2, 0, 2, 2, 0, 2], [0, 1, 0, 1, 1, 1], [1, 1]]) (by decide +kernel) (by decide +kernel)

private def e48_1 : Fin 6 → SylowModel := ![decode 0, decode 8, decode 1632, decode 640, decode 136, decode 1136]
set_option maxHeartbeats 1600000 in
private theorem edgeEq48_1 : binaryFamily s48 (s48 0) (![true, false, false]) = e48_1 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert48_1 : Represented smallParityCensusNode (Subgroup.closure (Set.range e48_1)) := by
  refine ⟨77, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node77]
  exact closure_eq_words _ o77 (![[], [0], [1], [4, 6], [0, 4, 5, 6], [3, 1]]) (![[1], [2], [2, 2], [1, 1, 2, 2, 5, 2], [1, 1, 3], [1, 1, 1, 3, 4], [1, 1]]) (by decide +kernel) (by decide +kernel)

private def e48_2 : Fin 6 → SylowModel := ![decode 156, decode 0, decode 1632, decode 28, decode 256, decode 1648]
set_option maxHeartbeats 1600000 in
private theorem edgeEq48_2 : binaryFamily s48 (s48 1) (![false, true, false]) = e48_2 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert48_2 : Represented smallParityCensusNode (Subgroup.closure (Set.range e48_2)) := by
  refine ⟨66, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node66]
  exact closure_eq_words _ o66 (![[1], [], [0], [1, 4, 5], [6], [3, 0, 6]]) (![[2], [0], [2, 2], [2, 2, 5, 2], [0, 0], [0, 3], [4]]) (by decide +kernel) (by decide +kernel)

private def e48_3 : Fin 6 → SylowModel := ![decode 0, decode 916, decode 1632, decode 640, decode 404, decode 1136]
set_option maxHeartbeats 1600000 in
private theorem edgeEq48_3 : binaryFamily s48 (s48 0) (![true, true, false]) = e48_3 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert48_3 : Represented smallParityCensusNode (Subgroup.closure (Set.range e48_3)) := by
  refine ⟨89, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node89]
  exact closure_eq_words _ o89 (![[], [0, 4, 5], [1], [4, 5], [0, 4], [3, 1]]) (![[1, 3], [2], [2, 2], [1, 1, 2, 2, 2, 5], [1, 1, 1, 3, 4], [1, 1, 1, 4], [1, 4]]) (by decide +kernel) (by decide +kernel)

private def e48_4 : Fin 6 → SylowModel := ![decode 156, decode 8, decode 0, decode 908, decode 24, decode 2240]
set_option maxHeartbeats 1600000 in
private theorem edgeEq48_4 : binaryFamily s48 (s48 2) (![false, false, true]) = e48_4 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert48_4 : Subgroup.closure (Set.range e48_4) ≤ character.ker := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨j, rfl⟩
  exact (show ∀ j, e48_4 j ∈ character.ker from by decide +kernel) j

private def e48_5 : Fin 6 → SylowModel := ![decode 0, decode 8, decode 1644, decode 640, decode 136, decode 1788]
set_option maxHeartbeats 1600000 in
private theorem edgeEq48_5 : binaryFamily s48 (s48 0) (![true, false, true]) = e48_5 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert48_5 : Represented smallParityCensusNode (Subgroup.closure (Set.range e48_5)) := by
  refine ⟨77, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node77]
  exact closure_eq_words _ o77 (![[], [0, 5], [1, 5], [4, 5, 6], [0, 4, 5, 6], [3, 1]]) (![[3, 4], [1, 3, 5, 4], [2, 2], [1, 1, 2, 2, 2, 5], [1, 4], [1, 1, 1, 3, 4], [1, 1]]) (by decide +kernel) (by decide +kernel)

private def e48_6 : Fin 6 → SylowModel := ![decode 156, decode 0, decode 1912, decode 28, decode 256, decode 1640]
set_option maxHeartbeats 1600000 in
private theorem edgeEq48_6 : binaryFamily s48 (s48 1) (![false, true, true]) = e48_6 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert48_6 : Represented smallParityCensusNode (Subgroup.closure (Set.range e48_6)) := by
  refine ⟨74, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node74]
  exact closure_eq_words _ o74 (![[1, 5, 6], [], [1, 0, 1], [1, 4], [6], [0]]) (![[5], [0, 0, 3], [5, 5], [0, 0, 2, 2, 2, 5], [0, 0], [0, 3, 4], [4]]) (by decide +kernel) (by decide +kernel)

private def e48_7 : Fin 6 → SylowModel := ![decode 0, decode 916, decode 1644, decode 640, decode 404, decode 1788]
set_option maxHeartbeats 1600000 in
private theorem edgeEq48_7 : binaryFamily s48 (s48 0) (![true, true, true]) = e48_7 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert48_7 : Represented smallParityCensusNode (Subgroup.closure (Set.range e48_7)) := by
  refine ⟨90, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node90]
  exact closure_eq_words _ o90 (![[], [0, 4, 5], [1, 4, 5], [4, 5], [0, 4], [3, 1]]) (![[1, 3], [2, 3], [2, 5], [2, 2, 3, 5, 2], [1, 1, 1, 3, 4], [1, 1, 1, 4], [1, 4]]) (by decide +kernel) (by decide +kernel)

private def s49 : Fin 3 → SylowModel := ![root 2 * root 3 * root 4 * root 7, root 3 * root 6 * root 7 * root 8, rootOne ^ 3 * root 5 * root 8]
set_option maxHeartbeats 1600000 in
private theorem gen49 : Subgroup.closure (Set.range s49) = smallParityCensusNode 49 := by
  rw [node49]
  exact closure_eq_words s49 o49 (![[2], [0], [1]]) (![[1], [2], [0], [2, 2], [0, 0, 0, 2, 0, 2, 2, 2], [2, 0, 2, 2, 0, 2], [1, 1, 2, 2, 2, 2], [2, 2, 2, 2]]) (by decide +kernel) (by decide +kernel)

private def e49_1 : Fin 6 → SylowModel := ![decode 0, decode 456, decode 1632, decode 640, decode 840, decode 1136]
set_option maxHeartbeats 1600000 in
private theorem edgeEq49_1 : binaryFamily s49 (s49 0) (![true, false, false]) = e49_1 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert49_1 : Represented smallParityCensusNode (Subgroup.closure (Set.range e49_1)) := by
  refine ⟨78, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node78]
  exact closure_eq_words _ o78 (![[], [0], [1], [4, 6], [0, 4, 6], [3, 1]]) (![[1], [2], [2, 2], [1, 1, 2, 2, 2, 5], [2, 2, 2, 2, 3], [1, 1, 2, 2, 2, 2], [2, 2, 2, 2]]) (by decide +kernel) (by decide +kernel)

private def e49_2 : Fin 6 → SylowModel := ![decode 156, decode 0, decode 1632, decode 540, decode 768, decode 1264]
set_option maxHeartbeats 1600000 in
private theorem edgeEq49_2 : binaryFamily s49 (s49 1) (![false, true, false]) = e49_2 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert49_2 : Represented smallParityCensusNode (Subgroup.closure (Set.range e49_2)) := by
  refine ⟨66, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node66]
  exact closure_eq_words _ o66 (![[1], [], [0], [1, 4], [5, 6], [3, 0, 4]]) (![[2], [0], [2, 2], [0, 0, 2, 2, 5, 2], [0, 0], [2, 2, 5, 5], [2, 2, 2, 2]]) (by decide +kernel) (by decide +kernel)

private def e49_3 : Fin 6 → SylowModel := ![decode 0, decode 84, decode 1632, decode 640, decode 84, decode 1136]
set_option maxHeartbeats 1600000 in
private theorem edgeEq49_3 : binaryFamily s49 (s49 0) (![true, true, false]) = e49_3 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert49_3 : Represented smallParityCensusNode (Subgroup.closure (Set.range e49_3)) := by
  refine ⟨90, root 1 * root 2 * root 4 * root 6 * root 7 * root 9, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node90]
  exact closure_eq_words _ o90 (![[], [0, 4], [3, 1], [4], [0, 4], [4, 1]]) (![[1, 3], [3, 5], [1, 1, 5, 2], [2, 2, 5, 3, 2], [3], [1, 1, 2, 2, 2, 2], [2, 2, 2, 2]]) (by decide +kernel) (by decide +kernel)

private def e49_4 : Fin 6 → SylowModel := ![decode 156, decode 456, decode 0, decode 908, decode 856, decode 2240]
set_option maxHeartbeats 1600000 in
private theorem edgeEq49_4 : binaryFamily s49 (s49 2) (![false, false, true]) = e49_4 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert49_4 : Subgroup.closure (Set.range e49_4) ≤ character.ker := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨j, rfl⟩
  exact (show ∀ j, e49_4 j ∈ character.ker from by decide +kernel) j

private def e49_5 : Fin 6 → SylowModel := ![decode 0, decode 456, decode 1644, decode 640, decode 840, decode 1788]
set_option maxHeartbeats 1600000 in
private theorem edgeEq49_5 : binaryFamily s49 (s49 0) (![true, false, true]) = e49_5 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert49_5 : Represented smallParityCensusNode (Subgroup.closure (Set.range e49_5)) := by
  refine ⟨78, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node78]
  exact closure_eq_words _ o78 (![[], [0, 5], [1, 5], [0, 0, 4], [0, 4, 6], [3, 1]]) (![[2, 2, 1, 2, 2], [1, 4, 2, 3], [2, 2], [1, 1, 2, 2, 5, 2], [1, 4], [1, 1, 2, 2, 2, 2], [2, 2, 2, 2]]) (by decide +kernel) (by decide +kernel)

private def e49_6 : Fin 6 → SylowModel := ![decode 156, decode 0, decode 1592, decode 540, decode 768, decode 1960]
set_option maxHeartbeats 1600000 in
private theorem edgeEq49_6 : binaryFamily s49 (s49 1) (![false, true, true]) = e49_6 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert49_6 : Represented smallParityCensusNode (Subgroup.closure (Set.range e49_6)) := by
  refine ⟨74, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node74]
  exact closure_eq_words _ o74 (![[1, 5, 6], [], [0, 5], [1, 4, 5, 6], [5], [3, 0, 6]]) (![[2, 4], [0, 2, 2, 5, 5], [2, 2], [2, 2, 2, 5], [0, 0], [4], [2, 2, 2, 2]]) (by decide +kernel) (by decide +kernel)

private def e49_7 : Fin 6 → SylowModel := ![decode 0, decode 84, decode 1644, decode 640, decode 84, decode 1788]
set_option maxHeartbeats 1600000 in
private theorem edgeEq49_7 : binaryFamily s49 (s49 0) (![true, true, true]) = e49_7 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert49_7 : Represented smallParityCensusNode (Subgroup.closure (Set.range e49_7)) := by
  refine ⟨89, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node89]
  exact closure_eq_words _ o89 (![[], [0, 5], [1, 5], [4], [0, 5], [3, 1]]) (![[2, 5, 1, 5, 2], [1, 1, 1, 2, 1], [2, 2], [1, 1, 2, 2, 5, 2], [3], [1, 1, 2, 2, 2, 2], [2, 2, 2, 2]]) (by decide +kernel) (by decide +kernel)

private def s50 : Fin 4 → SylowModel := ![root 4 * root 7 * root 8, root 6, root 2 * root 4 * root 8, rootOne ^ 3 * root 5 * root 8]
set_option maxHeartbeats 1600000 in
private theorem gen50 : Subgroup.closure (Set.range s50) = smallParityCensusNode 50 := by
  rw [node50]
  exact closure_eq_words s50 o50 (![[0, 0, 4, 5], [2, 5, 7], [0], [1]]) (![[2], [3], [0, 3, 0, 1, 3, 3, 3], [3, 3], [0, 1, 3, 3, 3, 1, 3], [0, 1, 3, 0, 3, 3, 1, 3], [0, 2, 0, 2], [3, 3, 3, 3]]) (by decide +kernel) (by decide +kernel)

private def e50_1 : Fin 8 → SylowModel := ![decode 0, decode 64, decode 276, decode 1632, decode 0, decode 64, decode 20, decode 1376]
set_option maxHeartbeats 1600000 in
private theorem edgeEq50_1 : binaryFamily s50 (s50 0) (![true, false, false, false]) = e50_1 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert50_1 : Represented smallParityCensusNode (Subgroup.closure (Set.range e50_1)) := by
  refine ⟨91, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node91]
  exact closure_eq_words _ o91 (![[], [2, 4, 5, 6], [0], [1], [], [2, 4, 5, 6], [0, 6], [1, 5]]) (![[2], [3], [3, 1, 3, 3, 7], [3, 3], [1, 3, 3, 3, 1, 3], [2, 2], [2, 2, 2, 6]]) (by decide +kernel) (by decide +kernel)

private def e50_2 : Fin 8 → SylowModel := ![decode 400, decode 0, decode 276, decode 1632, decode 400, decode 0, decode 276, decode 1504]
set_option maxHeartbeats 1600000 in
private theorem edgeEq50_2 : binaryFamily s50 (s50 1) (![false, true, false, false]) = e50_2 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert50_2 : Represented smallParityCensusNode (Subgroup.closure (Set.range e50_2)) := by
  refine ⟨89, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node89]
  exact closure_eq_words _ o89 (![[0, 0, 3, 4], [], [0], [1], [0, 0, 3, 4], [], [0], [1, 4, 5]]) (![[2], [3], [3, 3], [0, 3, 3, 3, 7], [0, 3, 0, 3, 3, 7], [0, 2, 0, 2], [3, 3, 3, 3]]) (by decide +kernel) (by decide +kernel)

private def e50_3 : Fin 8 → SylowModel := ![decode 0, decode 464, decode 276, decode 1632, decode 0, decode 464, decode 20, decode 1376]
set_option maxHeartbeats 1600000 in
private theorem edgeEq50_3 : binaryFamily s50 (s50 0) (![true, true, false, false]) = e50_3 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert50_3 : Represented smallParityCensusNode (Subgroup.closure (Set.range e50_3)) := by
  refine ⟨92, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node92]
  exact closure_eq_words _ o92 (![[], [0, 2, 0], [0], [1], [], [0, 2, 0], [0, 6], [1, 5]]) (![[2], [3], [1, 2, 6], [3, 3], [1, 3, 3, 3, 1, 7], [2, 2], [2, 2, 2, 6]]) (by decide +kernel) (by decide +kernel)

private def e50_4 : Fin 8 → SylowModel := ![decode 400, decode 64, decode 0, decode 1632, decode 144, decode 64, decode 768, decode 1120]
set_option maxHeartbeats 1600000 in
private theorem edgeEq50_4 : binaryFamily s50 (s50 2) (![false, false, true, false]) = e50_4 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert50_4 : Represented smallParityCensusNode (Subgroup.closure (Set.range e50_4)) := by
  refine ⟨63, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node63]
  exact closure_eq_words _ o63 (![[1, 4, 5, 6], [3, 4, 5], [], [0], [1, 4, 5], [3, 4, 5], [4, 6], [0, 4]]) (![[3], [0, 1, 3, 1, 3, 3, 7], [3, 1, 3, 6], [3, 3, 3, 1, 7], [0, 4, 6], [1, 3, 3, 3, 1, 3], [0, 4]]) (by decide +kernel) (by decide +kernel)

private def e50_5 : Fin 8 → SylowModel := ![decode 0, decode 64, decode 132, decode 1632, decode 0, decode 64, decode 388, decode 1376]
set_option maxHeartbeats 1600000 in
private theorem edgeEq50_5 : binaryFamily s50 (s50 0) (![true, false, true, false]) = e50_5 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert50_5 : Represented smallParityCensusNode (Subgroup.closure (Set.range e50_5)) := by
  refine ⟨93, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node93]
  exact closure_eq_words _ o93 (![[], [0, 0, 2, 4], [0, 4], [1], [], [0, 0, 2, 4], [0, 4, 6], [1, 5]]) (![[1, 2, 3, 3, 3, 1, 3], [3], [3, 1, 3, 3, 7], [3, 3], [1, 3, 3, 3, 1, 3], [2, 6], [2, 2, 2, 6]]) (by decide +kernel) (by decide +kernel)

private def e50_6 : Fin 8 → SylowModel := ![decode 400, decode 0, decode 340, decode 1632, decode 400, decode 0, decode 340, decode 1504]
set_option maxHeartbeats 1600000 in
private theorem edgeEq50_6 : binaryFamily s50 (s50 1) (![false, true, true, false]) = e50_6 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert50_6 : Represented smallParityCensusNode (Subgroup.closure (Set.range e50_6)) := by
  refine ⟨90, root 1 * root 2 * root 4 * root 6 * root 7 * root 9, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node90]
  exact closure_eq_words _ o90 (![[3, 6], [], [0, 4, 6], [3, 1], [3, 6], [], [0, 4, 6], [3, 1, 4]]) (![[2, 3, 3, 3, 7], [0, 2, 7, 2], [7, 0, 3], [0, 3, 3, 3, 3], [3, 3, 7, 3], [0, 2, 0, 2], [3, 3, 3, 3]]) (by decide +kernel) (by decide +kernel)

private def e50_7 : Fin 8 → SylowModel := ![decode 0, decode 464, decode 132, decode 1632, decode 0, decode 464, decode 388, decode 1376]
set_option maxHeartbeats 1600000 in
private theorem edgeEq50_7 : binaryFamily s50 (s50 0) (![true, true, true, false]) = e50_7 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert50_7 : Represented smallParityCensusNode (Subgroup.closure (Set.range e50_7)) := by
  refine ⟨94, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node94]
  exact closure_eq_words _ o94 (![[], [0, 0, 2], [0, 4], [1], [], [0, 0, 2], [0, 4, 6], [1, 5]]) (![[1, 2, 3, 1, 3, 3, 7], [3], [1, 2, 2], [3, 3], [1, 3, 3, 3, 1, 7], [2, 6], [2, 2, 2, 6]]) (by decide +kernel) (by decide +kernel)

private def e50_8 : Fin 8 → SylowModel := ![decode 400, decode 64, decode 276, decode 0, decode 656, decode 960, decode 788, decode 2240]
set_option maxHeartbeats 1600000 in
private theorem edgeEq50_8 : binaryFamily s50 (s50 3) (![false, false, false, true]) = e50_8 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert50_8 : Subgroup.closure (Set.range e50_8) ≤ character.ker := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨j, rfl⟩
  exact (show ∀ j, e50_8 j ∈ character.ker from by decide +kernel) j

private def e50_9 : Fin 8 → SylowModel := ![decode 0, decode 64, decode 276, decode 1264, decode 0, decode 64, decode 20, decode 2032]
set_option maxHeartbeats 1600000 in
private theorem edgeEq50_9 : binaryFamily s50 (s50 0) (![true, false, false, true]) = e50_9 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert50_9 : Represented smallParityCensusNode (Subgroup.closure (Set.range e50_9)) := by
  refine ⟨91, root 2 * root 3 * root 4 * root 7, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node91]
  exact closure_eq_words _ o91 (![[], [2, 4], [0, 4, 5], [1, 4, 5], [], [2, 4], [0, 4, 5, 6], [1, 4]]) (![[1, 2, 3, 3, 3, 1, 7], [1, 2, 6, 3, 1], [3, 3, 3, 1, 3], [1, 3, 3, 1], [1, 3, 3, 3, 1, 3], [2, 2], [2, 2, 2, 6]]) (by decide +kernel) (by decide +kernel)

private def e50_10 : Fin 8 → SylowModel := ![decode 400, decode 0, decode 276, decode 1440, decode 400, decode 0, decode 276, decode 1568]
set_option maxHeartbeats 1600000 in
private theorem edgeEq50_10 : binaryFamily s50 (s50 1) (![false, true, false, true]) = e50_10 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert50_10 : Represented smallParityCensusNode (Subgroup.closure (Set.range e50_10)) := by
  refine ⟨89, root 2 * root 3 * root 4 * root 5 * root 6 * root 7 * root 9, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node89]
  exact closure_eq_words _ o89 (![[3, 4], [], [0, 4, 5], [1, 3, 6], [3, 4], [], [0, 4, 5], [3, 4, 1]]) (![[2, 3, 3, 7, 3], [0, 7], [0, 7, 0, 7], [3, 0, 3, 3, 7], [0, 3, 0, 3, 3, 7], [0, 2, 0, 2], [3, 3, 3, 3]]) (by decide +kernel) (by decide +kernel)

private def e50_11 : Fin 8 → SylowModel := ![decode 0, decode 464, decode 276, decode 1264, decode 0, decode 464, decode 20, decode 2032]
set_option maxHeartbeats 1600000 in
private theorem edgeEq50_11 : binaryFamily s50 (s50 0) (![true, true, false, true]) = e50_11 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert50_11 : Represented smallParityCensusNode (Subgroup.closure (Set.range e50_11)) := by
  refine ⟨92, root 2 * root 3 * root 4 * root 7, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node92]
  exact closure_eq_words _ o92 (![[], [2, 6], [0, 4, 5], [1, 4, 5], [], [2, 6], [0, 4, 5, 6], [1, 4]]) (![[1, 2, 3, 1, 3, 3, 3], [1, 2, 3, 1, 2], [1, 2, 2, 2, 6], [1, 3, 3, 1], [1, 3, 3, 3, 1, 7], [2, 2], [2, 2, 2, 6]]) (by decide +kernel) (by decide +kernel)

private def e50_12 : Fin 8 → SylowModel := ![decode 400, decode 64, decode 0, decode 1652, decode 144, decode 64, decode 768, decode 1908]
set_option maxHeartbeats 1600000 in
private theorem edgeEq50_12 : binaryFamily s50 (s50 2) (![false, false, true, true]) = e50_12 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert50_12 : Represented smallParityCensusNode (Subgroup.closure (Set.range e50_12)) := by
  refine ⟨71, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node71]
  exact closure_eq_words _ o71 (![[1, 5, 6], [3, 4, 5], [], [1, 5, 0], [1, 5], [3, 4, 5], [4, 6], [1, 0, 5]]) (![[0, 7], [0, 1, 3, 1, 3, 3, 3], [3, 1, 7], [3, 1, 3, 3, 3, 6], [0, 4, 6], [1, 3, 1, 3, 3, 7], [0, 4]]) (by decide +kernel) (by decide +kernel)

private def e50_13 : Fin 8 → SylowModel := ![decode 0, decode 64, decode 132, decode 1264, decode 0, decode 64, decode 388, decode 2032]
set_option maxHeartbeats 1600000 in
private theorem edgeEq50_13 : binaryFamily s50 (s50 0) (![true, false, true, true]) = e50_13 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert50_13 : Represented smallParityCensusNode (Subgroup.closure (Set.range e50_13)) := by
  refine ⟨93, root 2 * root 3 * root 4 * root 7, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node93]
  exact closure_eq_words _ o93 (![[], [2, 4], [0, 0, 0], [1, 4, 5], [], [2, 4], [0, 5], [1, 4]]) (![[2, 2, 2], [1, 2, 2, 3, 1], [3, 3, 3, 1, 3], [1, 3, 3, 1], [1, 3, 3, 3, 1, 3], [2, 6], [2, 2, 2, 6]]) (by decide +kernel) (by decide +kernel)

private def e50_14 : Fin 8 → SylowModel := ![decode 400, decode 0, decode 340, decode 1440, decode 400, decode 0, decode 340, decode 1568]
set_option maxHeartbeats 1600000 in
private theorem edgeEq50_14 : binaryFamily s50 (s50 1) (![false, true, true, true]) = e50_14 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert50_14 : Represented smallParityCensusNode (Subgroup.closure (Set.range e50_14)) := by
  refine ⟨90, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node90]
  exact closure_eq_words _ o90 (![[3, 5], [], [0, 0, 0], [0, 0, 1], [3, 5], [], [0, 0, 0], [4, 1, 5]]) (![[2, 2, 2], [0, 3, 0], [7, 0, 3], [2, 0, 2], [3, 3, 7, 3], [0, 2, 0, 2], [3, 3, 3, 3]]) (by decide +kernel) (by decide +kernel)

private def e50_15 : Fin 8 → SylowModel := ![decode 0, decode 464, decode 132, decode 1264, decode 0, decode 464, decode 388, decode 2032]
set_option maxHeartbeats 1600000 in
private theorem edgeEq50_15 : binaryFamily s50 (s50 0) (![true, true, true, true]) = e50_15 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert50_15 : Represented smallParityCensusNode (Subgroup.closure (Set.range e50_15)) := by
  refine ⟨94, root 2 * root 3 * root 4 * root 7, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node94]
  exact closure_eq_words _ o94 (![[], [2, 6], [0, 0, 0], [1, 4, 5], [], [2, 6], [0, 5], [1, 4]]) (![[2, 2, 2], [1, 2, 2, 7, 1], [1, 2, 2, 2, 6], [1, 3, 3, 1], [1, 3, 3, 3, 1, 7], [2, 6], [2, 2, 2, 6]]) (by decide +kernel) (by decide +kernel)

private def s51 : Fin 3 → SylowModel := ![rootOne ^ 3, root 2 * root 4 * root 8, root 5 * root 8]
set_option maxHeartbeats 1600000 in
private theorem gen51 : Subgroup.closure (Set.range s51) = smallParityCensusNode 51 := by
  rw [node51]
  exact closure_eq_words s51 o51 (![[1], [0], [2]]) (![[1], [0], [2], [0, 0], [0, 0, 0, 2, 0, 2], [1, 1], [0, 0, 2, 0, 0, 2], [1, 2, 1, 2]]) (by decide +kernel) (by decide +kernel)

private def e51_1 : Fin 6 → SylowModel := ![decode 0, decode 276, decode 288, decode 2048, decode 276, decode 608]
set_option maxHeartbeats 1600000 in
private theorem edgeEq51_1 : binaryFamily s51 (s51 0) (![true, false, false]) = e51_1 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert51_1 : Subgroup.closure (Set.range e51_1) ≤ character.ker := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨j, rfl⟩
  exact (show ∀ j, e51_1 j ∈ character.ker from by decide +kernel) j

private def e51_2 : Fin 6 → SylowModel := ![decode 1024, decode 0, decode 288, decode 1024, decode 768, decode 800]
set_option maxHeartbeats 1600000 in
private theorem edgeEq51_2 : binaryFamily s51 (s51 1) (![false, true, false]) = e51_2 := by decide +kernel
private def a51_2 (k : Fin 128) : SylowModel :=
  decode ((#[0, 1024, 2048, 64, 384, 768, 512, 3072, 1984, 1152, 1792, 1536, 2368, 2432, 2816, 2560, 224, 448, 832, 576, 640, 896, 256, 3776, 3200, 3840, 3584, 1312, 1856, 1216, 1472, 1920, 1664, 1280, 2656, 2240, 2624, 2880, 2688, 2944, 2304, 160, 352, 992, 736, 704, 960, 320, 128, 3744, 3648, 3520, 3264, 3968, 3712, 3328, 1760, 1440, 1568, 1824, 1088, 1344, 1728, 1408, 2848, 3040, 2400, 2144, 3008, 2752, 2112, 2176, 288, 928, 672, 608, 864, 480, 192, 3168, 3616, 3488, 3232, 3392, 3136, 4032, 3456, 1632, 1504, 1248, 1696, 1952, 1056, 1600, 2720, 2080, 2336, 2272, 2528, 2912, 2496, 544, 800, 416, 96, 3296, 3936, 3680, 3360, 3104, 4000, 3904, 1376, 1120, 2016, 1184, 2464, 2208, 2592, 2784, 32, 4064, 3808, 3424, 3872, 1888, 2976, 3552] : Array ℕ).getD k.val 0)
private def next51_2 (k : Fin 128) (j : Fin 6) : Fin 128 :=
  Fin.ofNat 128 (((#[#[1, 0, 72, 1, 5, 102],
    #[2, 1, 87, 2, 10, 113],
    #[7, 2, 94, 7, 14, 117],
    #[60, 3, 42, 60, 18, 76],
    #[63, 4, 41, 63, 20, 74],
    #[10, 5, 101, 10, 0, 120],
    #[11, 6, 102, 11, 22, 72],
    #[0, 7, 105, 0, 25, 122],
    #[68, 8, 57, 68, 29, 91],
    #[71, 9, 56, 71, 31, 89],
    #[14, 10, 112, 14, 1, 125],
    #[15, 11, 113, 15, 33, 87],
    #[83, 12, 65, 83, 36, 98],
    #[86, 13, 64, 86, 38, 96],
    #[25, 14, 116, 25, 2, 126],
    #[26, 15, 117, 26, 40, 94],
    #[89, 16, 17, 89, 43, 46],
    #[30, 17, 16, 30, 45, 44],
    #[28, 18, 75, 28, 3, 104],
    #[93, 19, 76, 93, 47, 42],
    #[32, 20, 73, 32, 4, 103],
    #[31, 21, 74, 31, 48, 41],
    #[33, 22, 120, 33, 6, 101],
    #[45, 23, 80, 45, 51, 109],
    #[48, 24, 79, 48, 53, 107],
    #[5, 25, 121, 5, 7, 127],
    #[6, 26, 122, 6, 55, 105],
    #[96, 27, 28, 96, 58, 61],
    #[37, 28, 27, 37, 60, 59],
    #[35, 29, 90, 35, 8, 115],
    #[100, 30, 91, 100, 62, 57],
    #[39, 31, 88, 39, 9, 114],
    #[38, 32, 89, 38, 63, 56],
    #[40, 33, 125, 40, 11, 112],
    #[107, 34, 35, 107, 66, 69],
    #[52, 35, 34, 52, 68, 67],
    #[50, 36, 97, 50, 12, 119],
    #[111, 37, 98, 111, 70, 65],
    #[54, 38, 95, 54, 13, 118],
    #[53, 39, 96, 53, 71, 64],
    #[55, 40, 126, 55, 15, 116],
    #[115, 41, 4, 115, 73, 21],
    #[112, 42, 3, 112, 75, 19],
    #[114, 43, 45, 114, 16, 78],
    #[56, 44, 46, 56, 77, 17],
    #[62, 45, 43, 62, 17, 77],
    #[8, 46, 44, 8, 78, 16],
    #[61, 47, 104, 61, 19, 75],
    #[9, 48, 103, 9, 21, 73],
    #[74, 49, 50, 74, 81, 84],
    #[19, 50, 49, 19, 83, 82],
    #[17, 51, 108, 17, 23, 124],
    #[78, 52, 109, 78, 85, 80],
    #[21, 53, 106, 21, 24, 123],
    #[20, 54, 107, 20, 86, 79],
    #[22, 55, 127, 22, 26, 121],
    #[119, 56, 9, 119, 88, 32],
    #[116, 57, 8, 116, 90, 30],
    #[118, 58, 60, 118, 27, 93],
    #[64, 59, 61, 64, 92, 28],
    #[70, 60, 58, 70, 28, 92],
    #[12, 61, 59, 12, 93, 27],
    #[69, 62, 115, 69, 30, 90],
    #[13, 63, 114, 13, 32, 88],
    #[124, 64, 13, 124, 95, 39],
    #[121, 65, 12, 121, 97, 37],
    #[123, 66, 68, 123, 34, 100],
    #[79, 67, 69, 79, 99, 35],
    #[85, 68, 66, 85, 35, 99],
    #[23, 69, 67, 23, 100, 34],
    #[84, 70, 119, 84, 37, 97],
    #[24, 71, 118, 24, 39, 95],
    #[27, 72, 0, 27, 101, 6],
    #[91, 73, 20, 91, 41, 48],
    #[90, 74, 21, 90, 103, 4],
    #[87, 75, 18, 87, 42, 47],
    #[125, 76, 19, 125, 104, 3],
    #[88, 77, 78, 88, 44, 45],
    #[29, 78, 77, 29, 46, 43],
    #[104, 79, 24, 104, 106, 54],
    #[101, 80, 23, 101, 108, 52],
    #[103, 81, 83, 103, 49, 111],
    #[41, 82, 84, 41, 110, 50],
    #[47, 83, 81, 47, 50, 110],
    #[3, 84, 82, 3, 111, 49],
    #[46, 85, 124, 46, 52, 108],
    #[4, 86, 123, 4, 54, 106],
    #[34, 87, 1, 34, 112, 11],
    #[98, 88, 31, 98, 56, 63],
    #[97, 89, 32, 97, 114, 9],
    #[94, 90, 29, 94, 57, 62],
    #[126, 91, 30, 126, 115, 8],
    #[95, 92, 93, 95, 59, 60],
    #[36, 93, 92, 36, 61, 58],
    #[49, 94, 2, 49, 116, 15],
    #[109, 95, 38, 109, 64, 71],
    #[108, 96, 39, 108, 118, 13],
    #[105, 97, 36, 105, 65, 70],
    #[127, 98, 37, 127, 119, 12],
    #[106, 99, 100, 106, 67, 68],
    #[51, 100, 99, 51, 69, 66],
    #[58, 101, 5, 58, 72, 22],
    #[59, 102, 6, 59, 120, 0],
    #[57, 103, 48, 57, 74, 20],
    #[113, 104, 47, 113, 76, 18],
    #[16, 105, 7, 16, 121, 26],
    #[76, 106, 53, 76, 79, 86],
    #[75, 107, 54, 75, 123, 24],
    #[72, 108, 51, 72, 80, 85],
    #[120, 109, 52, 120, 124, 23],
    #[73, 110, 111, 73, 82, 83],
    #[18, 111, 110, 18, 84, 81],
    #[66, 112, 10, 66, 87, 33],
    #[67, 113, 11, 67, 125, 1],
    #[65, 114, 63, 65, 89, 31],
    #[117, 115, 62, 117, 91, 29],
    #[81, 116, 14, 81, 94, 40],
    #[82, 117, 15, 82, 126, 2],
    #[80, 118, 71, 80, 96, 38],
    #[122, 119, 70, 122, 98, 36],
    #[92, 120, 22, 92, 102, 5],
    #[43, 121, 25, 43, 105, 55],
    #[44, 122, 26, 44, 127, 7],
    #[42, 123, 86, 42, 107, 53],
    #[102, 124, 85, 102, 109, 51],
    #[99, 125, 33, 99, 113, 10],
    #[110, 126, 40, 110, 117, 14],
    #[77, 127, 55, 77, 122, 25]] : Array (Array ℕ)).getD k.val #[]).getD j.val 0)
private def prev51_2 (k : Fin 128) (j : Fin 6) : Fin 128 :=
  Fin.ofNat 128 (((#[#[7, 0, 72, 7, 5, 102],
    #[0, 1, 87, 0, 10, 113],
    #[1, 2, 94, 1, 14, 117],
    #[84, 3, 42, 84, 18, 76],
    #[86, 4, 41, 86, 20, 74],
    #[25, 5, 101, 25, 0, 120],
    #[26, 6, 102, 26, 22, 72],
    #[2, 7, 105, 2, 25, 122],
    #[46, 8, 57, 46, 29, 91],
    #[48, 9, 56, 48, 31, 89],
    #[5, 10, 112, 5, 1, 125],
    #[6, 11, 113, 6, 33, 87],
    #[61, 12, 65, 61, 36, 98],
    #[63, 13, 64, 63, 38, 96],
    #[10, 14, 116, 10, 2, 126],
    #[11, 15, 117, 11, 40, 94],
    #[105, 16, 17, 105, 43, 46],
    #[51, 17, 16, 51, 45, 44],
    #[111, 18, 75, 111, 3, 104],
    #[50, 19, 76, 50, 47, 42],
    #[54, 20, 73, 54, 4, 103],
    #[53, 21, 74, 53, 48, 41],
    #[55, 22, 120, 55, 6, 101],
    #[69, 23, 80, 69, 51, 109],
    #[71, 24, 79, 71, 53, 107],
    #[14, 25, 121, 14, 7, 127],
    #[15, 26, 122, 15, 55, 105],
    #[72, 27, 28, 72, 58, 61],
    #[18, 28, 27, 18, 60, 59],
    #[78, 29, 90, 78, 8, 115],
    #[17, 30, 91, 17, 62, 57],
    #[21, 31, 88, 21, 9, 114],
    #[20, 32, 89, 20, 63, 56],
    #[22, 33, 125, 22, 11, 112],
    #[87, 34, 35, 87, 66, 69],
    #[29, 35, 34, 29, 68, 67],
    #[93, 36, 97, 93, 12, 119],
    #[28, 37, 98, 28, 70, 65],
    #[32, 38, 95, 32, 13, 118],
    #[31, 39, 96, 31, 71, 64],
    #[33, 40, 126, 33, 15, 116],
    #[82, 41, 4, 82, 73, 21],
    #[123, 42, 3, 123, 75, 19],
    #[121, 43, 45, 121, 16, 78],
    #[122, 44, 46, 122, 77, 17],
    #[23, 45, 43, 23, 17, 77],
    #[85, 46, 44, 85, 78, 16],
    #[83, 47, 104, 83, 19, 75],
    #[24, 48, 103, 24, 21, 73],
    #[94, 49, 50, 94, 81, 84],
    #[36, 50, 49, 36, 83, 82],
    #[100, 51, 108, 100, 23, 124],
    #[35, 52, 109, 35, 85, 80],
    #[39, 53, 106, 39, 24, 123],
    #[38, 54, 107, 38, 86, 79],
    #[40, 55, 127, 40, 26, 121],
    #[44, 56, 9, 44, 88, 32],
    #[103, 57, 8, 103, 90, 30],
    #[101, 58, 60, 101, 27, 93],
    #[102, 59, 61, 102, 92, 28],
    #[3, 60, 58, 3, 28, 92],
    #[47, 61, 59, 47, 93, 27],
    #[45, 62, 115, 45, 30, 90],
    #[4, 63, 114, 4, 32, 88],
    #[59, 64, 13, 59, 95, 39],
    #[114, 65, 12, 114, 97, 37],
    #[112, 66, 68, 112, 34, 100],
    #[113, 67, 69, 113, 99, 35],
    #[8, 68, 66, 8, 35, 99],
    #[62, 69, 67, 62, 100, 34],
    #[60, 70, 119, 60, 37, 97],
    #[9, 71, 118, 9, 39, 95],
    #[108, 72, 0, 108, 101, 6],
    #[110, 73, 20, 110, 41, 48],
    #[49, 74, 21, 49, 103, 4],
    #[107, 75, 18, 107, 42, 47],
    #[106, 76, 19, 106, 104, 3],
    #[127, 77, 78, 127, 44, 45],
    #[52, 78, 77, 52, 46, 43],
    #[67, 79, 24, 67, 106, 54],
    #[118, 80, 23, 118, 108, 52],
    #[116, 81, 83, 116, 49, 111],
    #[117, 82, 84, 117, 110, 50],
    #[12, 83, 81, 12, 50, 110],
    #[70, 84, 82, 70, 111, 49],
    #[68, 85, 124, 68, 52, 108],
    #[13, 86, 123, 13, 54, 106],
    #[75, 87, 1, 75, 112, 11],
    #[77, 88, 31, 77, 56, 63],
    #[16, 89, 32, 16, 114, 9],
    #[74, 90, 29, 74, 57, 62],
    #[73, 91, 30, 73, 115, 8],
    #[120, 92, 93, 120, 59, 60],
    #[19, 93, 92, 19, 61, 58],
    #[90, 94, 2, 90, 116, 15],
    #[92, 95, 38, 92, 64, 71],
    #[27, 96, 39, 27, 118, 13],
    #[89, 97, 36, 89, 65, 70],
    #[88, 98, 37, 88, 119, 12],
    #[125, 99, 100, 125, 67, 68],
    #[30, 100, 99, 30, 69, 66],
    #[80, 101, 5, 80, 72, 22],
    #[124, 102, 6, 124, 120, 0],
    #[81, 103, 48, 81, 74, 20],
    #[79, 104, 47, 79, 76, 18],
    #[97, 105, 7, 97, 121, 26],
    #[99, 106, 53, 99, 79, 86],
    #[34, 107, 54, 34, 123, 24],
    #[96, 108, 51, 96, 80, 85],
    #[95, 109, 52, 95, 124, 23],
    #[126, 110, 111, 126, 82, 83],
    #[37, 111, 110, 37, 84, 81],
    #[42, 112, 10, 42, 87, 33],
    #[104, 113, 11, 104, 125, 1],
    #[43, 114, 63, 43, 89, 31],
    #[41, 115, 62, 41, 91, 29],
    #[57, 116, 14, 57, 94, 40],
    #[115, 117, 15, 115, 126, 2],
    #[58, 118, 71, 58, 96, 38],
    #[56, 119, 70, 56, 98, 36],
    #[109, 120, 22, 109, 102, 5],
    #[65, 121, 25, 65, 105, 55],
    #[119, 122, 26, 119, 127, 7],
    #[66, 123, 86, 66, 107, 53],
    #[64, 124, 85, 64, 109, 51],
    #[76, 125, 33, 76, 113, 10],
    #[91, 126, 40, 91, 117, 14],
    #[98, 127, 55, 98, 122, 25]] : Array (Array ℕ)).getD k.val #[]).getD j.val 0)
set_option maxHeartbeats 1600000 in
private theorem cert51_2 : ∃ c, c ∈ Subgroup.centralizer (Subgroup.closure (Set.range e51_2) : Set SylowModel) ∧ c ∉ Subgroup.closure (Set.range e51_2) := by
  refine ⟨root 2 * root 8, centralizes_generators e51_2 _ (by decide +kernel), ?_⟩
  exact outside_of_table e51_2 a51_2 0 next51_2 prev51_2
    (by decide +kernel) (by decide +kernel) (by decide +kernel) _ (by decide +kernel)

private def e51_3 : Fin 6 → SylowModel := ![decode 0, decode 3348, decode 288, decode 2048, decode 1300, decode 608]
set_option maxHeartbeats 1600000 in
private theorem edgeEq51_3 : binaryFamily s51 (s51 0) (![true, true, false]) = e51_3 := by decide +kernel
private def a51_3 (k : Fin 128) : SylowModel :=
  decode ((#[0, 2048, 64, 384, 768, 512, 2368, 2432, 2816, 2560, 224, 448, 832, 576, 640, 896, 256, 2656, 2240, 2624, 2880, 2688, 2944, 2304, 160, 352, 992, 736, 704, 960, 320, 128, 2848, 3040, 2400, 2144, 3008, 2752, 2112, 2176, 288, 928, 672, 608, 864, 480, 192, 1076, 1172, 2720, 2080, 2336, 2272, 2528, 2912, 2496, 544, 800, 416, 96, 4020, 3220, 2036, 1204, 1844, 1588, 1876, 1044, 1940, 1684, 2464, 2208, 2592, 2784, 32, 3444, 3892, 3252, 3508, 3668, 3092, 3988, 3732, 1908, 1268, 1524, 1972, 1716, 1332, 2004, 1108, 1364, 1812, 1556, 1428, 2976, 3572, 3700, 3956, 3124, 3380, 3764, 3796, 3412, 3156, 3860, 3604, 3476, 1140, 1396, 1780, 1460, 1236, 1492, 1620, 1300, 3828, 4084, 3188, 3636, 3540, 3284, 3924, 3348, 1652, 1748, 3316, 4052] : Array ℕ).getD k.val 0)
private def next51_3 (k : Fin 128) (j : Fin 6) : Fin 128 :=
  Fin.ofNat 128 (((#[#[0, 123, 40, 1, 115, 43],
    #[1, 115, 49, 0, 123, 52],
    #[2, 103, 25, 38, 91, 56],
    #[3, 61, 24, 7, 48, 26],
    #[4, 106, 56, 8, 93, 25],
    #[5, 105, 57, 9, 92, 59],
    #[6, 90, 33, 30, 104, 70],
    #[7, 48, 32, 3, 61, 34],
    #[8, 93, 70, 4, 106, 33],
    #[9, 92, 71, 5, 105, 73],
    #[10, 117, 11, 52, 62, 14],
    #[11, 121, 10, 55, 112, 41],
    #[12, 79, 43, 20, 114, 40],
    #[13, 122, 44, 19, 66, 74],
    #[14, 81, 41, 21, 68, 10],
    #[15, 82, 42, 22, 69, 45],
    #[16, 80, 74, 23, 67, 44],
    #[17, 109, 18, 43, 75, 21],
    #[18, 113, 17, 46, 120, 50],
    #[19, 66, 52, 13, 122, 49],
    #[20, 114, 53, 12, 79, 95],
    #[21, 68, 50, 14, 81, 17],
    #[22, 69, 51, 15, 82, 54],
    #[23, 67, 95, 16, 80, 53],
    #[24, 60, 3, 71, 86, 28],
    #[25, 97, 2, 34, 124, 4],
    #[26, 126, 28, 33, 84, 3],
    #[27, 96, 29, 73, 85, 31],
    #[28, 127, 26, 37, 89, 24],
    #[29, 102, 27, 36, 125, 58],
    #[30, 104, 59, 6, 90, 57],
    #[31, 107, 58, 39, 94, 27],
    #[32, 47, 7, 57, 99, 36],
    #[33, 84, 6, 26, 126, 8],
    #[34, 124, 36, 25, 97, 7],
    #[35, 83, 37, 59, 98, 39],
    #[36, 125, 34, 29, 102, 32],
    #[37, 89, 35, 28, 127, 72],
    #[38, 91, 73, 2, 103, 71],
    #[39, 94, 72, 31, 107, 35],
    #[40, 119, 0, 51, 65, 12],
    #[41, 77, 14, 95, 63, 11],
    #[42, 78, 15, 49, 111, 46],
    #[43, 75, 12, 17, 109, 0],
    #[44, 118, 13, 54, 108, 16],
    #[45, 116, 46, 53, 110, 15],
    #[46, 120, 45, 18, 113, 42],
    #[47, 74, 114, 99, 50, 69],
    #[48, 14, 110, 61, 21, 65],
    #[49, 111, 1, 42, 78, 19],
    #[50, 64, 21, 74, 76, 18],
    #[51, 65, 22, 40, 119, 55],
    #[52, 62, 19, 10, 117, 1],
    #[53, 110, 20, 45, 116, 23],
    #[54, 108, 55, 44, 118, 22],
    #[55, 112, 54, 11, 121, 51],
    #[56, 100, 4, 72, 88, 2],
    #[57, 99, 5, 32, 47, 30],
    #[58, 101, 31, 70, 87, 29],
    #[59, 98, 30, 35, 83, 5],
    #[60, 95, 122, 86, 41, 82],
    #[61, 21, 118, 48, 14, 78],
    #[62, 26, 94, 117, 33, 91],
    #[63, 24, 125, 77, 71, 93],
    #[64, 57, 91, 76, 32, 94],
    #[65, 56, 90, 119, 72, 48],
    #[66, 30, 88, 122, 6, 85],
    #[67, 5, 124, 80, 9, 87],
    #[68, 3, 85, 81, 7, 88],
    #[69, 31, 84, 82, 39, 47],
    #[70, 87, 8, 58, 101, 6],
    #[71, 86, 9, 24, 60, 38],
    #[72, 88, 39, 56, 100, 37],
    #[73, 85, 38, 27, 96, 9],
    #[74, 76, 16, 50, 64, 13],
    #[75, 34, 107, 109, 25, 104],
    #[76, 32, 127, 64, 57, 106],
    #[77, 71, 104, 63, 24, 107],
    #[78, 70, 103, 111, 58, 61],
    #[79, 38, 101, 114, 2, 98],
    #[80, 9, 126, 67, 5, 100],
    #[81, 7, 98, 68, 3, 101],
    #[82, 39, 97, 69, 31, 60],
    #[83, 44, 115, 98, 54, 113],
    #[84, 10, 69, 126, 52, 114],
    #[85, 45, 68, 96, 53, 66],
    #[86, 41, 113, 60, 95, 115],
    #[87, 42, 112, 101, 49, 67],
    #[88, 40, 66, 100, 51, 68],
    #[89, 11, 111, 127, 55, 109],
    #[90, 13, 65, 104, 19, 110],
    #[91, 12, 64, 103, 20, 62],
    #[92, 16, 109, 105, 23, 111],
    #[93, 0, 108, 106, 1, 63],
    #[94, 15, 62, 107, 22, 64],
    #[95, 63, 23, 41, 77, 20],
    #[96, 53, 123, 85, 45, 121],
    #[97, 17, 82, 124, 43, 122],
    #[98, 54, 81, 83, 44, 79],
    #[99, 50, 121, 47, 74, 123],
    #[100, 51, 120, 88, 40, 80],
    #[101, 49, 79, 87, 42, 81],
    #[102, 18, 119, 125, 46, 117],
    #[103, 20, 78, 91, 12, 118],
    #[104, 19, 77, 90, 13, 75],
    #[105, 23, 117, 92, 16, 119],
    #[106, 1, 116, 93, 0, 76],
    #[107, 22, 75, 94, 15, 77],
    #[108, 59, 93, 118, 35, 125],
    #[109, 25, 92, 75, 34, 89],
    #[110, 27, 48, 116, 73, 90],
    #[111, 58, 89, 78, 70, 92],
    #[112, 28, 87, 121, 37, 124],
    #[113, 29, 86, 120, 36, 83],
    #[114, 2, 47, 79, 38, 84],
    #[115, 4, 83, 123, 8, 86],
    #[116, 73, 106, 110, 27, 127],
    #[117, 33, 105, 62, 26, 102],
    #[118, 35, 61, 108, 59, 103],
    #[119, 72, 102, 65, 56, 105],
    #[120, 36, 100, 113, 29, 126],
    #[121, 37, 99, 112, 28, 96],
    #[122, 6, 60, 66, 30, 97],
    #[123, 8, 96, 115, 4, 99],
    #[124, 43, 67, 97, 17, 112],
    #[125, 46, 63, 102, 18, 108],
    #[126, 52, 80, 84, 10, 120],
    #[127, 55, 76, 89, 11, 116]] : Array (Array ℕ)).getD k.val #[]).getD j.val 0)
private def prev51_3 (k : Fin 128) (j : Fin 6) : Fin 128 :=
  Fin.ofNat 128 (((#[#[0, 93, 40, 1, 106, 43],
    #[1, 106, 49, 0, 93, 52],
    #[2, 114, 25, 38, 79, 56],
    #[3, 68, 24, 7, 81, 26],
    #[4, 115, 56, 8, 123, 25],
    #[5, 67, 57, 9, 80, 59],
    #[6, 122, 33, 30, 66, 70],
    #[7, 81, 32, 3, 68, 34],
    #[8, 123, 70, 4, 115, 33],
    #[9, 80, 71, 5, 67, 73],
    #[10, 84, 11, 52, 126, 14],
    #[11, 89, 10, 55, 127, 41],
    #[12, 91, 43, 20, 103, 40],
    #[13, 90, 44, 19, 104, 74],
    #[14, 48, 41, 21, 61, 10],
    #[15, 94, 42, 22, 107, 45],
    #[16, 92, 74, 23, 105, 44],
    #[17, 97, 18, 43, 124, 21],
    #[18, 102, 17, 46, 125, 50],
    #[19, 104, 52, 13, 90, 49],
    #[20, 103, 53, 12, 91, 95],
    #[21, 61, 50, 14, 48, 17],
    #[22, 107, 51, 15, 94, 54],
    #[23, 105, 95, 16, 92, 53],
    #[24, 63, 3, 71, 77, 28],
    #[25, 109, 2, 34, 75, 4],
    #[26, 62, 28, 33, 117, 3],
    #[27, 110, 29, 73, 116, 31],
    #[28, 112, 26, 37, 121, 24],
    #[29, 113, 27, 36, 120, 58],
    #[30, 66, 59, 6, 122, 57],
    #[31, 69, 58, 39, 82, 27],
    #[32, 76, 7, 57, 64, 36],
    #[33, 117, 6, 26, 62, 8],
    #[34, 75, 36, 25, 109, 7],
    #[35, 118, 37, 59, 108, 39],
    #[36, 120, 34, 29, 113, 32],
    #[37, 121, 35, 28, 112, 72],
    #[38, 79, 73, 2, 114, 71],
    #[39, 82, 72, 31, 69, 35],
    #[40, 88, 0, 51, 100, 12],
    #[41, 86, 14, 95, 60, 11],
    #[42, 87, 15, 49, 101, 46],
    #[43, 124, 12, 17, 97, 0],
    #[44, 83, 13, 54, 98, 16],
    #[45, 85, 46, 53, 96, 15],
    #[46, 125, 45, 18, 102, 42],
    #[47, 32, 114, 99, 57, 69],
    #[48, 7, 110, 61, 3, 65],
    #[49, 101, 1, 42, 87, 19],
    #[50, 99, 21, 74, 47, 18],
    #[51, 100, 22, 40, 88, 55],
    #[52, 126, 19, 10, 84, 1],
    #[53, 96, 20, 45, 85, 23],
    #[54, 98, 55, 44, 83, 22],
    #[55, 127, 54, 11, 89, 51],
    #[56, 65, 4, 72, 119, 2],
    #[57, 64, 5, 32, 76, 30],
    #[58, 111, 31, 70, 78, 29],
    #[59, 108, 30, 35, 118, 5],
    #[60, 24, 122, 86, 71, 82],
    #[61, 3, 118, 48, 7, 78],
    #[62, 52, 94, 117, 10, 91],
    #[63, 95, 125, 77, 41, 93],
    #[64, 50, 91, 76, 74, 94],
    #[65, 51, 90, 119, 40, 48],
    #[66, 19, 88, 122, 13, 85],
    #[67, 23, 124, 80, 16, 87],
    #[68, 21, 85, 81, 14, 88],
    #[69, 22, 84, 82, 15, 47],
    #[70, 78, 8, 58, 111, 6],
    #[71, 77, 9, 24, 63, 38],
    #[72, 119, 39, 56, 65, 37],
    #[73, 116, 38, 27, 110, 9],
    #[74, 47, 16, 50, 99, 13],
    #[75, 43, 107, 109, 17, 104],
    #[76, 74, 127, 64, 50, 106],
    #[77, 41, 104, 63, 95, 107],
    #[78, 42, 103, 111, 49, 61],
    #[79, 12, 101, 114, 20, 98],
    #[80, 16, 126, 67, 23, 100],
    #[81, 14, 98, 68, 21, 101],
    #[82, 15, 97, 69, 22, 60],
    #[83, 35, 115, 98, 59, 113],
    #[84, 33, 69, 126, 26, 114],
    #[85, 73, 68, 96, 27, 66],
    #[86, 71, 113, 60, 24, 115],
    #[87, 70, 112, 101, 58, 67],
    #[88, 72, 66, 100, 56, 68],
    #[89, 37, 111, 127, 28, 109],
    #[90, 6, 65, 104, 30, 110],
    #[91, 38, 64, 103, 2, 62],
    #[92, 9, 109, 105, 5, 111],
    #[93, 8, 108, 106, 4, 63],
    #[94, 39, 62, 107, 31, 64],
    #[95, 60, 23, 41, 86, 20],
    #[96, 27, 123, 85, 73, 121],
    #[97, 25, 82, 124, 34, 122],
    #[98, 59, 81, 83, 35, 79],
    #[99, 57, 121, 47, 32, 123],
    #[100, 56, 120, 88, 72, 80],
    #[101, 58, 79, 87, 70, 81],
    #[102, 29, 119, 125, 36, 117],
    #[103, 2, 78, 91, 38, 118],
    #[104, 30, 77, 90, 6, 75],
    #[105, 5, 117, 92, 9, 119],
    #[106, 4, 116, 93, 8, 76],
    #[107, 31, 75, 94, 39, 77],
    #[108, 54, 93, 118, 44, 125],
    #[109, 17, 92, 75, 43, 89],
    #[110, 53, 48, 116, 45, 90],
    #[111, 49, 89, 78, 42, 92],
    #[112, 55, 87, 121, 11, 124],
    #[113, 18, 86, 120, 46, 83],
    #[114, 20, 47, 79, 12, 84],
    #[115, 1, 83, 123, 0, 86],
    #[116, 45, 106, 110, 53, 127],
    #[117, 10, 105, 62, 52, 102],
    #[118, 44, 61, 108, 54, 103],
    #[119, 40, 102, 65, 51, 105],
    #[120, 46, 100, 113, 18, 126],
    #[121, 11, 99, 112, 55, 96],
    #[122, 13, 60, 66, 19, 97],
    #[123, 0, 96, 115, 1, 99],
    #[124, 34, 67, 97, 25, 112],
    #[125, 36, 63, 102, 29, 108],
    #[126, 26, 80, 84, 33, 120],
    #[127, 28, 76, 89, 37, 116]] : Array (Array ℕ)).getD k.val #[]).getD j.val 0)
set_option maxHeartbeats 1600000 in
private theorem cert51_3 : ∃ c, c ∈ Subgroup.centralizer (Subgroup.closure (Set.range e51_3) : Set SylowModel) ∧ c ∉ Subgroup.closure (Set.range e51_3) := by
  refine ⟨root 2 * root 7, centralizes_generators e51_3 _ (by decide +kernel), ?_⟩
  exact outside_of_table e51_3 a51_3 0 next51_3 prev51_3
    (by decide +kernel) (by decide +kernel) (by decide +kernel) _ (by decide +kernel)

private def e51_4 : Fin 6 → SylowModel := ![decode 1024, decode 276, decode 0, decode 1856, decode 788, decode 0]
set_option maxHeartbeats 1600000 in
private theorem edgeEq51_4 : binaryFamily s51 (s51 2) (![false, false, true]) = e51_4 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert51_4 : Represented smallParityCensusNode (Subgroup.closure (Set.range e51_4)) := by
  refine ⟨83, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node83]
  exact closure_eq_words _ o83 (![[1], [0], [], [1, 2], [0, 5, 6], []]) (![[1], [0], [0, 0, 0, 3], [0, 0], [0, 0, 3, 3], [1, 1], [1, 4]]) (by decide +kernel) (by decide +kernel)

private def e51_5 : Fin 6 → SylowModel := ![decode 0, decode 276, decode 3360, decode 2048, decode 276, decode 1632]
set_option maxHeartbeats 1600000 in
private theorem edgeEq51_5 : binaryFamily s51 (s51 0) (![true, false, true]) = e51_5 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert51_5 : Represented smallParityCensusNode (Subgroup.closure (Set.range e51_5)) := by
  refine ⟨91, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node91]
  exact closure_eq_words _ o91 (![[], [0], [1, 3, 6], [3, 2], [0], [1]]) (![[1], [5], [2, 2, 3], [5, 5], [2, 3, 5, 3], [1, 1], [1, 2, 1, 5]]) (by decide +kernel) (by decide +kernel)

private def e51_6 : Fin 6 → SylowModel := ![decode 1024, decode 0, decode 308, decode 1024, decode 768, decode 52]
set_option maxHeartbeats 1600000 in
private theorem edgeEq51_6 : binaryFamily s51 (s51 1) (![false, true, true]) = e51_6 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert51_6 : Represented smallParityCensusNode (Subgroup.closure (Set.range e51_6)) := by
  refine ⟨87, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node87]
  exact closure_eq_words _ o87 (![[1], [], [0, 4], [1], [4], [0, 4, 6]]) (![[2, 4], [0], [0, 0], [0, 0, 0, 2, 0, 5], [4], [0, 0, 2, 0, 0, 5], [2, 2]]) (by decide +kernel) (by decide +kernel)

private def e51_7 : Fin 6 → SylowModel := ![decode 0, decode 3348, decode 3360, decode 2048, decode 1300, decode 1632]
set_option maxHeartbeats 1600000 in
private theorem edgeEq51_7 : binaryFamily s51 (s51 0) (![true, true, true]) = e51_7 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert51_7 : Represented smallParityCensusNode (Subgroup.closure (Set.range e51_7)) := by
  refine ⟨88, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node88]
  exact closure_eq_words _ o88 (![[], [0, 1, 2, 4], [3, 1, 2, 4], [3, 2, 4], [1, 0], [0, 1, 0, 4]]) (![[5, 1], [3, 2], [2, 4, 5, 4], [1, 2, 2, 1], [1, 4], [2, 1, 2, 1], [1, 5, 1, 5]]) (by decide +kernel) (by decide +kernel)

private def s52 : Fin 3 → SylowModel := ![rootOne ^ 3, root 2 * root 4 * root 8, root 4 * root 5 * root 8 * root 9]
set_option maxHeartbeats 1600000 in
private theorem gen52 : Subgroup.closure (Set.range s52) = smallParityCensusNode 52 := by
  rw [node52]
  exact closure_eq_words s52 o52 (![[1], [0], [2]]) (![[1], [0], [2], [0, 0], [0, 0, 0, 2, 0, 2, 2, 2], [1, 1], [0, 0, 2, 0, 0, 2, 2, 2], [1, 1, 2, 2]]) (by decide +kernel) (by decide +kernel)

private def e52_1 : Fin 6 → SylowModel := ![decode 0, decode 276, decode 816, decode 2048, decode 276, decode 112]
set_option maxHeartbeats 1600000 in
private theorem edgeEq52_1 : binaryFamily s52 (s52 0) (![true, false, false]) = e52_1 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert52_1 : Subgroup.closure (Set.range e52_1) ≤ character.ker := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨j, rfl⟩
  exact (show ∀ j, e52_1 j ∈ character.ker from by decide +kernel) j

private def e52_2 : Fin 6 → SylowModel := ![decode 1024, decode 0, decode 816, decode 1024, decode 768, decode 48]
set_option maxHeartbeats 1600000 in
private theorem edgeEq52_2 : binaryFamily s52 (s52 1) (![false, true, false]) = e52_2 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert52_2 : Represented smallParityCensusNode (Subgroup.closure (Set.range e52_2)) := by
  refine ⟨62, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node62]
  exact closure_eq_words _ o62 (![[0], [], [1, 6], [0], [4, 6], [1, 4]]) (![[0], [2, 2, 5], [0, 0], [0, 2, 0, 5, 0, 0], [2, 2], [0, 2, 0, 0, 5, 0], [2, 5]]) (by decide +kernel) (by decide +kernel)

private def e52_3 : Fin 6 → SylowModel := ![decode 0, decode 3348, decode 816, decode 2048, decode 1300, decode 112]
set_option maxHeartbeats 1600000 in
private theorem edgeEq52_3 : binaryFamily s52 (s52 0) (![true, true, false]) = e52_3 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert52_3 : Represented smallParityCensusNode (Subgroup.closure (Set.range e52_3)) := by
  refine ⟨70, root 1 * root 2 * root 4 * root 5 * root 7 * root 9, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node70]
  exact closure_eq_words _ o70 (![[], [1, 2, 1, 0], [1], [2, 4], [5, 0], [1, 3, 4, 5, 6]]) (![[3, 5, 1, 2], [2], [2, 2, 3], [1, 2, 4, 2], [2, 2], [1, 1, 5, 3, 5], [1, 2, 2, 4]]) (by decide +kernel) (by decide +kernel)

private def e52_4 : Fin 6 → SylowModel := ![decode 1024, decode 276, decode 0, decode 1856, decode 532, decode 512]
set_option maxHeartbeats 1600000 in
private theorem edgeEq52_4 : binaryFamily s52 (s52 2) (![false, false, true]) = e52_4 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert52_4 : Represented smallParityCensusNode (Subgroup.closure (Set.range e52_4)) := by
  refine ⟨83, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node83]
  exact closure_eq_words _ o83 (![[1], [0], [], [1, 2], [0, 5], [5, 6]]) (![[1], [0], [0, 0, 0, 3], [0, 0], [0, 0, 3, 3], [1, 1], [1, 1, 5]]) (by decide +kernel) (by decide +kernel)

private def e52_5 : Fin 6 → SylowModel := ![decode 0, decode 276, decode 3888, decode 2048, decode 276, decode 1136]
set_option maxHeartbeats 1600000 in
private theorem edgeEq52_5 : binaryFamily s52 (s52 0) (![true, false, true]) = e52_5 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert52_5 : Represented smallParityCensusNode (Subgroup.closure (Set.range e52_5)) := by
  refine ⟨91, root 2 * root 3 * root 4 * root 7, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node91]
  exact closure_eq_words _ o91 (![[], [0, 4, 5], [1, 3, 5, 6], [3, 2], [0, 4, 5], [1, 6]]) (![[1, 3, 5, 3, 2], [1, 1, 2, 5, 5], [2, 2, 3], [5, 5], [1, 1, 3, 5, 3, 2], [1, 1], [1, 1, 2, 5]]) (by decide +kernel) (by decide +kernel)

private def e52_6 : Fin 6 → SylowModel := ![decode 1024, decode 0, decode 548, decode 1024, decode 768, decode 548]
set_option maxHeartbeats 1600000 in
private theorem edgeEq52_6 : binaryFamily s52 (s52 1) (![false, true, true]) = e52_6 := by decide +kernel
private def a52_6 (k : Fin 128) : SylowModel :=
  decode ((#[0, 1024, 2048, 64, 384, 768, 512, 3072, 1984, 1152, 1792, 1536, 2368, 2432, 2816, 2560, 448, 832, 576, 640, 896, 256, 3776, 3200, 3840, 3584, 1856, 1216, 1472, 1920, 1664, 1280, 2240, 2624, 2880, 2688, 2944, 2304, 704, 960, 320, 128, 1700, 228, 3648, 3520, 3264, 3968, 3712, 3328, 1088, 1344, 1728, 1408, 3008, 2752, 2112, 2176, 192, 3364, 1380, 1572, 1444, 1188, 2660, 164, 356, 996, 740, 3392, 3136, 4032, 3456, 1600, 2496, 4068, 3492, 3620, 3876, 1508, 1636, 1892, 1316, 1060, 1956, 2852, 3044, 2404, 2148, 292, 932, 676, 612, 868, 484, 3904, 3940, 3300, 3556, 3748, 4004, 3108, 1764, 2020, 1124, 1828, 2724, 2084, 2340, 2276, 2532, 2916, 548, 804, 420, 100, 3172, 3428, 3812, 3236, 1252, 2468, 2212, 2596, 2788, 36, 3684, 2980] : Array ℕ).getD k.val 0)
private def next52_6 (k : Fin 128) (j : Fin 6) : Fin 128 :=
  Fin.ofNat 128 (((#[#[1, 0, 112, 1, 5, 112],
    #[2, 1, 60, 2, 10, 60],
    #[7, 2, 121, 7, 14, 121],
    #[50, 3, 92, 50, 17, 92],
    #[53, 4, 90, 53, 19, 90],
    #[10, 5, 89, 10, 0, 89],
    #[11, 6, 125, 11, 21, 125],
    #[0, 7, 75, 0, 24, 75],
    #[54, 8, 42, 54, 27, 42],
    #[57, 9, 79, 57, 29, 79],
    #[14, 10, 80, 14, 1, 80],
    #[15, 11, 81, 15, 31, 81],
    #[69, 12, 109, 69, 33, 109],
    #[72, 13, 107, 72, 35, 107],
    #[24, 14, 106, 24, 2, 106],
    #[25, 15, 127, 25, 37, 127],
    #[28, 16, 67, 28, 38, 67],
    #[26, 17, 66, 26, 3, 66],
    #[73, 18, 115, 73, 40, 115],
    #[30, 19, 65, 30, 4, 65],
    #[29, 20, 114, 29, 41, 114],
    #[31, 21, 113, 31, 6, 113],
    #[38, 22, 59, 38, 45, 59],
    #[41, 23, 96, 41, 47, 96],
    #[5, 24, 97, 5, 7, 97],
    #[6, 25, 98, 6, 49, 98],
    #[34, 26, 61, 34, 50, 61],
    #[32, 27, 62, 32, 8, 62],
    #[74, 28, 63, 74, 52, 63],
    #[36, 29, 102, 36, 9, 102],
    #[35, 30, 103, 35, 53, 103],
    #[37, 31, 104, 37, 11, 104],
    #[46, 32, 87, 46, 54, 87],
    #[44, 33, 86, 44, 12, 86],
    #[95, 34, 124, 95, 56, 124],
    #[48, 35, 85, 48, 13, 85],
    #[47, 36, 123, 47, 57, 123],
    #[49, 37, 122, 49, 15, 122],
    #[52, 38, 43, 52, 16, 43],
    #[8, 39, 94, 8, 58, 94],
    #[51, 40, 93, 51, 18, 93],
    #[9, 41, 91, 9, 20, 91],
    #[106, 42, 28, 106, 62, 28],
    #[120, 43, 58, 120, 67, 58],
    #[18, 44, 76, 18, 69, 76],
    #[16, 45, 77, 16, 22, 77],
    #[58, 46, 78, 58, 71, 78],
    #[20, 47, 116, 20, 23, 116],
    #[19, 48, 117, 19, 72, 117],
    #[21, 49, 118, 21, 25, 118],
    #[56, 50, 82, 56, 26, 82],
    #[12, 51, 83, 12, 73, 83],
    #[55, 52, 84, 55, 28, 84],
    #[13, 53, 120, 13, 30, 120],
    #[71, 54, 64, 71, 32, 64],
    #[22, 55, 111, 22, 74, 111],
    #[70, 56, 110, 70, 34, 110],
    #[23, 57, 108, 23, 36, 108],
    #[27, 58, 68, 27, 39, 68],
    #[89, 59, 46, 89, 77, 46],
    #[87, 60, 11, 87, 80, 11],
    #[123, 61, 51, 123, 82, 51],
    #[121, 62, 52, 121, 42, 52],
    #[122, 63, 8, 122, 84, 8],
    #[126, 64, 74, 126, 87, 74],
    #[63, 65, 41, 63, 90, 41],
    #[60, 66, 40, 60, 92, 40],
    #[103, 67, 39, 103, 43, 39],
    #[102, 68, 38, 102, 94, 38],
    #[40, 69, 99, 40, 44, 99],
    #[3, 70, 100, 3, 95, 100],
    #[39, 71, 101, 39, 46, 101],
    #[4, 72, 126, 4, 48, 126],
    #[33, 73, 105, 33, 51, 105],
    #[45, 74, 88, 45, 55, 88],
    #[67, 75, 25, 67, 97, 25],
    #[114, 76, 70, 114, 99, 70],
    #[112, 77, 71, 112, 59, 71],
    #[113, 78, 22, 113, 101, 22],
    #[110, 79, 30, 110, 102, 30],
    #[64, 80, 31, 64, 60, 31],
    #[111, 81, 1, 111, 104, 1],
    #[108, 82, 73, 108, 61, 73],
    #[107, 83, 26, 107, 105, 26],
    #[127, 84, 27, 127, 63, 27],
    #[78, 85, 57, 78, 107, 57],
    #[75, 86, 56, 75, 109, 56],
    #[117, 87, 55, 117, 64, 55],
    #[116, 88, 54, 116, 111, 54],
    #[82, 89, 21, 82, 112, 21],
    #[84, 90, 20, 84, 65, 20],
    #[42, 91, 19, 42, 114, 19],
    #[80, 92, 18, 80, 66, 18],
    #[81, 93, 17, 81, 115, 17],
    #[79, 94, 16, 79, 68, 16],
    #[17, 95, 119, 17, 70, 119],
    #[93, 96, 48, 93, 116, 48],
    #[43, 97, 49, 43, 75, 49],
    #[94, 98, 7, 94, 118, 7],
    #[91, 99, 95, 91, 76, 95],
    #[90, 100, 44, 90, 119, 44],
    #[125, 101, 45, 125, 78, 45],
    #[124, 102, 53, 124, 79, 53],
    #[86, 103, 9, 86, 120, 9],
    #[88, 104, 10, 88, 81, 10],
    #[85, 105, 50, 85, 83, 50],
    #[99, 106, 37, 99, 121, 37],
    #[101, 107, 36, 101, 85, 36],
    #[59, 108, 35, 59, 123, 35],
    #[97, 109, 34, 97, 86, 34],
    #[98, 110, 33, 98, 124, 33],
    #[96, 111, 32, 96, 88, 32],
    #[61, 112, 6, 61, 89, 6],
    #[105, 113, 5, 105, 125, 5],
    #[62, 114, 4, 62, 91, 4],
    #[104, 115, 3, 104, 93, 3],
    #[115, 116, 72, 115, 96, 72],
    #[66, 117, 23, 66, 126, 23],
    #[68, 118, 24, 68, 98, 24],
    #[65, 119, 69, 65, 100, 69],
    #[109, 120, 29, 109, 103, 29],
    #[76, 121, 15, 76, 106, 15],
    #[119, 122, 14, 119, 127, 14],
    #[77, 123, 13, 77, 108, 13],
    #[118, 124, 12, 118, 110, 12],
    #[83, 125, 0, 83, 113, 0],
    #[92, 126, 47, 92, 117, 47],
    #[100, 127, 2, 100, 122, 2]] : Array (Array ℕ)).getD k.val #[]).getD j.val 0)
private def prev52_6 (k : Fin 128) (j : Fin 6) : Fin 128 :=
  Fin.ofNat 128 (((#[#[7, 0, 125, 7, 5, 125],
    #[0, 1, 81, 0, 10, 81],
    #[1, 2, 127, 1, 14, 127],
    #[70, 3, 115, 70, 17, 115],
    #[72, 4, 114, 72, 19, 114],
    #[24, 5, 113, 24, 0, 113],
    #[25, 6, 112, 25, 21, 112],
    #[2, 7, 98, 2, 24, 98],
    #[39, 8, 63, 39, 27, 63],
    #[41, 9, 103, 41, 29, 103],
    #[5, 10, 104, 5, 1, 104],
    #[6, 11, 60, 6, 31, 60],
    #[51, 12, 124, 51, 33, 124],
    #[53, 13, 123, 53, 35, 123],
    #[10, 14, 122, 10, 2, 122],
    #[11, 15, 121, 11, 37, 121],
    #[45, 16, 94, 45, 38, 94],
    #[95, 17, 93, 95, 3, 93],
    #[44, 18, 92, 44, 40, 92],
    #[48, 19, 91, 48, 4, 91],
    #[47, 20, 90, 47, 41, 90],
    #[49, 21, 89, 49, 6, 89],
    #[55, 22, 78, 55, 45, 78],
    #[57, 23, 117, 57, 47, 117],
    #[14, 24, 118, 14, 7, 118],
    #[15, 25, 75, 15, 49, 75],
    #[17, 26, 83, 17, 50, 83],
    #[58, 27, 84, 58, 8, 84],
    #[16, 28, 42, 16, 52, 42],
    #[20, 29, 120, 20, 9, 120],
    #[19, 30, 79, 19, 53, 79],
    #[21, 31, 80, 21, 11, 80],
    #[27, 32, 111, 27, 54, 111],
    #[73, 33, 110, 73, 12, 110],
    #[26, 34, 109, 26, 56, 109],
    #[30, 35, 108, 30, 13, 108],
    #[29, 36, 107, 29, 57, 107],
    #[31, 37, 106, 31, 15, 106],
    #[22, 38, 68, 22, 16, 68],
    #[71, 39, 67, 71, 58, 67],
    #[69, 40, 66, 69, 18, 66],
    #[23, 41, 65, 23, 20, 65],
    #[91, 42, 8, 91, 62, 8],
    #[97, 43, 38, 97, 67, 38],
    #[33, 44, 100, 33, 69, 100],
    #[74, 45, 101, 74, 22, 101],
    #[32, 46, 59, 32, 71, 59],
    #[36, 47, 126, 36, 23, 126],
    #[35, 48, 96, 35, 72, 96],
    #[37, 49, 97, 37, 25, 97],
    #[3, 50, 105, 3, 26, 105],
    #[40, 51, 61, 40, 73, 61],
    #[38, 52, 62, 38, 28, 62],
    #[4, 53, 102, 4, 30, 102],
    #[8, 54, 88, 8, 32, 88],
    #[52, 55, 87, 52, 74, 87],
    #[50, 56, 86, 50, 34, 86],
    #[9, 57, 85, 9, 36, 85],
    #[46, 58, 43, 46, 39, 43],
    #[108, 59, 22, 108, 77, 22],
    #[66, 60, 1, 66, 80, 1],
    #[112, 61, 26, 112, 82, 26],
    #[114, 62, 27, 114, 42, 27],
    #[65, 63, 28, 65, 84, 28],
    #[80, 64, 54, 80, 87, 54],
    #[119, 65, 19, 119, 90, 19],
    #[117, 66, 17, 117, 92, 17],
    #[75, 67, 16, 75, 43, 16],
    #[118, 68, 58, 118, 94, 58],
    #[12, 69, 119, 12, 44, 119],
    #[56, 70, 76, 56, 95, 76],
    #[54, 71, 77, 54, 46, 77],
    #[13, 72, 116, 13, 48, 116],
    #[18, 73, 82, 18, 51, 82],
    #[28, 74, 64, 28, 55, 64],
    #[86, 75, 7, 86, 97, 7],
    #[121, 76, 44, 121, 99, 44],
    #[123, 77, 45, 123, 59, 45],
    #[85, 78, 46, 85, 101, 46],
    #[94, 79, 9, 94, 102, 9],
    #[92, 80, 10, 92, 60, 10],
    #[93, 81, 11, 93, 104, 11],
    #[89, 82, 50, 89, 61, 50],
    #[125, 83, 51, 125, 105, 51],
    #[90, 84, 52, 90, 63, 52],
    #[105, 85, 35, 105, 107, 35],
    #[103, 86, 33, 103, 109, 33],
    #[60, 87, 32, 60, 64, 32],
    #[104, 88, 74, 104, 111, 74],
    #[59, 89, 5, 59, 112, 5],
    #[100, 90, 4, 100, 65, 4],
    #[99, 91, 41, 99, 114, 41],
    #[126, 92, 3, 126, 66, 3],
    #[96, 93, 40, 96, 115, 40],
    #[98, 94, 39, 98, 68, 39],
    #[34, 95, 99, 34, 70, 99],
    #[111, 96, 23, 111, 116, 23],
    #[109, 97, 24, 109, 75, 24],
    #[110, 98, 25, 110, 118, 25],
    #[106, 99, 69, 106, 76, 69],
    #[127, 100, 70, 127, 119, 70],
    #[107, 101, 71, 107, 78, 71],
    #[68, 102, 29, 68, 79, 29],
    #[67, 103, 30, 67, 120, 30],
    #[115, 104, 31, 115, 81, 31],
    #[113, 105, 73, 113, 83, 73],
    #[42, 106, 14, 42, 121, 14],
    #[83, 107, 13, 83, 85, 13],
    #[82, 108, 57, 82, 123, 57],
    #[120, 109, 12, 120, 86, 12],
    #[79, 110, 56, 79, 124, 56],
    #[81, 111, 55, 81, 88, 55],
    #[77, 112, 0, 77, 89, 0],
    #[78, 113, 21, 78, 125, 21],
    #[76, 114, 20, 76, 91, 20],
    #[116, 115, 18, 116, 93, 18],
    #[88, 116, 47, 88, 96, 47],
    #[87, 117, 48, 87, 126, 48],
    #[124, 118, 49, 124, 98, 49],
    #[122, 119, 95, 122, 100, 95],
    #[43, 120, 53, 43, 103, 53],
    #[62, 121, 2, 62, 106, 2],
    #[63, 122, 37, 63, 127, 37],
    #[61, 123, 36, 61, 108, 36],
    #[102, 124, 34, 102, 110, 34],
    #[101, 125, 6, 101, 113, 6],
    #[64, 126, 72, 64, 117, 72],
    #[84, 127, 15, 84, 122, 15]] : Array (Array ℕ)).getD k.val #[]).getD j.val 0)
set_option maxHeartbeats 1600000 in
private theorem cert52_6 : ∃ c, c ∈ Subgroup.centralizer (Subgroup.closure (Set.range e52_6) : Set SylowModel) ∧ c ∉ Subgroup.closure (Set.range e52_6) := by
  refine ⟨root 2 * root 8, centralizes_generators e52_6 _ (by decide +kernel), ?_⟩
  exact outside_of_table e52_6 a52_6 0 next52_6 prev52_6
    (by decide +kernel) (by decide +kernel) (by decide +kernel) _ (by decide +kernel)

private def e52_7 : Fin 6 → SylowModel := ![decode 0, decode 3348, decode 3888, decode 2048, decode 1300, decode 1136]
set_option maxHeartbeats 1600000 in
private theorem edgeEq52_7 : binaryFamily s52 (s52 0) (![true, true, true]) = e52_7 := by decide +kernel
private def a52_7 (k : Fin 128) : SylowModel :=
  decode ((#[0, 2048, 64, 384, 768, 512, 2368, 2432, 2816, 2560, 448, 832, 576, 640, 896, 256, 2240, 2624, 2880, 2688, 2944, 2304, 704, 960, 320, 128, 228, 1968, 3008, 2752, 2112, 2176, 192, 1172, 2660, 164, 356, 996, 740, 3120, 1136, 1840, 1200, 1456, 2496, 3220, 1876, 1044, 1940, 1684, 2852, 3044, 2404, 2148, 292, 932, 676, 612, 868, 484, 3824, 3248, 3888, 3632, 1264, 1904, 1648, 1072, 1328, 1712, 3668, 3092, 3988, 3732, 2004, 1108, 1364, 1812, 1556, 1428, 2724, 2084, 2340, 2276, 2532, 2916, 548, 804, 420, 100, 3696, 3568, 3312, 4016, 3760, 3376, 2032, 1776, 1392, 1584, 3796, 3412, 3156, 3860, 3604, 3476, 1236, 1492, 1620, 1300, 2468, 2212, 2596, 2788, 36, 3440, 3184, 4080, 3504, 1520, 3540, 3284, 3924, 3348, 1748, 2980, 3952, 4052] : Array ℕ).getD k.val 0)
private def next52_7 (k : Fin 128) (j : Fin 6) : Fin 128 :=
  Fin.ofNat 128 (((#[#[0, 123, 62, 1, 109, 40],
    #[1, 109, 42, 0, 123, 60],
    #[2, 101, 126, 30, 76, 67],
    #[3, 45, 94, 7, 33, 119],
    #[4, 104, 39, 8, 78, 65],
    #[5, 103, 95, 9, 77, 66],
    #[6, 75, 119, 24, 102, 93],
    #[7, 33, 68, 3, 45, 126],
    #[8, 78, 27, 4, 104, 91],
    #[9, 77, 69, 5, 103, 92],
    #[10, 121, 60, 44, 106, 43],
    #[11, 70, 116, 18, 108, 41],
    #[12, 122, 115, 17, 46, 99],
    #[13, 72, 118, 19, 48, 97],
    #[14, 73, 61, 20, 49, 96],
    #[15, 71, 63, 21, 47, 98],
    #[16, 107, 40, 32, 120, 63],
    #[17, 46, 97, 12, 122, 61],
    #[18, 108, 96, 11, 70, 118],
    #[19, 48, 99, 13, 72, 116],
    #[20, 49, 41, 14, 73, 115],
    #[21, 47, 43, 15, 71, 117],
    #[22, 127, 91, 29, 74, 69],
    #[23, 100, 92, 28, 124, 27],
    #[24, 102, 90, 6, 75, 68],
    #[25, 105, 93, 31, 79, 64],
    #[26, 91, 120, 83, 119, 49],
    #[27, 88, 10, 93, 110, 21],
    #[28, 124, 65, 23, 100, 95],
    #[29, 74, 66, 22, 127, 39],
    #[30, 76, 64, 2, 101, 94],
    #[31, 79, 67, 25, 105, 90],
    #[32, 120, 117, 16, 107, 42],
    #[33, 13, 26, 45, 19, 81],
    #[34, 65, 106, 57, 126, 73],
    #[35, 118, 105, 111, 43, 124],
    #[36, 116, 102, 52, 40, 77],
    #[37, 60, 100, 51, 97, 79],
    #[38, 117, 127, 113, 96, 33],
    #[39, 112, 16, 67, 86, 15],
    #[40, 57, 5, 116, 34, 29],
    #[41, 54, 24, 62, 82, 7],
    #[42, 56, 22, 61, 80, 9],
    #[43, 55, 23, 118, 125, 8],
    #[44, 106, 98, 10, 121, 62],
    #[45, 19, 34, 33, 13, 55],
    #[46, 24, 87, 122, 6, 51],
    #[47, 5, 89, 71, 9, 111],
    #[48, 3, 37, 72, 7, 50],
    #[49, 25, 38, 73, 31, 112],
    #[50, 99, 79, 87, 63, 127],
    #[51, 97, 76, 37, 60, 103],
    #[52, 40, 74, 36, 116, 105],
    #[53, 98, 124, 89, 115, 45],
    #[54, 39, 71, 82, 67, 46],
    #[55, 94, 73, 125, 69, 107],
    #[56, 93, 72, 80, 27, 106],
    #[57, 126, 122, 34, 65, 47],
    #[58, 90, 70, 85, 66, 109],
    #[59, 92, 121, 84, 64, 48],
    #[60, 83, 9, 97, 26, 23],
    #[61, 80, 30, 42, 56, 3],
    #[62, 82, 28, 41, 54, 5],
    #[63, 81, 29, 99, 114, 4],
    #[64, 38, 13, 92, 113, 17],
    #[65, 36, 15, 126, 52, 44],
    #[66, 89, 0, 90, 53, 16],
    #[67, 86, 12, 39, 112, 19],
    #[68, 87, 11, 95, 50, 20],
    #[69, 35, 32, 94, 111, 1],
    #[70, 30, 111, 108, 2, 36],
    #[71, 9, 113, 47, 5, 87],
    #[72, 7, 52, 48, 3, 35],
    #[73, 31, 53, 49, 25, 88],
    #[74, 10, 55, 127, 44, 85],
    #[75, 12, 114, 102, 17, 83],
    #[76, 11, 54, 101, 18, 84],
    #[77, 15, 58, 103, 21, 125],
    #[78, 0, 57, 104, 1, 80],
    #[79, 14, 59, 105, 20, 82],
    #[80, 27, 47, 56, 93, 70],
    #[81, 68, 49, 114, 95, 121],
    #[82, 67, 48, 54, 39, 120],
    #[83, 119, 108, 26, 91, 71],
    #[84, 64, 46, 59, 92, 123],
    #[85, 66, 107, 58, 90, 72],
    #[86, 62, 103, 112, 41, 75],
    #[87, 63, 104, 50, 99, 76],
    #[88, 61, 45, 110, 42, 74],
    #[89, 115, 101, 53, 98, 78],
    #[90, 53, 19, 66, 89, 11],
    #[91, 51, 21, 119, 37, 32],
    #[92, 113, 1, 64, 38, 10],
    #[93, 110, 18, 27, 88, 13],
    #[94, 111, 17, 69, 35, 14],
    #[95, 50, 44, 68, 87, 0],
    #[96, 59, 3, 117, 84, 6],
    #[97, 26, 25, 60, 83, 30],
    #[98, 58, 4, 115, 85, 28],
    #[99, 114, 2, 63, 81, 31],
    #[100, 16, 81, 124, 32, 59],
    #[101, 18, 125, 76, 11, 57],
    #[102, 17, 80, 75, 12, 58],
    #[103, 21, 84, 77, 15, 114],
    #[104, 1, 83, 78, 0, 54],
    #[105, 20, 85, 79, 14, 56],
    #[106, 22, 35, 121, 29, 53],
    #[107, 23, 88, 120, 28, 52],
    #[108, 2, 86, 70, 30, 113],
    #[109, 4, 36, 123, 8, 110],
    #[110, 42, 77, 88, 61, 101],
    #[111, 43, 78, 35, 118, 102],
    #[112, 41, 33, 86, 62, 100],
    #[113, 96, 75, 38, 117, 104],
    #[114, 95, 123, 81, 68, 108],
    #[115, 85, 7, 98, 58, 2],
    #[116, 34, 31, 40, 57, 24],
    #[117, 84, 8, 96, 59, 22],
    #[118, 125, 6, 43, 55, 25],
    #[119, 37, 14, 91, 51, 18],
    #[120, 28, 50, 107, 23, 38],
    #[121, 29, 112, 106, 22, 37],
    #[122, 6, 110, 46, 24, 89],
    #[123, 8, 51, 109, 4, 86],
    #[124, 32, 56, 100, 16, 34],
    #[125, 69, 109, 55, 94, 122],
    #[126, 52, 20, 65, 36, 12],
    #[127, 44, 82, 74, 10, 26]] : Array (Array ℕ)).getD k.val #[]).getD j.val 0)
private def prev52_7 (k : Fin 128) (j : Fin 6) : Fin 128 :=
  Fin.ofNat 128 (((#[#[0, 78, 66, 1, 104, 95],
    #[1, 104, 92, 0, 78, 69],
    #[2, 108, 99, 30, 70, 115],
    #[3, 48, 96, 7, 72, 61],
    #[4, 109, 98, 8, 123, 63],
    #[5, 47, 40, 9, 71, 62],
    #[6, 122, 118, 24, 46, 96],
    #[7, 72, 115, 3, 48, 41],
    #[8, 123, 117, 4, 109, 43],
    #[9, 71, 60, 5, 47, 42],
    #[10, 74, 27, 44, 127, 92],
    #[11, 76, 68, 18, 101, 90],
    #[12, 75, 67, 17, 102, 126],
    #[13, 33, 64, 19, 45, 93],
    #[14, 79, 119, 20, 105, 94],
    #[15, 77, 65, 21, 103, 39],
    #[16, 100, 39, 32, 124, 66],
    #[17, 102, 94, 12, 75, 64],
    #[18, 101, 93, 11, 76, 119],
    #[19, 45, 90, 13, 33, 67],
    #[20, 105, 126, 14, 79, 68],
    #[21, 103, 91, 15, 77, 27],
    #[22, 106, 42, 29, 121, 117],
    #[23, 107, 43, 28, 120, 60],
    #[24, 46, 41, 6, 122, 116],
    #[25, 49, 97, 31, 73, 118],
    #[26, 97, 33, 83, 60, 127],
    #[27, 80, 8, 93, 56, 23],
    #[28, 120, 62, 23, 107, 98],
    #[29, 121, 63, 22, 106, 40],
    #[30, 70, 61, 2, 108, 97],
    #[31, 73, 116, 25, 49, 99],
    #[32, 124, 69, 16, 100, 91],
    #[33, 7, 112, 45, 3, 38],
    #[34, 116, 45, 57, 40, 124],
    #[35, 69, 106, 111, 94, 72],
    #[36, 65, 109, 52, 126, 70],
    #[37, 119, 48, 51, 91, 121],
    #[38, 64, 49, 113, 92, 120],
    #[39, 54, 4, 67, 82, 29],
    #[40, 52, 16, 116, 36, 0],
    #[41, 112, 20, 62, 86, 11],
    #[42, 110, 1, 61, 88, 32],
    #[43, 111, 21, 118, 35, 10],
    #[44, 127, 95, 10, 74, 65],
    #[45, 3, 88, 33, 7, 53],
    #[46, 17, 84, 122, 12, 54],
    #[47, 21, 80, 71, 15, 57],
    #[48, 19, 82, 72, 13, 59],
    #[49, 20, 81, 73, 14, 26],
    #[50, 95, 120, 87, 68, 48],
    #[51, 91, 123, 37, 119, 46],
    #[52, 126, 72, 36, 65, 107],
    #[53, 90, 73, 89, 66, 106],
    #[54, 41, 76, 82, 62, 104],
    #[55, 43, 74, 125, 118, 45],
    #[56, 42, 124, 80, 61, 105],
    #[57, 40, 78, 34, 116, 101],
    #[58, 98, 77, 85, 115, 102],
    #[59, 96, 79, 84, 117, 100],
    #[60, 37, 10, 97, 51, 1],
    #[61, 88, 14, 42, 110, 17],
    #[62, 86, 0, 41, 112, 44],
    #[63, 87, 15, 99, 50, 16],
    #[64, 84, 30, 92, 59, 25],
    #[65, 34, 28, 126, 57, 4],
    #[66, 85, 29, 90, 58, 5],
    #[67, 82, 31, 39, 54, 2],
    #[68, 81, 7, 95, 114, 24],
    #[69, 125, 9, 94, 55, 22],
    #[70, 11, 58, 108, 18, 80],
    #[71, 15, 54, 47, 21, 83],
    #[72, 13, 56, 48, 19, 85],
    #[73, 14, 55, 49, 20, 34],
    #[74, 29, 52, 127, 22, 88],
    #[75, 6, 113, 102, 24, 86],
    #[76, 30, 51, 101, 2, 87],
    #[77, 9, 110, 103, 5, 36],
    #[78, 8, 111, 104, 4, 89],
    #[79, 31, 50, 105, 25, 37],
    #[80, 61, 102, 56, 42, 78],
    #[81, 63, 100, 114, 99, 33],
    #[82, 62, 127, 54, 41, 79],
    #[83, 60, 104, 26, 97, 75],
    #[84, 117, 103, 59, 96, 76],
    #[85, 115, 105, 58, 98, 74],
    #[86, 67, 108, 112, 39, 123],
    #[87, 68, 46, 50, 95, 71],
    #[88, 27, 107, 110, 93, 73],
    #[89, 66, 47, 53, 90, 122],
    #[90, 58, 24, 66, 85, 31],
    #[91, 26, 22, 119, 83, 8],
    #[92, 59, 23, 64, 84, 9],
    #[93, 56, 25, 27, 80, 6],
    #[94, 55, 3, 69, 125, 30],
    #[95, 114, 5, 68, 81, 28],
    #[96, 113, 18, 117, 38, 14],
    #[97, 51, 17, 60, 37, 13],
    #[98, 53, 44, 115, 89, 15],
    #[99, 50, 19, 63, 87, 12],
    #[100, 23, 37, 124, 28, 112],
    #[101, 2, 89, 76, 30, 110],
    #[102, 24, 36, 75, 6, 111],
    #[103, 5, 86, 77, 9, 51],
    #[104, 4, 87, 78, 8, 113],
    #[105, 25, 35, 79, 31, 52],
    #[106, 44, 34, 121, 10, 56],
    #[107, 16, 85, 120, 32, 55],
    #[108, 18, 83, 70, 11, 114],
    #[109, 1, 125, 123, 0, 58],
    #[110, 93, 122, 88, 27, 109],
    #[111, 94, 70, 35, 69, 47],
    #[112, 39, 121, 86, 67, 49],
    #[113, 92, 71, 38, 64, 108],
    #[114, 99, 75, 81, 63, 103],
    #[115, 89, 12, 98, 53, 20],
    #[116, 36, 11, 40, 52, 19],
    #[117, 38, 32, 96, 113, 21],
    #[118, 35, 13, 43, 111, 18],
    #[119, 83, 6, 91, 26, 3],
    #[120, 32, 26, 107, 16, 82],
    #[121, 10, 59, 106, 44, 81],
    #[122, 12, 57, 46, 17, 125],
    #[123, 0, 114, 109, 1, 84],
    #[124, 28, 53, 100, 23, 35],
    #[125, 118, 101, 55, 43, 77],
    #[126, 57, 2, 65, 34, 7],
    #[127, 22, 38, 74, 29, 50]] : Array (Array ℕ)).getD k.val #[]).getD j.val 0)
set_option maxHeartbeats 1600000 in
private theorem cert52_7 : ∃ c, c ∈ Subgroup.centralizer (Subgroup.closure (Set.range e52_7) : Set SylowModel) ∧ c ∉ Subgroup.closure (Set.range e52_7) := by
  refine ⟨root 2 * root 7, centralizes_generators e52_7 _ (by decide +kernel), ?_⟩
  exact outside_of_table e52_7 a52_7 0 next52_7 prev52_7
    (by decide +kernel) (by decide +kernel) (by decide +kernel) _ (by decide +kernel)

private def s53 : Fin 3 → SylowModel := ![rootOne ^ 3, root 5 * root 8, root 2 * root 8]
set_option maxHeartbeats 1600000 in
private theorem gen53 : Subgroup.closure (Set.range s53) = smallParityCensusNode 53 := by
  rw [node53]
  exact closure_eq_words s53 o53 (![[1], [2], [0]]) (![[2], [0], [1], [0, 0], [0, 0, 0, 1, 0, 1], [0, 1, 0, 1, 0, 1, 0, 1, 2, 2], [0, 0, 1, 0, 0, 1], [0, 1, 0, 1, 0, 1, 0, 1]]) (by decide +kernel) (by decide +kernel)

private def e53_1 : Fin 6 → SylowModel := ![decode 0, decode 288, decode 260, decode 2048, decode 608, decode 260]
set_option maxHeartbeats 1600000 in
private theorem edgeEq53_1 : binaryFamily s53 (s53 0) (![true, false, false]) = e53_1 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert53_1 : Subgroup.closure (Set.range e53_1) ≤ character.ker := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨j, rfl⟩
  exact (show ∀ j, e53_1 j ∈ character.ker from by decide +kernel) j

private def e53_2 : Fin 6 → SylowModel := ![decode 1024, decode 0, decode 260, decode 1856, decode 0, decode 260]
set_option maxHeartbeats 1600000 in
private theorem edgeEq53_2 : binaryFamily s53 (s53 1) (![false, true, false]) = e53_2 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert53_2 : Represented smallParityCensusNode (Subgroup.closure (Set.range e53_2)) := by
  refine ⟨85, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node85]
  exact closure_eq_words _ o85 (![[1], [], [0], [1, 2], [], [0]]) (![[2], [0], [0, 0, 0, 3], [0, 0], [0, 0, 3, 3], [0, 2, 2, 3, 0, 3], [0, 3, 0, 3]]) (by decide +kernel) (by decide +kernel)

private def e53_3 : Fin 6 → SylowModel := ![decode 0, decode 3360, decode 260, decode 2048, decode 1632, decode 260]
set_option maxHeartbeats 1600000 in
private theorem edgeEq53_3 : binaryFamily s53 (s53 0) (![true, true, false]) = e53_3 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert53_3 : Represented smallParityCensusNode (Subgroup.closure (Set.range e53_3)) := by
  refine ⟨93, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node93]
  exact closure_eq_words _ o93 (![[], [1, 3, 6], [0, 0, 0], [3, 2], [1], [0, 0, 0]]) (![[2, 2, 2], [4], [1, 1, 3], [4, 4], [1, 3, 4, 3], [1, 1, 1, 1, 2, 2], [1, 1, 1, 1]]) (by decide +kernel) (by decide +kernel)

private def e53_4 : Fin 6 → SylowModel := ![decode 1024, decode 288, decode 0, decode 1024, decode 288, decode 512]
set_option maxHeartbeats 1600000 in
private theorem edgeEq53_4 : binaryFamily s53 (s53 2) (![false, false, true]) = e53_4 := by decide +kernel
private def a53_4 (k : Fin 128) : SylowModel :=
  decode ((#[0, 1024, 2048, 64, 384, 768, 512, 3072, 1984, 1152, 1792, 1536, 2368, 2432, 2816, 2560, 224, 448, 832, 576, 640, 896, 256, 3776, 3200, 3840, 3584, 1312, 1856, 1216, 1472, 1920, 1664, 1280, 2656, 2240, 2624, 2880, 2688, 2944, 2304, 160, 352, 992, 736, 704, 960, 320, 128, 3744, 3648, 3520, 3264, 3968, 3712, 3328, 1760, 1440, 1568, 1824, 1088, 1344, 1728, 1408, 2848, 3040, 2400, 2144, 3008, 2752, 2112, 2176, 288, 928, 672, 608, 864, 480, 192, 3168, 3616, 3488, 3232, 3392, 3136, 4032, 3456, 1632, 1504, 1248, 1696, 1952, 1056, 1600, 2720, 2080, 2336, 2272, 2528, 2912, 2496, 544, 800, 416, 96, 3296, 3936, 3680, 3360, 3104, 4000, 3904, 1376, 1120, 2016, 1184, 2464, 2208, 2592, 2784, 32, 4064, 3808, 3424, 3872, 1888, 2976, 3552] : Array ℕ).getD k.val 0)
private def next53_4 (k : Fin 128) (j : Fin 6) : Fin 128 :=
  Fin.ofNat 128 (((#[#[1, 72, 0, 1, 72, 6],
    #[2, 87, 1, 2, 87, 11],
    #[7, 94, 2, 7, 94, 15],
    #[60, 42, 3, 60, 42, 19],
    #[63, 41, 4, 63, 41, 21],
    #[10, 101, 5, 10, 101, 22],
    #[11, 102, 6, 11, 102, 0],
    #[0, 105, 7, 0, 105, 26],
    #[68, 57, 8, 68, 57, 30],
    #[71, 56, 9, 71, 56, 32],
    #[14, 112, 10, 14, 112, 33],
    #[15, 113, 11, 15, 113, 1],
    #[83, 65, 12, 83, 65, 37],
    #[86, 64, 13, 86, 64, 39],
    #[25, 116, 14, 25, 116, 40],
    #[26, 117, 15, 26, 117, 2],
    #[89, 17, 16, 89, 17, 44],
    #[30, 16, 17, 30, 16, 46],
    #[28, 75, 18, 28, 75, 47],
    #[93, 76, 19, 93, 76, 3],
    #[32, 73, 20, 32, 73, 48],
    #[31, 74, 21, 31, 74, 4],
    #[33, 120, 22, 33, 120, 5],
    #[45, 80, 23, 45, 80, 52],
    #[48, 79, 24, 48, 79, 54],
    #[5, 121, 25, 5, 121, 55],
    #[6, 122, 26, 6, 122, 7],
    #[96, 28, 27, 96, 28, 59],
    #[37, 27, 28, 37, 27, 61],
    #[35, 90, 29, 35, 90, 62],
    #[100, 91, 30, 100, 91, 8],
    #[39, 88, 31, 39, 88, 63],
    #[38, 89, 32, 38, 89, 9],
    #[40, 125, 33, 40, 125, 10],
    #[107, 35, 34, 107, 35, 67],
    #[52, 34, 35, 52, 34, 69],
    #[50, 97, 36, 50, 97, 70],
    #[111, 98, 37, 111, 98, 12],
    #[54, 95, 38, 54, 95, 71],
    #[53, 96, 39, 53, 96, 13],
    #[55, 126, 40, 55, 126, 14],
    #[115, 4, 41, 115, 4, 74],
    #[112, 3, 42, 112, 3, 76],
    #[114, 45, 43, 114, 45, 77],
    #[56, 46, 44, 56, 46, 16],
    #[62, 43, 45, 62, 43, 78],
    #[8, 44, 46, 8, 44, 17],
    #[61, 104, 47, 61, 104, 18],
    #[9, 103, 48, 9, 103, 20],
    #[74, 50, 49, 74, 50, 82],
    #[19, 49, 50, 19, 49, 84],
    #[17, 108, 51, 17, 108, 85],
    #[78, 109, 52, 78, 109, 23],
    #[21, 106, 53, 21, 106, 86],
    #[20, 107, 54, 20, 107, 24],
    #[22, 127, 55, 22, 127, 25],
    #[119, 9, 56, 119, 9, 89],
    #[116, 8, 57, 116, 8, 91],
    #[118, 60, 58, 118, 60, 92],
    #[64, 61, 59, 64, 61, 27],
    #[70, 58, 60, 70, 58, 93],
    #[12, 59, 61, 12, 59, 28],
    #[69, 115, 62, 69, 115, 29],
    #[13, 114, 63, 13, 114, 31],
    #[124, 13, 64, 124, 13, 96],
    #[121, 12, 65, 121, 12, 98],
    #[123, 68, 66, 123, 68, 99],
    #[79, 69, 67, 79, 69, 34],
    #[85, 66, 68, 85, 66, 100],
    #[23, 67, 69, 23, 67, 35],
    #[84, 119, 70, 84, 119, 36],
    #[24, 118, 71, 24, 118, 38],
    #[27, 0, 72, 27, 0, 102],
    #[91, 20, 73, 91, 20, 103],
    #[90, 21, 74, 90, 21, 41],
    #[87, 18, 75, 87, 18, 104],
    #[125, 19, 76, 125, 19, 42],
    #[88, 78, 77, 88, 78, 43],
    #[29, 77, 78, 29, 77, 45],
    #[104, 24, 79, 104, 24, 107],
    #[101, 23, 80, 101, 23, 109],
    #[103, 83, 81, 103, 83, 110],
    #[41, 84, 82, 41, 84, 49],
    #[47, 81, 83, 47, 81, 111],
    #[3, 82, 84, 3, 82, 50],
    #[46, 124, 85, 46, 124, 51],
    #[4, 123, 86, 4, 123, 53],
    #[34, 1, 87, 34, 1, 113],
    #[98, 31, 88, 98, 31, 114],
    #[97, 32, 89, 97, 32, 56],
    #[94, 29, 90, 94, 29, 115],
    #[126, 30, 91, 126, 30, 57],
    #[95, 93, 92, 95, 93, 58],
    #[36, 92, 93, 36, 92, 60],
    #[49, 2, 94, 49, 2, 117],
    #[109, 38, 95, 109, 38, 118],
    #[108, 39, 96, 108, 39, 64],
    #[105, 36, 97, 105, 36, 119],
    #[127, 37, 98, 127, 37, 65],
    #[106, 100, 99, 106, 100, 66],
    #[51, 99, 100, 51, 99, 68],
    #[58, 5, 101, 58, 5, 120],
    #[59, 6, 102, 59, 6, 72],
    #[57, 48, 103, 57, 48, 73],
    #[113, 47, 104, 113, 47, 75],
    #[16, 7, 105, 16, 7, 122],
    #[76, 53, 106, 76, 53, 123],
    #[75, 54, 107, 75, 54, 79],
    #[72, 51, 108, 72, 51, 124],
    #[120, 52, 109, 120, 52, 80],
    #[73, 111, 110, 73, 111, 81],
    #[18, 110, 111, 18, 110, 83],
    #[66, 10, 112, 66, 10, 125],
    #[67, 11, 113, 67, 11, 87],
    #[65, 63, 114, 65, 63, 88],
    #[117, 62, 115, 117, 62, 90],
    #[81, 14, 116, 81, 14, 126],
    #[82, 15, 117, 82, 15, 94],
    #[80, 71, 118, 80, 71, 95],
    #[122, 70, 119, 122, 70, 97],
    #[92, 22, 120, 92, 22, 101],
    #[43, 25, 121, 43, 25, 127],
    #[44, 26, 122, 44, 26, 105],
    #[42, 86, 123, 42, 86, 106],
    #[102, 85, 124, 102, 85, 108],
    #[99, 33, 125, 99, 33, 112],
    #[110, 40, 126, 110, 40, 116],
    #[77, 55, 127, 77, 55, 121]] : Array (Array ℕ)).getD k.val #[]).getD j.val 0)
private def prev53_4 (k : Fin 128) (j : Fin 6) : Fin 128 :=
  Fin.ofNat 128 (((#[#[7, 72, 0, 7, 72, 6],
    #[0, 87, 1, 0, 87, 11],
    #[1, 94, 2, 1, 94, 15],
    #[84, 42, 3, 84, 42, 19],
    #[86, 41, 4, 86, 41, 21],
    #[25, 101, 5, 25, 101, 22],
    #[26, 102, 6, 26, 102, 0],
    #[2, 105, 7, 2, 105, 26],
    #[46, 57, 8, 46, 57, 30],
    #[48, 56, 9, 48, 56, 32],
    #[5, 112, 10, 5, 112, 33],
    #[6, 113, 11, 6, 113, 1],
    #[61, 65, 12, 61, 65, 37],
    #[63, 64, 13, 63, 64, 39],
    #[10, 116, 14, 10, 116, 40],
    #[11, 117, 15, 11, 117, 2],
    #[105, 17, 16, 105, 17, 44],
    #[51, 16, 17, 51, 16, 46],
    #[111, 75, 18, 111, 75, 47],
    #[50, 76, 19, 50, 76, 3],
    #[54, 73, 20, 54, 73, 48],
    #[53, 74, 21, 53, 74, 4],
    #[55, 120, 22, 55, 120, 5],
    #[69, 80, 23, 69, 80, 52],
    #[71, 79, 24, 71, 79, 54],
    #[14, 121, 25, 14, 121, 55],
    #[15, 122, 26, 15, 122, 7],
    #[72, 28, 27, 72, 28, 59],
    #[18, 27, 28, 18, 27, 61],
    #[78, 90, 29, 78, 90, 62],
    #[17, 91, 30, 17, 91, 8],
    #[21, 88, 31, 21, 88, 63],
    #[20, 89, 32, 20, 89, 9],
    #[22, 125, 33, 22, 125, 10],
    #[87, 35, 34, 87, 35, 67],
    #[29, 34, 35, 29, 34, 69],
    #[93, 97, 36, 93, 97, 70],
    #[28, 98, 37, 28, 98, 12],
    #[32, 95, 38, 32, 95, 71],
    #[31, 96, 39, 31, 96, 13],
    #[33, 126, 40, 33, 126, 14],
    #[82, 4, 41, 82, 4, 74],
    #[123, 3, 42, 123, 3, 76],
    #[121, 45, 43, 121, 45, 77],
    #[122, 46, 44, 122, 46, 16],
    #[23, 43, 45, 23, 43, 78],
    #[85, 44, 46, 85, 44, 17],
    #[83, 104, 47, 83, 104, 18],
    #[24, 103, 48, 24, 103, 20],
    #[94, 50, 49, 94, 50, 82],
    #[36, 49, 50, 36, 49, 84],
    #[100, 108, 51, 100, 108, 85],
    #[35, 109, 52, 35, 109, 23],
    #[39, 106, 53, 39, 106, 86],
    #[38, 107, 54, 38, 107, 24],
    #[40, 127, 55, 40, 127, 25],
    #[44, 9, 56, 44, 9, 89],
    #[103, 8, 57, 103, 8, 91],
    #[101, 60, 58, 101, 60, 92],
    #[102, 61, 59, 102, 61, 27],
    #[3, 58, 60, 3, 58, 93],
    #[47, 59, 61, 47, 59, 28],
    #[45, 115, 62, 45, 115, 29],
    #[4, 114, 63, 4, 114, 31],
    #[59, 13, 64, 59, 13, 96],
    #[114, 12, 65, 114, 12, 98],
    #[112, 68, 66, 112, 68, 99],
    #[113, 69, 67, 113, 69, 34],
    #[8, 66, 68, 8, 66, 100],
    #[62, 67, 69, 62, 67, 35],
    #[60, 119, 70, 60, 119, 36],
    #[9, 118, 71, 9, 118, 38],
    #[108, 0, 72, 108, 0, 102],
    #[110, 20, 73, 110, 20, 103],
    #[49, 21, 74, 49, 21, 41],
    #[107, 18, 75, 107, 18, 104],
    #[106, 19, 76, 106, 19, 42],
    #[127, 78, 77, 127, 78, 43],
    #[52, 77, 78, 52, 77, 45],
    #[67, 24, 79, 67, 24, 107],
    #[118, 23, 80, 118, 23, 109],
    #[116, 83, 81, 116, 83, 110],
    #[117, 84, 82, 117, 84, 49],
    #[12, 81, 83, 12, 81, 111],
    #[70, 82, 84, 70, 82, 50],
    #[68, 124, 85, 68, 124, 51],
    #[13, 123, 86, 13, 123, 53],
    #[75, 1, 87, 75, 1, 113],
    #[77, 31, 88, 77, 31, 114],
    #[16, 32, 89, 16, 32, 56],
    #[74, 29, 90, 74, 29, 115],
    #[73, 30, 91, 73, 30, 57],
    #[120, 93, 92, 120, 93, 58],
    #[19, 92, 93, 19, 92, 60],
    #[90, 2, 94, 90, 2, 117],
    #[92, 38, 95, 92, 38, 118],
    #[27, 39, 96, 27, 39, 64],
    #[89, 36, 97, 89, 36, 119],
    #[88, 37, 98, 88, 37, 65],
    #[125, 100, 99, 125, 100, 66],
    #[30, 99, 100, 30, 99, 68],
    #[80, 5, 101, 80, 5, 120],
    #[124, 6, 102, 124, 6, 72],
    #[81, 48, 103, 81, 48, 73],
    #[79, 47, 104, 79, 47, 75],
    #[97, 7, 105, 97, 7, 122],
    #[99, 53, 106, 99, 53, 123],
    #[34, 54, 107, 34, 54, 79],
    #[96, 51, 108, 96, 51, 124],
    #[95, 52, 109, 95, 52, 80],
    #[126, 111, 110, 126, 111, 81],
    #[37, 110, 111, 37, 110, 83],
    #[42, 10, 112, 42, 10, 125],
    #[104, 11, 113, 104, 11, 87],
    #[43, 63, 114, 43, 63, 88],
    #[41, 62, 115, 41, 62, 90],
    #[57, 14, 116, 57, 14, 126],
    #[115, 15, 117, 115, 15, 94],
    #[58, 71, 118, 58, 71, 95],
    #[56, 70, 119, 56, 70, 97],
    #[109, 22, 120, 109, 22, 101],
    #[65, 25, 121, 65, 25, 127],
    #[119, 26, 122, 119, 26, 105],
    #[66, 86, 123, 66, 86, 106],
    #[64, 85, 124, 64, 85, 108],
    #[76, 33, 125, 76, 33, 112],
    #[91, 40, 126, 91, 40, 116],
    #[98, 55, 127, 98, 55, 121]] : Array (Array ℕ)).getD k.val #[]).getD j.val 0)
set_option maxHeartbeats 1600000 in
private theorem cert53_4 : ∃ c, c ∈ Subgroup.centralizer (Subgroup.closure (Set.range e53_4) : Set SylowModel) ∧ c ∉ Subgroup.closure (Set.range e53_4) := by
  refine ⟨root 2 * root 8, centralizes_generators e53_4 _ (by decide +kernel), ?_⟩
  exact outside_of_table e53_4 a53_4 0 next53_4 prev53_4
    (by decide +kernel) (by decide +kernel) (by decide +kernel) _ (by decide +kernel)

private def e53_5 : Fin 6 → SylowModel := ![decode 0, decode 288, decode 3332, decode 2048, decode 608, decode 1284]
set_option maxHeartbeats 1600000 in
private theorem edgeEq53_5 : binaryFamily s53 (s53 0) (![true, false, true]) = e53_5 := by decide +kernel
private def a53_5 (k : Fin 128) : SylowModel :=
  decode ((#[0, 2048, 64, 384, 768, 512, 2368, 2432, 2816, 2560, 224, 448, 832, 576, 640, 896, 256, 2656, 2240, 2624, 2880, 2688, 2944, 2304, 160, 352, 992, 736, 704, 960, 320, 128, 1700, 1028, 2848, 3040, 2400, 2144, 3008, 2752, 2112, 2176, 288, 928, 672, 608, 864, 480, 192, 3364, 3076, 1380, 1572, 1444, 1188, 1988, 1156, 1796, 1540, 2720, 2080, 2336, 2272, 2528, 2912, 2496, 544, 800, 416, 96, 4068, 3492, 3620, 3876, 3780, 3204, 3844, 3588, 1508, 1636, 1892, 1316, 1060, 1956, 1860, 1220, 1476, 1924, 1668, 1284, 2464, 2208, 2592, 2784, 32, 3940, 3300, 3556, 3748, 4004, 3108, 3652, 3524, 3268, 3972, 3716, 3332, 1764, 2020, 1124, 1828, 1092, 1348, 1732, 1412, 2976, 3172, 3428, 3812, 3236, 3396, 3140, 4036, 3460, 1252, 1604, 3684, 3908] : Array ℕ).getD k.val 0)
private def next53_5 (k : Fin 128) (j : Fin 6) : Fin 128 :=
  Fin.ofNat 128 (((#[#[0, 42, 106, 1, 45, 89],
    #[1, 59, 89, 0, 62, 106],
    #[2, 25, 120, 40, 66, 112],
    #[3, 24, 75, 7, 26, 56],
    #[4, 66, 77, 8, 25, 58],
    #[5, 67, 76, 9, 69, 57],
    #[6, 35, 111, 30, 90, 121],
    #[7, 34, 56, 3, 36, 75],
    #[8, 90, 58, 4, 35, 77],
    #[9, 91, 57, 5, 93, 76],
    #[10, 11, 97, 62, 14, 78],
    #[11, 10, 103, 65, 43, 85],
    #[12, 45, 101, 20, 42, 125],
    #[13, 46, 127, 19, 94, 84],
    #[14, 43, 104, 21, 10, 87],
    #[15, 44, 105, 22, 47, 88],
    #[16, 94, 50, 23, 46, 33],
    #[17, 18, 80, 45, 21, 95],
    #[18, 17, 86, 48, 60, 102],
    #[19, 62, 84, 13, 59, 127],
    #[20, 63, 125, 12, 115, 101],
    #[21, 60, 87, 14, 17, 104],
    #[22, 61, 88, 15, 64, 105],
    #[23, 115, 33, 16, 63, 50],
    #[24, 3, 71, 91, 28, 53],
    #[25, 2, 116, 36, 4, 109],
    #[26, 28, 118, 35, 3, 107],
    #[27, 29, 70, 93, 31, 108],
    #[28, 26, 122, 39, 24, 55],
    #[29, 27, 74, 38, 68, 113],
    #[30, 69, 121, 6, 67, 111],
    #[31, 68, 123, 41, 27, 114],
    #[32, 85, 68, 98, 33, 90],
    #[33, 79, 4, 50, 32, 8],
    #[34, 7, 52, 67, 38, 72],
    #[35, 6, 107, 26, 8, 118],
    #[36, 38, 109, 25, 7, 116],
    #[37, 39, 51, 69, 41, 117],
    #[38, 36, 113, 29, 34, 74],
    #[39, 37, 55, 28, 92, 122],
    #[40, 93, 112, 2, 91, 120],
    #[41, 92, 114, 31, 37, 123],
    #[42, 0, 100, 61, 12, 82],
    #[43, 14, 98, 115, 11, 32],
    #[44, 15, 99, 59, 48, 83],
    #[45, 12, 95, 17, 0, 80],
    #[46, 13, 126, 64, 16, 79],
    #[47, 48, 96, 63, 15, 124],
    #[48, 47, 102, 18, 44, 86],
    #[49, 102, 92, 81, 50, 66],
    #[50, 96, 8, 33, 49, 4],
    #[51, 57, 45, 117, 55, 17],
    #[52, 111, 42, 72, 56, 61],
    #[53, 55, 44, 71, 57, 59],
    #[54, 113, 43, 119, 58, 115],
    #[55, 53, 48, 122, 51, 18],
    #[56, 107, 15, 75, 52, 22],
    #[57, 51, 0, 76, 53, 1],
    #[58, 109, 16, 77, 54, 23],
    #[59, 1, 83, 44, 19, 99],
    #[60, 21, 81, 94, 18, 49],
    #[61, 22, 82, 42, 65, 100],
    #[62, 19, 78, 10, 1, 97],
    #[63, 20, 124, 47, 23, 96],
    #[64, 65, 79, 46, 22, 126],
    #[65, 64, 85, 11, 61, 103],
    #[66, 4, 73, 92, 2, 110],
    #[67, 5, 72, 34, 30, 52],
    #[68, 31, 119, 90, 29, 54],
    #[69, 30, 117, 37, 5, 51],
    #[70, 76, 62, 108, 74, 10],
    #[71, 120, 59, 53, 75, 44],
    #[72, 74, 61, 52, 76, 42],
    #[73, 122, 60, 110, 77, 94],
    #[74, 72, 65, 113, 70, 11],
    #[75, 116, 22, 56, 71, 15],
    #[76, 70, 1, 57, 72, 0],
    #[77, 118, 23, 58, 73, 16],
    #[78, 87, 27, 97, 84, 93],
    #[79, 33, 25, 126, 85, 36],
    #[80, 89, 69, 95, 86, 37],
    #[81, 84, 66, 49, 87, 92],
    #[82, 125, 67, 100, 88, 34],
    #[83, 86, 24, 99, 89, 91],
    #[84, 81, 2, 127, 78, 40],
    #[85, 32, 29, 103, 79, 38],
    #[86, 83, 28, 102, 80, 39],
    #[87, 78, 31, 104, 81, 41],
    #[88, 124, 3, 105, 82, 7],
    #[89, 80, 5, 106, 83, 9],
    #[90, 8, 54, 68, 6, 119],
    #[91, 9, 53, 24, 40, 71],
    #[92, 41, 110, 66, 39, 73],
    #[93, 40, 108, 27, 9, 70],
    #[94, 16, 49, 60, 13, 81],
    #[95, 104, 37, 80, 101, 69],
    #[96, 50, 35, 124, 102, 26],
    #[97, 106, 93, 78, 103, 27],
    #[98, 101, 90, 32, 104, 68],
    #[99, 127, 91, 83, 105, 24],
    #[100, 103, 34, 82, 106, 67],
    #[101, 98, 6, 125, 95, 30],
    #[102, 49, 39, 86, 96, 28],
    #[103, 100, 38, 85, 97, 29],
    #[104, 95, 41, 87, 98, 31],
    #[105, 126, 7, 88, 99, 3],
    #[106, 97, 9, 89, 100, 5],
    #[107, 56, 47, 118, 111, 63],
    #[108, 114, 10, 70, 112, 62],
    #[109, 58, 46, 116, 113, 64],
    #[110, 112, 94, 73, 114, 60],
    #[111, 52, 12, 121, 107, 20],
    #[112, 110, 13, 120, 108, 19],
    #[113, 54, 11, 74, 109, 65],
    #[114, 108, 14, 123, 110, 21],
    #[115, 23, 32, 43, 20, 98],
    #[116, 75, 64, 109, 120, 46],
    #[117, 123, 17, 51, 121, 45],
    #[118, 77, 63, 107, 122, 47],
    #[119, 121, 115, 54, 123, 43],
    #[120, 71, 19, 112, 116, 13],
    #[121, 119, 20, 111, 117, 12],
    #[122, 73, 18, 55, 118, 48],
    #[123, 117, 21, 114, 119, 14],
    #[124, 88, 26, 96, 125, 35],
    #[125, 82, 30, 101, 124, 6],
    #[126, 105, 36, 79, 127, 25],
    #[127, 99, 40, 84, 126, 2]] : Array (Array ℕ)).getD k.val #[]).getD j.val 0)
private def prev53_5 (k : Fin 128) (j : Fin 6) : Fin 128 :=
  Fin.ofNat 128 (((#[#[0, 42, 57, 1, 45, 76],
    #[1, 59, 76, 0, 62, 57],
    #[2, 25, 84, 40, 66, 127],
    #[3, 24, 88, 7, 26, 105],
    #[4, 66, 33, 8, 25, 50],
    #[5, 67, 89, 9, 69, 106],
    #[6, 35, 101, 30, 90, 125],
    #[7, 34, 105, 3, 36, 88],
    #[8, 90, 50, 4, 35, 33],
    #[9, 91, 106, 5, 93, 89],
    #[10, 11, 108, 62, 14, 70],
    #[11, 10, 113, 65, 43, 74],
    #[12, 45, 111, 20, 42, 121],
    #[13, 46, 112, 19, 94, 120],
    #[14, 43, 114, 21, 10, 123],
    #[15, 44, 56, 22, 47, 75],
    #[16, 94, 58, 23, 46, 77],
    #[17, 18, 117, 45, 21, 51],
    #[18, 17, 122, 48, 60, 55],
    #[19, 62, 120, 13, 59, 112],
    #[20, 63, 121, 12, 115, 111],
    #[21, 60, 123, 14, 17, 114],
    #[22, 61, 75, 15, 64, 56],
    #[23, 115, 77, 16, 63, 58],
    #[24, 3, 83, 91, 28, 99],
    #[25, 2, 79, 36, 4, 126],
    #[26, 28, 124, 35, 3, 96],
    #[27, 29, 78, 93, 31, 97],
    #[28, 26, 86, 39, 24, 102],
    #[29, 27, 85, 38, 68, 103],
    #[30, 69, 125, 6, 67, 101],
    #[31, 68, 87, 41, 27, 104],
    #[32, 85, 115, 98, 33, 43],
    #[33, 79, 23, 50, 32, 16],
    #[34, 7, 100, 67, 38, 82],
    #[35, 6, 96, 26, 8, 124],
    #[36, 38, 126, 25, 7, 79],
    #[37, 39, 95, 69, 41, 80],
    #[38, 36, 103, 29, 34, 85],
    #[39, 37, 102, 28, 92, 86],
    #[40, 93, 127, 2, 91, 84],
    #[41, 92, 104, 31, 37, 87],
    #[42, 0, 52, 61, 12, 72],
    #[43, 14, 54, 115, 11, 119],
    #[44, 15, 53, 59, 48, 71],
    #[45, 12, 51, 17, 0, 117],
    #[46, 13, 109, 64, 16, 116],
    #[47, 48, 107, 63, 15, 118],
    #[48, 47, 55, 18, 44, 122],
    #[49, 102, 94, 81, 50, 60],
    #[50, 96, 16, 33, 49, 23],
    #[51, 57, 37, 117, 55, 69],
    #[52, 111, 34, 72, 56, 67],
    #[53, 55, 91, 71, 57, 24],
    #[54, 113, 90, 119, 58, 68],
    #[55, 53, 39, 122, 51, 28],
    #[56, 107, 7, 75, 52, 3],
    #[57, 51, 9, 76, 53, 5],
    #[58, 109, 8, 77, 54, 4],
    #[59, 1, 71, 44, 19, 53],
    #[60, 21, 73, 94, 18, 110],
    #[61, 22, 72, 42, 65, 52],
    #[62, 19, 70, 10, 1, 108],
    #[63, 20, 118, 47, 23, 107],
    #[64, 65, 116, 46, 22, 109],
    #[65, 64, 74, 11, 61, 113],
    #[66, 4, 81, 92, 2, 49],
    #[67, 5, 82, 34, 30, 100],
    #[68, 31, 32, 90, 29, 98],
    #[69, 30, 80, 37, 5, 95],
    #[70, 76, 27, 108, 74, 93],
    #[71, 120, 24, 53, 75, 91],
    #[72, 74, 67, 52, 76, 34],
    #[73, 122, 66, 110, 77, 92],
    #[74, 72, 29, 113, 70, 38],
    #[75, 116, 3, 56, 71, 7],
    #[76, 70, 5, 57, 72, 9],
    #[77, 118, 4, 58, 73, 8],
    #[78, 87, 62, 97, 84, 10],
    #[79, 33, 64, 126, 85, 46],
    #[80, 89, 17, 95, 86, 45],
    #[81, 84, 60, 49, 87, 94],
    #[82, 125, 61, 100, 88, 42],
    #[83, 86, 59, 99, 89, 44],
    #[84, 81, 19, 127, 78, 13],
    #[85, 32, 65, 103, 79, 11],
    #[86, 83, 18, 102, 80, 48],
    #[87, 78, 21, 104, 81, 14],
    #[88, 124, 22, 105, 82, 15],
    #[89, 80, 1, 106, 83, 0],
    #[90, 8, 98, 68, 6, 32],
    #[91, 9, 99, 24, 40, 83],
    #[92, 41, 49, 66, 39, 81],
    #[93, 40, 97, 27, 9, 78],
    #[94, 16, 110, 60, 13, 73],
    #[95, 104, 45, 80, 101, 17],
    #[96, 50, 47, 124, 102, 63],
    #[97, 106, 10, 78, 103, 62],
    #[98, 101, 43, 32, 104, 115],
    #[99, 127, 44, 83, 105, 59],
    #[100, 103, 42, 82, 106, 61],
    #[101, 98, 12, 125, 95, 20],
    #[102, 49, 48, 86, 96, 18],
    #[103, 100, 11, 85, 97, 65],
    #[104, 95, 14, 87, 98, 21],
    #[105, 126, 15, 88, 99, 22],
    #[106, 97, 0, 89, 100, 1],
    #[107, 56, 35, 118, 111, 26],
    #[108, 114, 93, 70, 112, 27],
    #[109, 58, 36, 116, 113, 25],
    #[110, 112, 92, 73, 114, 66],
    #[111, 52, 6, 121, 107, 30],
    #[112, 110, 40, 120, 108, 2],
    #[113, 54, 38, 74, 109, 29],
    #[114, 108, 41, 123, 110, 31],
    #[115, 23, 119, 43, 20, 54],
    #[116, 75, 25, 109, 120, 36],
    #[117, 123, 69, 51, 121, 37],
    #[118, 77, 26, 107, 122, 35],
    #[119, 121, 68, 54, 123, 90],
    #[120, 71, 2, 112, 116, 40],
    #[121, 119, 30, 111, 117, 6],
    #[122, 73, 28, 55, 118, 39],
    #[123, 117, 31, 114, 119, 41],
    #[124, 88, 63, 96, 125, 47],
    #[125, 82, 20, 101, 124, 12],
    #[126, 105, 46, 79, 127, 64],
    #[127, 99, 13, 84, 126, 19]] : Array (Array ℕ)).getD k.val #[]).getD j.val 0)
set_option maxHeartbeats 1600000 in
private theorem cert53_5 : ∃ c, c ∈ Subgroup.centralizer (Subgroup.closure (Set.range e53_5) : Set SylowModel) ∧ c ∉ Subgroup.closure (Set.range e53_5) := by
  refine ⟨root 2 * root 8, centralizes_generators e53_5 _ (by decide +kernel), ?_⟩
  exact outside_of_table e53_5 a53_5 0 next53_5 prev53_5
    (by decide +kernel) (by decide +kernel) (by decide +kernel) _ (by decide +kernel)

private def e53_6 : Fin 6 → SylowModel := ![decode 1024, decode 0, decode 36, decode 1856, decode 0, decode 36]
set_option maxHeartbeats 1600000 in
private theorem edgeEq53_6 : binaryFamily s53 (s53 1) (![false, true, true]) = e53_6 := by decide +kernel
private def a53_6 (k : Fin 128) : SylowModel :=
  decode ((#[0, 1024, 2048, 64, 384, 768, 512, 3072, 1984, 1152, 1792, 1536, 2368, 2432, 2816, 2560, 448, 832, 576, 640, 896, 256, 3776, 3200, 3840, 3584, 1856, 1216, 1472, 1920, 1664, 1280, 2240, 2624, 2880, 2688, 2944, 2304, 704, 960, 320, 128, 1700, 228, 3648, 3520, 3264, 3968, 3712, 3328, 1088, 1344, 1728, 1408, 3008, 2752, 2112, 2176, 192, 3364, 1380, 1572, 1444, 1188, 2660, 164, 356, 996, 740, 3392, 3136, 4032, 3456, 1600, 2496, 4068, 3492, 3620, 3876, 1508, 1636, 1892, 1316, 1060, 1956, 2852, 3044, 2404, 2148, 292, 932, 676, 612, 868, 484, 3904, 3940, 3300, 3556, 3748, 4004, 3108, 1764, 2020, 1124, 1828, 2724, 2084, 2340, 2276, 2532, 2916, 548, 804, 420, 100, 3172, 3428, 3812, 3236, 1252, 2468, 2212, 2596, 2788, 36, 3684, 2980] : Array ℕ).getD k.val 0)
private def next53_6 (k : Fin 128) (j : Fin 6) : Fin 128 :=
  Fin.ofNat 128 (((#[#[1, 0, 125, 26, 0, 125],
    #[2, 1, 81, 32, 1, 81],
    #[7, 2, 127, 44, 2, 127],
    #[50, 3, 115, 10, 3, 115],
    #[53, 4, 114, 52, 4, 114],
    #[10, 5, 113, 50, 5, 113],
    #[11, 6, 112, 51, 6, 112],
    #[0, 7, 98, 16, 7, 98],
    #[54, 8, 63, 14, 8, 63],
    #[57, 9, 103, 56, 9, 103],
    #[14, 10, 104, 54, 10, 104],
    #[15, 11, 60, 55, 11, 60],
    #[69, 12, 124, 24, 12, 124],
    #[72, 13, 123, 71, 13, 123],
    #[24, 14, 122, 69, 14, 122],
    #[25, 15, 121, 70, 15, 121],
    #[28, 16, 94, 30, 16, 94],
    #[26, 17, 93, 1, 17, 93],
    #[73, 18, 92, 31, 18, 92],
    #[30, 19, 91, 28, 19, 91],
    #[29, 20, 90, 27, 20, 90],
    #[31, 21, 89, 73, 21, 89],
    #[38, 22, 78, 5, 22, 78],
    #[41, 23, 117, 40, 23, 117],
    #[5, 24, 118, 38, 24, 118],
    #[6, 25, 75, 39, 25, 75],
    #[34, 26, 83, 36, 26, 83],
    #[32, 27, 84, 2, 27, 84],
    #[74, 28, 42, 37, 28, 42],
    #[36, 29, 120, 34, 29, 120],
    #[35, 30, 79, 33, 30, 79],
    #[37, 31, 80, 74, 31, 80],
    #[46, 32, 111, 48, 32, 111],
    #[44, 33, 110, 7, 33, 110],
    #[95, 34, 109, 49, 34, 109],
    #[48, 35, 108, 46, 35, 108],
    #[47, 36, 107, 45, 36, 107],
    #[49, 37, 106, 95, 37, 106],
    #[52, 38, 68, 53, 38, 68],
    #[8, 39, 67, 9, 39, 67],
    #[51, 40, 66, 11, 40, 66],
    #[9, 41, 65, 8, 41, 65],
    #[106, 42, 8, 64, 42, 8],
    #[120, 43, 38, 84, 43, 38],
    #[18, 44, 100, 20, 44, 100],
    #[16, 45, 101, 0, 45, 101],
    #[58, 46, 59, 21, 46, 59],
    #[20, 47, 126, 18, 47, 126],
    #[19, 48, 96, 17, 48, 96],
    #[21, 49, 97, 58, 49, 97],
    #[56, 50, 105, 57, 50, 105],
    #[12, 51, 61, 13, 51, 61],
    #[55, 52, 62, 15, 52, 62],
    #[13, 53, 102, 12, 53, 102],
    #[71, 54, 88, 72, 54, 88],
    #[22, 55, 87, 23, 55, 87],
    #[70, 56, 86, 25, 56, 86],
    #[23, 57, 85, 22, 57, 85],
    #[27, 58, 43, 29, 58, 43],
    #[89, 59, 22, 43, 59, 22],
    #[87, 60, 1, 121, 60, 1],
    #[123, 61, 26, 124, 61, 26],
    #[121, 62, 27, 87, 62, 27],
    #[122, 63, 28, 88, 63, 28],
    #[126, 64, 54, 101, 64, 54],
    #[63, 65, 19, 103, 65, 19],
    #[60, 66, 17, 61, 66, 17],
    #[103, 67, 16, 63, 67, 16],
    #[102, 68, 58, 62, 68, 58],
    #[40, 69, 119, 41, 69, 119],
    #[3, 70, 76, 4, 70, 76],
    #[39, 71, 77, 6, 71, 77],
    #[4, 72, 116, 3, 72, 116],
    #[33, 73, 82, 35, 73, 82],
    #[45, 74, 64, 47, 74, 64],
    #[67, 75, 7, 112, 75, 7],
    #[114, 76, 44, 115, 76, 44],
    #[112, 77, 45, 67, 77, 45],
    #[113, 78, 46, 68, 78, 46],
    #[110, 79, 9, 108, 79, 9],
    #[64, 80, 10, 106, 80, 10],
    #[111, 81, 11, 127, 81, 11],
    #[108, 82, 50, 110, 82, 50],
    #[107, 83, 51, 109, 83, 51],
    #[127, 84, 52, 111, 84, 52],
    #[78, 85, 35, 117, 85, 35],
    #[75, 86, 33, 76, 86, 33],
    #[117, 87, 32, 78, 87, 32],
    #[116, 88, 74, 77, 88, 74],
    #[82, 89, 5, 80, 89, 5],
    #[84, 90, 4, 120, 90, 4],
    #[42, 91, 41, 79, 91, 41],
    #[80, 92, 3, 82, 92, 3],
    #[81, 93, 40, 83, 93, 40],
    #[79, 94, 39, 42, 94, 39],
    #[17, 95, 99, 19, 95, 99],
    #[93, 96, 23, 91, 96, 23],
    #[43, 97, 24, 89, 97, 24],
    #[94, 98, 25, 125, 98, 25],
    #[91, 99, 69, 93, 99, 69],
    #[90, 100, 70, 92, 100, 70],
    #[125, 101, 71, 94, 101, 71],
    #[124, 102, 29, 123, 102, 29],
    #[86, 103, 30, 85, 103, 30],
    #[88, 104, 31, 122, 104, 31],
    #[85, 105, 73, 86, 105, 73],
    #[99, 106, 14, 97, 106, 14],
    #[101, 107, 13, 126, 107, 13],
    #[59, 108, 57, 96, 108, 57],
    #[97, 109, 12, 99, 109, 12],
    #[98, 110, 56, 100, 110, 56],
    #[96, 111, 55, 59, 111, 55],
    #[61, 112, 0, 60, 112, 0],
    #[105, 113, 21, 104, 113, 21],
    #[62, 114, 20, 102, 114, 20],
    #[104, 115, 18, 105, 115, 18],
    #[115, 116, 47, 114, 116, 47],
    #[66, 117, 48, 65, 117, 48],
    #[68, 118, 49, 113, 118, 49],
    #[65, 119, 95, 66, 119, 95],
    #[109, 120, 53, 107, 120, 53],
    #[76, 121, 2, 75, 121, 2],
    #[119, 122, 37, 118, 122, 37],
    #[77, 123, 36, 116, 123, 36],
    #[118, 124, 34, 119, 124, 34],
    #[83, 125, 6, 81, 125, 6],
    #[92, 126, 72, 90, 126, 72],
    #[100, 127, 15, 98, 127, 15]] : Array (Array ℕ)).getD k.val #[]).getD j.val 0)
private def prev53_6 (k : Fin 128) (j : Fin 6) : Fin 128 :=
  Fin.ofNat 128 (((#[#[7, 0, 112, 45, 0, 112],
    #[0, 1, 60, 17, 1, 60],
    #[1, 2, 121, 27, 2, 121],
    #[70, 3, 92, 72, 3, 92],
    #[72, 4, 90, 70, 4, 90],
    #[24, 5, 89, 22, 5, 89],
    #[25, 6, 125, 71, 6, 125],
    #[2, 7, 75, 33, 7, 75],
    #[39, 8, 42, 41, 8, 42],
    #[41, 9, 79, 39, 9, 79],
    #[5, 10, 80, 3, 10, 80],
    #[6, 11, 81, 40, 11, 81],
    #[51, 12, 109, 53, 12, 109],
    #[53, 13, 107, 51, 13, 107],
    #[10, 14, 106, 8, 14, 106],
    #[11, 15, 127, 52, 15, 127],
    #[45, 16, 67, 7, 16, 67],
    #[95, 17, 66, 48, 17, 66],
    #[44, 18, 115, 47, 18, 115],
    #[48, 19, 65, 95, 19, 65],
    #[47, 20, 114, 44, 20, 114],
    #[49, 21, 113, 46, 21, 113],
    #[55, 22, 59, 57, 22, 59],
    #[57, 23, 96, 55, 23, 96],
    #[14, 24, 97, 12, 24, 97],
    #[15, 25, 98, 56, 25, 98],
    #[17, 26, 61, 0, 26, 61],
    #[58, 27, 62, 20, 27, 62],
    #[16, 28, 63, 19, 28, 63],
    #[20, 29, 102, 58, 29, 102],
    #[19, 30, 103, 16, 30, 103],
    #[21, 31, 104, 18, 31, 104],
    #[27, 32, 87, 1, 32, 87],
    #[73, 33, 86, 30, 33, 86],
    #[26, 34, 124, 29, 34, 124],
    #[30, 35, 85, 73, 35, 85],
    #[29, 36, 123, 26, 36, 123],
    #[31, 37, 122, 28, 37, 122],
    #[22, 38, 43, 24, 38, 43],
    #[71, 39, 94, 25, 39, 94],
    #[69, 40, 93, 23, 40, 93],
    #[23, 41, 91, 69, 41, 91],
    #[91, 42, 28, 94, 42, 28],
    #[97, 43, 58, 59, 43, 58],
    #[33, 44, 76, 2, 44, 76],
    #[74, 45, 77, 36, 45, 77],
    #[32, 46, 78, 35, 46, 78],
    #[36, 47, 116, 74, 47, 116],
    #[35, 48, 117, 32, 48, 117],
    #[37, 49, 118, 34, 49, 118],
    #[3, 50, 82, 5, 50, 82],
    #[40, 51, 83, 6, 51, 83],
    #[38, 52, 84, 4, 52, 84],
    #[4, 53, 120, 38, 53, 120],
    #[8, 54, 64, 10, 54, 64],
    #[52, 55, 111, 11, 55, 111],
    #[50, 56, 110, 9, 56, 110],
    #[9, 57, 108, 50, 57, 108],
    #[46, 58, 68, 49, 58, 68],
    #[108, 59, 46, 111, 59, 46],
    #[66, 60, 11, 112, 60, 11],
    #[112, 61, 51, 66, 61, 51],
    #[114, 62, 52, 68, 62, 52],
    #[65, 63, 8, 67, 63, 8],
    #[80, 64, 74, 42, 64, 74],
    #[119, 65, 41, 117, 65, 41],
    #[117, 66, 40, 119, 66, 40],
    #[75, 67, 39, 77, 67, 39],
    #[118, 68, 38, 78, 68, 38],
    #[12, 69, 99, 14, 69, 99],
    #[56, 70, 100, 15, 70, 100],
    #[54, 71, 101, 13, 71, 101],
    #[13, 72, 126, 54, 72, 126],
    #[18, 73, 105, 21, 73, 105],
    #[28, 74, 88, 31, 74, 88],
    #[86, 75, 25, 121, 75, 25],
    #[121, 76, 70, 86, 76, 70],
    #[123, 77, 71, 88, 77, 71],
    #[85, 78, 22, 87, 78, 22],
    #[94, 79, 30, 91, 79, 30],
    #[92, 80, 31, 89, 80, 31],
    #[93, 81, 1, 125, 81, 1],
    #[89, 82, 73, 92, 82, 73],
    #[125, 83, 26, 93, 83, 26],
    #[90, 84, 27, 43, 84, 27],
    #[105, 85, 57, 103, 85, 57],
    #[103, 86, 56, 105, 86, 56],
    #[60, 87, 55, 62, 87, 55],
    #[104, 88, 54, 63, 88, 54],
    #[59, 89, 21, 97, 89, 21],
    #[100, 90, 20, 126, 90, 20],
    #[99, 91, 19, 96, 91, 19],
    #[126, 92, 18, 100, 92, 18],
    #[96, 93, 17, 99, 93, 17],
    #[98, 94, 16, 101, 94, 16],
    #[34, 95, 119, 37, 95, 119],
    #[111, 96, 48, 108, 96, 48],
    #[109, 97, 49, 106, 97, 49],
    #[110, 98, 7, 127, 98, 7],
    #[106, 99, 95, 109, 99, 95],
    #[127, 100, 44, 110, 100, 44],
    #[107, 101, 45, 64, 101, 45],
    #[68, 102, 53, 114, 102, 53],
    #[67, 103, 9, 65, 103, 9],
    #[115, 104, 10, 113, 104, 10],
    #[113, 105, 50, 115, 105, 50],
    #[42, 106, 37, 80, 106, 37],
    #[83, 107, 36, 120, 107, 36],
    #[82, 108, 35, 79, 108, 35],
    #[120, 109, 34, 83, 109, 34],
    #[79, 110, 33, 82, 110, 33],
    #[81, 111, 32, 84, 111, 32],
    #[77, 112, 6, 75, 112, 6],
    #[78, 113, 5, 118, 113, 5],
    #[76, 114, 4, 116, 114, 4],
    #[116, 115, 3, 76, 115, 3],
    #[88, 116, 72, 123, 116, 72],
    #[87, 117, 23, 85, 117, 23],
    #[124, 118, 24, 122, 118, 24],
    #[122, 119, 69, 124, 119, 69],
    #[43, 120, 29, 90, 120, 29],
    #[62, 121, 15, 60, 121, 15],
    #[63, 122, 14, 104, 122, 14],
    #[61, 123, 13, 102, 123, 13],
    #[102, 124, 12, 61, 124, 12],
    #[101, 125, 0, 98, 125, 0],
    #[64, 126, 47, 107, 126, 47],
    #[84, 127, 2, 81, 127, 2]] : Array (Array ℕ)).getD k.val #[]).getD j.val 0)
set_option maxHeartbeats 1600000 in
private theorem cert53_6 : ∃ c, c ∈ Subgroup.centralizer (Subgroup.closure (Set.range e53_6) : Set SylowModel) ∧ c ∉ Subgroup.closure (Set.range e53_6) := by
  refine ⟨root 2 * root 8, centralizes_generators e53_6 _ (by decide +kernel), ?_⟩
  exact outside_of_table e53_6 a53_6 0 next53_6 prev53_6
    (by decide +kernel) (by decide +kernel) (by decide +kernel) _ (by decide +kernel)

private def e53_7 : Fin 6 → SylowModel := ![decode 0, decode 3360, decode 3332, decode 2048, decode 1632, decode 1284]
set_option maxHeartbeats 1600000 in
private theorem edgeEq53_7 : binaryFamily s53 (s53 0) (![true, true, true]) = e53_7 := by decide +kernel
private def a53_7 (k : Fin 128) : SylowModel :=
  decode ((#[0, 2048, 64, 384, 768, 512, 2368, 2432, 2816, 2560, 448, 832, 576, 640, 896, 256, 1312, 2240, 2624, 2880, 2688, 2944, 2304, 704, 960, 320, 128, 1028, 228, 3744, 1760, 1440, 1568, 1824, 3008, 2752, 2112, 2176, 192, 3076, 1988, 1156, 1796, 1540, 2660, 164, 356, 996, 740, 3168, 3616, 3488, 3232, 1632, 1504, 1248, 1696, 1952, 1056, 2496, 3780, 3204, 3844, 3588, 1860, 1220, 1476, 1924, 1668, 1284, 2852, 3044, 2404, 2148, 292, 932, 676, 612, 868, 484, 3296, 3936, 3680, 3360, 3104, 4000, 1376, 1120, 2016, 1184, 3652, 3524, 3268, 3972, 3716, 3332, 1092, 1348, 1732, 1412, 2724, 2084, 2340, 2276, 2532, 2916, 548, 804, 420, 100, 4064, 3808, 3424, 3872, 1888, 3396, 3140, 4036, 3460, 1604, 2468, 2212, 2596, 2788, 36, 3552, 3908, 2980] : Array ℕ).getD k.val 0)
private def next53_7 (k : Fin 128) (j : Fin 6) : Fin 128 :=
  Fin.ofNat 128 (((#[#[0, 83, 95, 1, 53, 69],
    #[1, 56, 69, 0, 80, 95],
    #[2, 112, 115, 36, 32, 97],
    #[3, 52, 61, 7, 88, 41],
    #[4, 50, 63, 8, 86, 43],
    #[5, 113, 62, 9, 87, 42],
    #[6, 88, 96, 25, 51, 116],
    #[7, 33, 41, 3, 112, 61],
    #[8, 31, 43, 4, 110, 63],
    #[9, 89, 42, 5, 111, 62],
    #[10, 80, 92, 59, 57, 65],
    #[11, 82, 90, 19, 16, 119],
    #[12, 81, 126, 18, 58, 64],
    #[13, 85, 93, 20, 55, 67],
    #[14, 29, 94, 21, 54, 68],
    #[15, 84, 39, 22, 114, 27],
    #[16, 11, 124, 83, 21, 101],
    #[17, 53, 66, 38, 84, 91],
    #[18, 55, 64, 12, 29, 126],
    #[19, 54, 119, 11, 85, 90],
    #[20, 58, 67, 13, 82, 93],
    #[21, 16, 68, 14, 81, 94],
    #[22, 57, 27, 15, 125, 39],
    #[23, 110, 117, 35, 89, 40],
    #[24, 111, 60, 34, 31, 98],
    #[25, 49, 116, 6, 33, 96],
    #[26, 51, 118, 37, 30, 99],
    #[27, 77, 4, 39, 100, 8],
    #[28, 91, 110, 103, 68, 88],
    #[29, 18, 127, 56, 14, 75],
    #[30, 26, 47, 111, 36, 71],
    #[31, 24, 45, 51, 8, 121],
    #[32, 2, 107, 50, 37, 70],
    #[33, 25, 106, 113, 7, 122],
    #[34, 86, 98, 24, 113, 60],
    #[35, 87, 40, 23, 50, 117],
    #[36, 30, 97, 2, 52, 115],
    #[37, 32, 99, 26, 49, 118],
    #[38, 125, 91, 17, 56, 66],
    #[39, 103, 8, 27, 74, 4],
    #[40, 108, 38, 117, 72, 17],
    #[41, 48, 14, 61, 122, 21],
    #[42, 46, 0, 62, 120, 1],
    #[43, 109, 15, 63, 121, 22],
    #[44, 65, 86, 77, 94, 112],
    #[45, 118, 85, 121, 98, 57],
    #[46, 116, 82, 72, 42, 53],
    #[47, 60, 80, 71, 99, 55],
    #[48, 117, 125, 123, 41, 54],
    #[49, 37, 72, 87, 25, 46],
    #[50, 35, 70, 32, 4, 107],
    #[51, 6, 121, 31, 26, 45],
    #[52, 36, 120, 89, 3, 108],
    #[53, 0, 78, 82, 17, 105],
    #[54, 14, 28, 125, 19, 103],
    #[55, 13, 79, 80, 18, 104],
    #[56, 38, 75, 29, 1, 127],
    #[57, 10, 76, 85, 22, 100],
    #[58, 12, 74, 84, 20, 102],
    #[59, 114, 65, 10, 83, 92],
    #[60, 122, 59, 98, 47, 10],
    #[61, 73, 21, 41, 108, 14],
    #[62, 71, 1, 42, 106, 0],
    #[63, 123, 22, 43, 107, 15],
    #[64, 74, 2, 126, 104, 36],
    #[65, 76, 24, 92, 44, 34],
    #[66, 75, 23, 91, 105, 35],
    #[67, 79, 26, 93, 102, 37],
    #[68, 28, 3, 94, 101, 7],
    #[69, 78, 5, 95, 127, 9],
    #[70, 99, 58, 107, 117, 84],
    #[71, 97, 55, 47, 62, 80],
    #[72, 40, 53, 46, 118, 82],
    #[73, 98, 114, 109, 61, 81],
    #[74, 39, 50, 102, 64, 32],
    #[75, 94, 52, 127, 66, 89],
    #[76, 93, 51, 100, 65, 31],
    #[77, 126, 112, 44, 27, 86],
    #[78, 90, 49, 105, 69, 87],
    #[79, 92, 111, 104, 67, 30],
    #[80, 1, 104, 55, 10, 79],
    #[81, 21, 44, 114, 12, 77],
    #[82, 20, 105, 53, 11, 78],
    #[83, 59, 101, 16, 0, 124],
    #[84, 17, 102, 58, 15, 74],
    #[85, 19, 100, 57, 13, 76],
    #[86, 4, 109, 112, 34, 73],
    #[87, 5, 46, 49, 35, 72],
    #[88, 3, 48, 110, 6, 123],
    #[89, 23, 108, 52, 9, 120],
    #[90, 100, 6, 119, 78, 25],
    #[91, 102, 35, 66, 28, 23],
    #[92, 101, 34, 65, 79, 24],
    #[93, 105, 37, 67, 76, 26],
    #[94, 44, 7, 68, 75, 3],
    #[95, 104, 9, 69, 124, 5],
    #[96, 106, 11, 116, 123, 19],
    #[97, 107, 12, 115, 71, 18],
    #[98, 45, 10, 60, 73, 59],
    #[99, 47, 13, 118, 70, 20],
    #[100, 27, 31, 76, 90, 51],
    #[101, 68, 33, 124, 92, 113],
    #[102, 67, 32, 74, 91, 50],
    #[103, 119, 88, 28, 39, 110],
    #[104, 64, 30, 79, 95, 111],
    #[105, 66, 87, 78, 93, 49],
    #[106, 62, 83, 122, 96, 16],
    #[107, 63, 84, 70, 97, 58],
    #[108, 61, 29, 120, 40, 56],
    #[109, 115, 81, 73, 43, 114],
    #[110, 8, 123, 88, 23, 48],
    #[111, 9, 71, 30, 24, 47],
    #[112, 7, 73, 86, 2, 109],
    #[113, 34, 122, 33, 5, 106],
    #[114, 15, 77, 81, 59, 44],
    #[115, 120, 18, 97, 109, 12],
    #[116, 121, 19, 96, 46, 11],
    #[117, 70, 17, 40, 48, 38],
    #[118, 72, 20, 99, 45, 13],
    #[119, 124, 25, 90, 103, 6],
    #[120, 42, 56, 108, 115, 29],
    #[121, 43, 57, 45, 116, 85],
    #[122, 41, 16, 106, 60, 83],
    #[123, 96, 54, 48, 63, 125],
    #[124, 95, 113, 101, 119, 33],
    #[125, 22, 103, 54, 38, 28],
    #[126, 127, 36, 64, 77, 2],
    #[127, 69, 89, 75, 126, 52]] : Array (Array ℕ)).getD k.val #[]).getD j.val 0)
private def prev53_7 (k : Fin 128) (j : Fin 6) : Fin 128 :=
  Fin.ofNat 128 (((#[#[0, 53, 42, 1, 83, 62],
    #[1, 80, 62, 0, 56, 42],
    #[2, 32, 64, 36, 112, 126],
    #[3, 88, 68, 7, 52, 94],
    #[4, 86, 27, 8, 50, 39],
    #[5, 87, 69, 9, 113, 95],
    #[6, 51, 90, 25, 88, 119],
    #[7, 112, 94, 3, 33, 68],
    #[8, 110, 39, 4, 31, 27],
    #[9, 111, 95, 5, 89, 69],
    #[10, 57, 98, 59, 80, 60],
    #[11, 16, 96, 19, 82, 116],
    #[12, 58, 97, 18, 81, 115],
    #[13, 55, 99, 20, 85, 118],
    #[14, 54, 41, 21, 29, 61],
    #[15, 114, 43, 22, 84, 63],
    #[16, 21, 122, 83, 11, 106],
    #[17, 84, 117, 38, 53, 40],
    #[18, 29, 115, 12, 55, 97],
    #[19, 85, 116, 11, 54, 96],
    #[20, 82, 118, 13, 58, 99],
    #[21, 81, 61, 14, 16, 41],
    #[22, 125, 63, 15, 57, 43],
    #[23, 89, 66, 35, 110, 91],
    #[24, 31, 65, 34, 111, 92],
    #[25, 33, 119, 6, 49, 90],
    #[26, 30, 67, 37, 51, 93],
    #[27, 100, 22, 39, 77, 15],
    #[28, 68, 54, 103, 91, 125],
    #[29, 14, 108, 56, 18, 120],
    #[30, 36, 104, 111, 26, 79],
    #[31, 8, 100, 51, 24, 76],
    #[32, 37, 102, 50, 2, 74],
    #[33, 7, 101, 113, 25, 124],
    #[34, 113, 92, 24, 86, 65],
    #[35, 50, 91, 23, 87, 66],
    #[36, 52, 126, 2, 30, 64],
    #[37, 49, 93, 26, 32, 67],
    #[38, 56, 40, 17, 125, 117],
    #[39, 74, 15, 27, 103, 22],
    #[40, 72, 35, 117, 108, 23],
    #[41, 122, 7, 61, 48, 3],
    #[42, 120, 9, 62, 46, 5],
    #[43, 121, 8, 63, 109, 4],
    #[44, 94, 81, 77, 65, 114],
    #[45, 98, 31, 121, 118, 51],
    #[46, 42, 87, 72, 116, 49],
    #[47, 99, 30, 71, 60, 111],
    #[48, 41, 88, 123, 117, 110],
    #[49, 25, 78, 87, 37, 105],
    #[50, 4, 74, 32, 35, 102],
    #[51, 26, 76, 31, 6, 100],
    #[52, 3, 75, 89, 36, 127],
    #[53, 17, 72, 82, 0, 46],
    #[54, 19, 123, 125, 14, 48],
    #[55, 18, 71, 80, 13, 47],
    #[56, 1, 120, 29, 38, 108],
    #[57, 22, 121, 85, 10, 45],
    #[58, 20, 70, 84, 12, 107],
    #[59, 83, 60, 10, 114, 98],
    #[60, 47, 24, 98, 122, 34],
    #[61, 108, 3, 41, 73, 7],
    #[62, 106, 5, 42, 71, 9],
    #[63, 107, 4, 43, 123, 8],
    #[64, 104, 18, 126, 74, 12],
    #[65, 44, 59, 92, 76, 10],
    #[66, 105, 17, 91, 75, 38],
    #[67, 102, 20, 93, 79, 13],
    #[68, 101, 21, 94, 28, 14],
    #[69, 127, 1, 95, 78, 0],
    #[70, 117, 50, 107, 99, 32],
    #[71, 62, 111, 47, 97, 30],
    #[72, 118, 49, 46, 40, 87],
    #[73, 61, 112, 109, 98, 86],
    #[74, 64, 58, 102, 39, 84],
    #[75, 66, 56, 127, 94, 29],
    #[76, 65, 57, 100, 93, 85],
    #[77, 27, 114, 44, 126, 81],
    #[78, 69, 53, 105, 90, 82],
    #[79, 67, 55, 104, 92, 80],
    #[80, 10, 47, 55, 1, 71],
    #[81, 12, 109, 114, 21, 73],
    #[82, 11, 46, 53, 20, 72],
    #[83, 0, 106, 16, 59, 122],
    #[84, 15, 107, 58, 17, 70],
    #[85, 13, 45, 57, 19, 121],
    #[86, 34, 44, 112, 4, 77],
    #[87, 35, 105, 49, 5, 78],
    #[88, 6, 103, 110, 3, 28],
    #[89, 9, 127, 52, 23, 75],
    #[90, 78, 11, 119, 100, 19],
    #[91, 28, 38, 66, 102, 17],
    #[92, 79, 10, 65, 101, 59],
    #[93, 76, 13, 67, 105, 20],
    #[94, 75, 14, 68, 44, 21],
    #[95, 124, 0, 69, 104, 1],
    #[96, 123, 6, 116, 106, 25],
    #[97, 71, 36, 115, 107, 2],
    #[98, 73, 34, 60, 45, 24],
    #[99, 70, 37, 118, 47, 26],
    #[100, 90, 85, 76, 27, 57],
    #[101, 92, 83, 124, 68, 16],
    #[102, 91, 84, 74, 67, 58],
    #[103, 39, 125, 28, 119, 54],
    #[104, 95, 80, 79, 64, 55],
    #[105, 93, 82, 78, 66, 53],
    #[106, 96, 33, 122, 62, 113],
    #[107, 97, 32, 70, 63, 50],
    #[108, 40, 89, 120, 61, 52],
    #[109, 43, 86, 73, 115, 112],
    #[110, 23, 28, 88, 8, 103],
    #[111, 24, 79, 30, 9, 104],
    #[112, 2, 77, 86, 7, 44],
    #[113, 5, 124, 33, 34, 101],
    #[114, 59, 73, 81, 15, 109],
    #[115, 109, 2, 97, 120, 36],
    #[116, 46, 25, 96, 121, 6],
    #[117, 48, 23, 40, 70, 35],
    #[118, 45, 26, 99, 72, 37],
    #[119, 103, 19, 90, 124, 11],
    #[120, 115, 52, 108, 42, 89],
    #[121, 116, 51, 45, 43, 31],
    #[122, 60, 113, 106, 41, 33],
    #[123, 63, 110, 48, 96, 88],
    #[124, 119, 16, 101, 95, 83],
    #[125, 38, 48, 54, 22, 123],
    #[126, 77, 12, 64, 127, 18],
    #[127, 126, 29, 75, 69, 56]] : Array (Array ℕ)).getD k.val #[]).getD j.val 0)
set_option maxHeartbeats 1600000 in
private theorem cert53_7 : ∃ c, c ∈ Subgroup.centralizer (Subgroup.closure (Set.range e53_7) : Set SylowModel) ∧ c ∉ Subgroup.closure (Set.range e53_7) := by
  refine ⟨root 2 * root 8, centralizes_generators e53_7 _ (by decide +kernel), ?_⟩
  exact outside_of_table e53_7 a53_7 0 next53_7 prev53_7
    (by decide +kernel) (by decide +kernel) (by decide +kernel) _ (by decide +kernel)

private def s54 : Fin 3 → SylowModel := ![rootOne ^ 3, root 4 * root 5 * root 8 * root 9, root 2 * root 8]
set_option maxHeartbeats 1600000 in
private theorem gen54 : Subgroup.closure (Set.range s54) = smallParityCensusNode 54 := by
  rw [node54]
  exact closure_eq_words s54 o54 (![[1], [2], [0]]) (![[2], [0], [1], [0, 0], [0, 0, 0, 1, 0, 1, 1, 1], [1, 1, 1, 2, 1, 2], [0, 0, 1, 0, 0, 1, 1, 1], [1, 2, 1, 2]]) (by decide +kernel) (by decide +kernel)

private def e54_1 : Fin 6 → SylowModel := ![decode 0, decode 816, decode 260, decode 2048, decode 112, decode 260]
set_option maxHeartbeats 1600000 in
private theorem edgeEq54_1 : binaryFamily s54 (s54 0) (![true, false, false]) = e54_1 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert54_1 : Subgroup.closure (Set.range e54_1) ≤ character.ker := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨j, rfl⟩
  exact (show ∀ j, e54_1 j ∈ character.ker from by decide +kernel) j

private def e54_2 : Fin 6 → SylowModel := ![decode 1024, decode 0, decode 260, decode 1856, decode 512, decode 4]
set_option maxHeartbeats 1600000 in
private theorem edgeEq54_2 : binaryFamily s54 (s54 1) (![false, true, false]) = e54_2 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert54_2 : Represented smallParityCensusNode (Subgroup.closure (Set.range e54_2)) := by
  refine ⟨85, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node85]
  exact closure_eq_words _ o85 (![[1], [], [0], [1, 2], [0, 0], [0, 6]]) (![[2], [0], [0, 0, 0, 3], [0, 0], [0, 0, 3, 3], [2, 5], [2, 4, 5]]) (by decide +kernel) (by decide +kernel)

private def e54_3 : Fin 6 → SylowModel := ![decode 0, decode 3888, decode 260, decode 2048, decode 1136, decode 260]
set_option maxHeartbeats 1600000 in
private theorem edgeEq54_3 : binaryFamily s54 (s54 0) (![true, true, false]) = e54_3 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert54_3 : Represented smallParityCensusNode (Subgroup.closure (Set.range e54_3)) := by
  refine ⟨93, root 2 * root 3 * root 4 * root 7, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node93]
  exact closure_eq_words _ o93 (![[], [0, 0, 1, 3], [0, 4], [3, 2], [1, 6], [0, 4]]) (![[1, 1, 1, 3, 1, 2, 3], [1, 1, 1, 1, 4], [1, 1, 3], [4, 4], [1, 1, 1, 3, 1, 3], [1, 1, 1, 1, 1, 4], [1, 1, 1, 1]]) (by decide +kernel) (by decide +kernel)

private def e54_4 : Fin 6 → SylowModel := ![decode 1024, decode 816, decode 0, decode 1024, decode 560, decode 512]
set_option maxHeartbeats 1600000 in
private theorem edgeEq54_4 : binaryFamily s54 (s54 2) (![false, false, true]) = e54_4 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert54_4 : Represented smallParityCensusNode (Subgroup.closure (Set.range e54_4)) := by
  refine ⟨62, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node62]
  exact closure_eq_words _ o62 (![[0], [1, 6], [], [0], [1], [4]]) (![[0], [4], [0, 0], [0, 0, 0, 1, 0, 1, 5], [5], [0, 0, 1, 0, 0, 1, 5], [1, 4, 5]]) (by decide +kernel) (by decide +kernel)

private def e54_5 : Fin 6 → SylowModel := ![decode 0, decode 816, decode 3332, decode 2048, decode 112, decode 1284]
set_option maxHeartbeats 1600000 in
private theorem edgeEq54_5 : binaryFamily s54 (s54 0) (![true, false, true]) = e54_5 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert54_5 : Represented smallParityCensusNode (Subgroup.closure (Set.range e54_5)) := by
  refine ⟨70, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node70]
  exact closure_eq_words _ o70 (![[], [1, 4, 6], [2, 5, 0], [2, 4, 6], [1, 3, 4, 5], [0, 4, 5]]) (![[1, 5, 4], [2, 4, 5], [1, 1, 1, 2, 4, 2], [2, 1, 4, 5], [1, 1], [2, 1, 5, 4], [1, 2, 4, 5]]) (by decide +kernel) (by decide +kernel)

private def e54_6 : Fin 6 → SylowModel := ![decode 1024, decode 0, decode 52, decode 1856, decode 512, decode 820]
set_option maxHeartbeats 1600000 in
private theorem edgeEq54_6 : binaryFamily s54 (s54 1) (![false, true, true]) = e54_6 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert54_6 : Represented smallParityCensusNode (Subgroup.closure (Set.range e54_6)) := by
  refine ⟨87, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node87]
  exact closure_eq_words _ o87 (![[1], [], [0, 4, 6], [1, 3], [4, 6], [0, 6]]) (![[2, 4], [0], [0, 0], [0, 0, 0, 3], [2, 2, 4], [0, 0, 3, 3], [2, 2]]) (by decide +kernel) (by decide +kernel)

private def e54_7 : Fin 6 → SylowModel := ![decode 0, decode 3888, decode 3332, decode 2048, decode 1136, decode 1284]
set_option maxHeartbeats 1600000 in
private theorem edgeEq54_7 : binaryFamily s54 (s54 0) (![true, true, true]) = e54_7 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert54_7 : Represented smallParityCensusNode (Subgroup.closure (Set.range e54_7)) := by
  refine ⟨88, root 1 * root 2 * root 4 * root 5 * root 7 * root 9, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node88]
  exact closure_eq_words _ o88 (![[], [1, 2, 3], [0, 1, 2], [2, 3, 4], [3, 1, 4], [1, 0, 4, 6]]) (![[1, 1, 5, 4], [2, 4, 5], [1, 3, 1, 3], [1, 2, 2, 1], [1, 1, 1, 1, 1, 4], [1, 2, 1, 2], [1, 1, 1, 1]]) (by decide +kernel) (by decide +kernel)

private def s55 : Fin 3 → SylowModel := ![rootOne ^ 3, root 2 * root 4 * root 8, root 2 * root 3 * root 4 * root 5 * root 7 * root 8 * root 9]
set_option maxHeartbeats 1600000 in
private theorem gen55 : Subgroup.closure (Set.range s55) = smallParityCensusNode 55 := by
  rw [node55]
  exact closure_eq_words s55 o55 (![[1], [0], [2]]) (![[1], [0], [2], [0, 0], [0, 0, 0, 2, 0, 1, 2, 1], [1, 1], [1, 1, 2, 2], [1, 2, 1, 2]]) (by decide +kernel) (by decide +kernel)

private def e55_1 : Fin 6 → SylowModel := ![decode 0, decode 276, decode 956, decode 2048, decode 276, decode 492]
set_option maxHeartbeats 1600000 in
private theorem edgeEq55_1 : binaryFamily s55 (s55 0) (![true, false, false]) = e55_1 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert55_1 : Subgroup.closure (Set.range e55_1) ≤ character.ker := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨j, rfl⟩
  exact (show ∀ j, e55_1 j ∈ character.ker from by decide +kernel) j

private def e55_2 : Fin 6 → SylowModel := ![decode 1024, decode 0, decode 956, decode 1024, decode 768, decode 316]
set_option maxHeartbeats 1600000 in
private theorem edgeEq55_2 : binaryFamily s55 (s55 1) (![false, true, false]) = e55_2 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert55_2 : Represented smallParityCensusNode (Subgroup.closure (Set.range e55_2)) := by
  refine ⟨65, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node65]
  exact closure_eq_words _ o65 (![[0], [], [1], [0], [4], [1, 5, 6]]) (![[0], [2], [0, 0], [0, 0, 0, 2, 0, 4, 5], [4], [2, 2, 4], [2, 4, 5]]) (by decide +kernel) (by decide +kernel)

private def e55_3 : Fin 6 → SylowModel := ![decode 0, decode 3348, decode 956, decode 2048, decode 1300, decode 492]
set_option maxHeartbeats 1600000 in
private theorem edgeEq55_3 : binaryFamily s55 (s55 0) (![true, true, false]) = e55_3 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert55_3 : Represented smallParityCensusNode (Subgroup.closure (Set.range e55_3)) := by
  refine ⟨73, root 1 * root 2 * root 4 * root 5 * root 7 * root 9, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node73]
  exact closure_eq_words _ o73 (![[], [0, 1, 1, 2], [1, 5], [2, 4], [0, 5], [3, 1]]) (![[1, 1, 1, 5, 5], [1, 1, 4, 5, 4], [1, 1, 1, 5, 4, 2], [1, 2, 4, 2], [1, 1, 1, 2, 1, 5], [1, 2, 2, 4], [1, 5, 4, 2]]) (by decide +kernel) (by decide +kernel)

private def e55_4 : Fin 6 → SylowModel := ![decode 1024, decode 276, decode 0, decode 1360, decode 916, decode 128]
set_option maxHeartbeats 1600000 in
private theorem edgeEq55_4 : binaryFamily s55 (s55 2) (![false, false, true]) = e55_4 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert55_4 : Represented smallParityCensusNode (Subgroup.closure (Set.range e55_4)) := by
  refine ⟨84, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node84]
  exact closure_eq_words _ o84 (![[1], [0], [], [0, 1, 2, 0], [0, 4, 6], [4, 5]]) (![[1], [0], [0, 0, 3, 5, 0], [0, 0], [1, 1, 5], [1, 1], [1, 4, 5]]) (by decide +kernel) (by decide +kernel)

private def e55_5 : Fin 6 → SylowModel := ![decode 0, decode 276, decode 4028, decode 2048, decode 276, decode 1516]
set_option maxHeartbeats 1600000 in
private theorem edgeEq55_5 : binaryFamily s55 (s55 0) (![true, false, true]) = e55_5 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert55_5 : Represented smallParityCensusNode (Subgroup.closure (Set.range e55_5)) := by
  refine ⟨94, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node94]
  exact closure_eq_words _ o94 (![[], [0, 2, 4, 5], [1, 3, 6], [3, 2], [0, 2, 4, 5], [4, 1]]) (![[1, 2, 3, 2], [5, 2, 5], [2, 2, 3], [3, 2, 2, 3], [5, 2], [1, 1], [1, 2, 1, 5]]) (by decide +kernel) (by decide +kernel)

private def e55_6 : Fin 6 → SylowModel := ![decode 1024, decode 0, decode 40, decode 1024, decode 768, decode 424]
set_option maxHeartbeats 1600000 in
private theorem edgeEq55_6 : binaryFamily s55 (s55 1) (![false, true, true]) = e55_6 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert55_6 : Represented smallParityCensusNode (Subgroup.closure (Set.range e55_6)) := by
  refine ⟨79, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node79]
  exact closure_eq_words _ o79 (![[1], [], [0, 6], [1], [4, 6], [0, 4, 5, 6]]) (![[2, 2, 2], [0], [0, 0], [0, 0, 0, 5, 0, 5], [2, 2, 4], [2, 4, 5], [2, 2]]) (by decide +kernel) (by decide +kernel)

private def e55_7 : Fin 6 → SylowModel := ![decode 0, decode 3348, decode 4028, decode 2048, decode 1300, decode 1516]
set_option maxHeartbeats 1600000 in
private theorem edgeEq55_7 : binaryFamily s55 (s55 0) (![true, true, true]) = e55_7 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert55_7 : Represented smallParityCensusNode (Subgroup.closure (Set.range e55_7)) := by
  refine ⟨80, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node80]
  exact closure_eq_words _ o80 (![[], [0, 1, 2, 4, 6], [1, 2, 6], [2, 3, 4], [1, 0], [4, 5, 1]]) (![[2, 4], [5, 2, 5], [3, 2, 2, 3], [1, 1, 2, 2], [1, 1, 1, 2, 4, 2], [1, 2, 1, 2], [1, 5, 1, 5]]) (by decide +kernel) (by decide +kernel)

private def s56 : Fin 3 → SylowModel := ![rootOne ^ 3, root 2 * root 4 * root 8, root 2 * root 3 * root 4 * root 5 * root 6 * root 9]
set_option maxHeartbeats 1600000 in
private theorem gen56 : Subgroup.closure (Set.range s56) = smallParityCensusNode 56 := by
  rw [node56]
  exact closure_eq_words s56 o56 (![[1], [0], [2]]) (![[1], [0], [2], [0, 0], [0, 0, 0, 2, 0, 2], [1, 1], [0, 0, 0, 2, 2, 0], [0, 0, 0, 2, 2, 0, 2, 2]]) (by decide +kernel) (by decide +kernel)

private def e56_1 : Fin 6 → SylowModel := ![decode 0, decode 276, decode 636, decode 2048, decode 276, decode 684]
set_option maxHeartbeats 1600000 in
private theorem edgeEq56_1 : binaryFamily s56 (s56 0) (![true, false, false]) = e56_1 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert56_1 : Subgroup.closure (Set.range e56_1) ≤ character.ker := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨j, rfl⟩
  exact (show ∀ j, e56_1 j ∈ character.ker from by decide +kernel) j

private def e56_2 : Fin 6 → SylowModel := ![decode 1024, decode 0, decode 636, decode 1024, decode 768, decode 252]
set_option maxHeartbeats 1600000 in
private theorem edgeEq56_2 : binaryFamily s56 (s56 1) (![false, true, false]) = e56_2 := by decide +kernel
private def a56_2 (k : Fin 128) : SylowModel :=
  decode ((#[0, 1024, 2048, 764, 384, 768, 512, 3072, 1836, 1152, 1792, 1536, 2172, 2432, 2816, 2560, 892, 508, 252, 464, 640, 896, 256, 3244, 3200, 3840, 3584, 1964, 1068, 1324, 1872, 1920, 1664, 1280, 2556, 2940, 2684, 2256, 2688, 2944, 2304, 300, 124, 380, 1020, 80, 720, 976, 128, 3116, 4012, 3756, 3664, 3968, 3712, 3328, 1660, 1196, 1452, 1580, 2000, 1104, 1360, 1408, 2732, 2812, 3068, 2428, 2384, 3024, 2768, 2176, 172, 556, 812, 636, 848, 592, 208, 3324, 3884, 3628, 3500, 3792, 3408, 3152, 3456, 1788, 1404, 1148, 1708, 1232, 1488, 1616, 2860, 2476, 2220, 2300, 2640, 2896, 2512, 940, 684, 44, 336, 3196, 4092, 3836, 3372, 3536, 3280, 3920, 1532, 1276, 1916, 1744, 2092, 2348, 2988, 2128, 428, 3964, 3708, 3580, 4048, 2044, 2604, 3452] : Array ℕ).getD k.val 0)
private def next56_2 (k : Fin 128) (j : Fin 6) : Fin 128 :=
  Fin.ofNat 128 (((#[#[1, 0, 75, 1, 5, 18],
    #[2, 1, 90, 2, 10, 29],
    #[7, 2, 97, 7, 14, 36],
    #[87, 3, 6, 87, 17, 48],
    #[63, 4, 44, 63, 20, 43],
    #[10, 5, 43, 10, 0, 44],
    #[11, 6, 42, 11, 22, 3],
    #[0, 7, 108, 0, 25, 51],
    #[94, 8, 11, 94, 28, 63],
    #[71, 9, 59, 71, 31, 58],
    #[14, 10, 58, 14, 1, 59],
    #[15, 11, 57, 15, 33, 8],
    #[105, 12, 15, 105, 35, 71],
    #[86, 13, 67, 86, 38, 66],
    #[25, 14, 66, 25, 2, 67],
    #[26, 15, 65, 26, 40, 12],
    #[114, 16, 21, 114, 42, 22],
    #[112, 17, 22, 112, 3, 21],
    #[113, 18, 0, 113, 44, 20],
    #[92, 19, 72, 92, 46, 73],
    #[32, 20, 18, 32, 4, 75],
    #[31, 21, 17, 31, 48, 16],
    #[33, 22, 16, 33, 6, 17],
    #[72, 23, 26, 72, 50, 86],
    #[48, 24, 82, 48, 53, 81],
    #[5, 25, 81, 5, 7, 82],
    #[6, 26, 80, 6, 55, 23],
    #[118, 27, 32, 118, 57, 33],
    #[116, 28, 33, 116, 8, 32],
    #[117, 29, 1, 117, 59, 31],
    #[99, 30, 87, 99, 61, 88],
    #[39, 31, 29, 39, 9, 90],
    #[38, 32, 28, 38, 63, 27],
    #[40, 33, 27, 40, 11, 28],
    #[123, 34, 39, 123, 65, 40],
    #[121, 35, 40, 121, 12, 39],
    #[122, 36, 2, 122, 67, 38],
    #[110, 37, 94, 110, 69, 95],
    #[54, 38, 36, 54, 13, 97],
    #[53, 39, 35, 53, 71, 34],
    #[55, 40, 34, 55, 15, 35],
    #[29, 41, 46, 29, 73, 45],
    #[89, 42, 48, 89, 16, 6],
    #[88, 43, 4, 88, 75, 5],
    #[125, 44, 5, 125, 18, 4],
    #[61, 45, 41, 61, 76, 101],
    #[115, 46, 101, 115, 19, 41],
    #[60, 47, 102, 60, 78, 103],
    #[9, 48, 3, 9, 21, 42],
    #[103, 49, 54, 103, 80, 55],
    #[101, 50, 55, 101, 23, 54],
    #[102, 51, 7, 102, 82, 53],
    #[77, 52, 105, 77, 84, 106],
    #[21, 53, 51, 21, 24, 108],
    #[20, 54, 50, 20, 86, 49],
    #[22, 55, 49, 22, 26, 50],
    #[36, 56, 61, 36, 88, 60],
    #[96, 57, 63, 96, 27, 11],
    #[95, 58, 9, 95, 90, 10],
    #[126, 59, 10, 126, 29, 9],
    #[69, 60, 56, 69, 91, 112],
    #[119, 61, 112, 119, 30, 56],
    #[68, 62, 113, 68, 93, 114],
    #[13, 63, 8, 13, 32, 57],
    #[51, 64, 69, 51, 95, 68],
    #[107, 65, 71, 107, 34, 15],
    #[106, 66, 13, 106, 97, 14],
    #[127, 67, 14, 127, 36, 13],
    #[84, 68, 64, 84, 98, 116],
    #[124, 69, 116, 124, 37, 64],
    #[83, 70, 117, 83, 100, 118],
    #[24, 71, 12, 24, 39, 65],
    #[57, 72, 76, 57, 101, 19],
    #[59, 73, 19, 59, 41, 76],
    #[8, 74, 78, 8, 103, 77],
    #[56, 75, 20, 56, 43, 0],
    #[30, 76, 73, 30, 45, 72],
    #[93, 77, 74, 93, 104, 120],
    #[91, 78, 120, 91, 47, 74],
    #[18, 79, 84, 18, 106, 83],
    #[74, 80, 86, 74, 49, 26],
    #[73, 81, 24, 73, 108, 25],
    #[120, 82, 25, 120, 51, 24],
    #[46, 83, 79, 46, 109, 121],
    #[104, 84, 121, 104, 52, 79],
    #[45, 85, 122, 45, 111, 123],
    #[4, 86, 23, 4, 54, 80],
    #[65, 87, 91, 65, 112, 30],
    #[67, 88, 30, 67, 56, 91],
    #[12, 89, 93, 12, 114, 92],
    #[64, 90, 31, 64, 58, 1],
    #[37, 91, 88, 37, 60, 87],
    #[100, 92, 89, 100, 115, 125],
    #[98, 93, 125, 98, 62, 89],
    #[80, 94, 98, 80, 116, 37],
    #[82, 95, 37, 82, 64, 98],
    #[23, 96, 100, 23, 118, 99],
    #[79, 97, 38, 79, 66, 2],
    #[52, 98, 95, 52, 68, 94],
    #[111, 99, 96, 111, 119, 126],
    #[109, 100, 126, 109, 70, 96],
    #[27, 101, 45, 27, 72, 46],
    #[90, 102, 104, 90, 120, 47],
    #[28, 103, 47, 28, 74, 104],
    #[62, 104, 103, 62, 77, 102],
    #[42, 105, 109, 42, 121, 52],
    #[44, 106, 52, 44, 79, 109],
    #[3, 107, 111, 3, 123, 110],
    #[41, 108, 53, 41, 81, 7],
    #[19, 109, 106, 19, 83, 105],
    #[78, 110, 107, 78, 124, 127],
    #[76, 111, 127, 76, 85, 107],
    #[34, 112, 60, 34, 87, 61],
    #[97, 113, 115, 97, 125, 62],
    #[35, 114, 62, 35, 89, 115],
    #[70, 115, 114, 70, 92, 113],
    #[49, 116, 68, 49, 94, 69],
    #[108, 117, 119, 108, 126, 70],
    #[50, 118, 70, 50, 96, 119],
    #[85, 119, 118, 85, 99, 117],
    #[58, 120, 77, 58, 102, 78],
    #[16, 121, 83, 16, 105, 84],
    #[75, 122, 124, 75, 127, 85],
    #[17, 123, 85, 17, 107, 124],
    #[47, 124, 123, 47, 110, 122],
    #[66, 125, 92, 66, 113, 93],
    #[81, 126, 99, 81, 117, 100],
    #[43, 127, 110, 43, 122, 111]] : Array (Array ℕ)).getD k.val #[]).getD j.val 0)
private def prev56_2 (k : Fin 128) (j : Fin 6) : Fin 128 :=
  Fin.ofNat 128 (((#[#[7, 0, 18, 7, 5, 75],
    #[0, 1, 29, 0, 10, 90],
    #[1, 2, 36, 1, 14, 97],
    #[107, 3, 48, 107, 17, 6],
    #[86, 4, 43, 86, 20, 44],
    #[25, 5, 44, 25, 0, 43],
    #[26, 6, 3, 26, 22, 42],
    #[2, 7, 51, 2, 25, 108],
    #[74, 8, 63, 74, 28, 11],
    #[48, 9, 58, 48, 31, 59],
    #[5, 10, 59, 5, 1, 58],
    #[6, 11, 8, 6, 33, 57],
    #[89, 12, 71, 89, 35, 15],
    #[63, 13, 66, 63, 38, 67],
    #[10, 14, 67, 10, 2, 66],
    #[11, 15, 12, 11, 40, 65],
    #[121, 16, 22, 121, 42, 21],
    #[123, 17, 21, 123, 3, 22],
    #[79, 18, 20, 79, 44, 0],
    #[109, 19, 73, 109, 46, 72],
    #[54, 20, 75, 54, 4, 18],
    #[53, 21, 16, 53, 48, 17],
    #[55, 22, 17, 55, 6, 16],
    #[96, 23, 86, 96, 50, 26],
    #[71, 24, 81, 71, 53, 82],
    #[14, 25, 82, 14, 7, 81],
    #[15, 26, 23, 15, 55, 80],
    #[101, 27, 33, 101, 57, 32],
    #[103, 28, 32, 103, 8, 33],
    #[41, 29, 31, 41, 59, 1],
    #[76, 30, 88, 76, 61, 87],
    #[21, 31, 90, 21, 9, 29],
    #[20, 32, 27, 20, 63, 28],
    #[22, 33, 28, 22, 11, 27],
    #[112, 34, 40, 112, 65, 39],
    #[114, 35, 39, 114, 12, 40],
    #[56, 36, 38, 56, 67, 2],
    #[91, 37, 95, 91, 69, 94],
    #[32, 38, 97, 32, 13, 36],
    #[31, 39, 34, 31, 71, 35],
    #[33, 40, 35, 33, 15, 34],
    #[108, 41, 45, 108, 73, 46],
    #[105, 42, 6, 105, 16, 48],
    #[127, 43, 5, 127, 75, 4],
    #[106, 44, 4, 106, 18, 5],
    #[85, 45, 101, 85, 76, 41],
    #[83, 46, 41, 83, 19, 101],
    #[124, 47, 103, 124, 78, 102],
    #[24, 48, 42, 24, 21, 3],
    #[116, 49, 55, 116, 80, 54],
    #[118, 50, 54, 118, 23, 55],
    #[64, 51, 53, 64, 82, 7],
    #[98, 52, 106, 98, 84, 105],
    #[39, 53, 108, 39, 24, 51],
    #[38, 54, 49, 38, 86, 50],
    #[40, 55, 50, 40, 26, 49],
    #[75, 56, 60, 75, 88, 61],
    #[72, 57, 11, 72, 27, 63],
    #[120, 58, 10, 120, 90, 9],
    #[73, 59, 9, 73, 29, 10],
    #[47, 60, 112, 47, 91, 56],
    #[45, 61, 56, 45, 30, 112],
    #[104, 62, 114, 104, 93, 113],
    #[4, 63, 57, 4, 32, 8],
    #[90, 64, 68, 90, 95, 69],
    #[87, 65, 15, 87, 34, 71],
    #[125, 66, 14, 125, 97, 13],
    #[88, 67, 13, 88, 36, 14],
    #[62, 68, 116, 62, 98, 64],
    #[60, 69, 64, 60, 37, 116],
    #[115, 70, 118, 115, 100, 117],
    #[9, 71, 65, 9, 39, 12],
    #[23, 72, 19, 23, 101, 76],
    #[81, 73, 76, 81, 41, 19],
    #[80, 74, 77, 80, 103, 78],
    #[122, 75, 0, 122, 43, 20],
    #[111, 76, 72, 111, 45, 73],
    #[52, 77, 120, 52, 104, 74],
    #[110, 78, 74, 110, 47, 120],
    #[97, 79, 83, 97, 106, 84],
    #[94, 80, 26, 94, 49, 86],
    #[126, 81, 25, 126, 108, 24],
    #[95, 82, 24, 95, 51, 25],
    #[70, 83, 121, 70, 109, 79],
    #[68, 84, 79, 68, 52, 121],
    #[119, 85, 123, 119, 111, 122],
    #[13, 86, 80, 13, 54, 23],
    #[3, 87, 30, 3, 112, 91],
    #[43, 88, 91, 43, 56, 30],
    #[42, 89, 92, 42, 114, 93],
    #[102, 90, 1, 102, 58, 31],
    #[78, 91, 87, 78, 60, 88],
    #[19, 92, 125, 19, 115, 89],
    #[77, 93, 89, 77, 62, 125],
    #[8, 94, 37, 8, 116, 98],
    #[58, 95, 98, 58, 64, 37],
    #[57, 96, 99, 57, 118, 100],
    #[113, 97, 2, 113, 66, 38],
    #[93, 98, 94, 93, 68, 95],
    #[30, 99, 126, 30, 119, 96],
    #[92, 100, 96, 92, 70, 126],
    #[50, 101, 46, 50, 72, 45],
    #[51, 102, 47, 51, 120, 104],
    #[49, 103, 104, 49, 74, 47],
    #[84, 104, 102, 84, 77, 103],
    #[12, 105, 52, 12, 121, 109],
    #[66, 106, 109, 66, 79, 52],
    #[65, 107, 110, 65, 123, 111],
    #[117, 108, 7, 117, 81, 53],
    #[100, 109, 105, 100, 83, 106],
    #[37, 110, 127, 37, 124, 107],
    #[99, 111, 107, 99, 85, 127],
    #[17, 112, 61, 17, 87, 60],
    #[18, 113, 62, 18, 125, 115],
    #[16, 114, 115, 16, 89, 62],
    #[46, 115, 113, 46, 92, 114],
    #[28, 116, 69, 28, 94, 68],
    #[29, 117, 70, 29, 126, 119],
    #[27, 118, 119, 27, 96, 70],
    #[61, 119, 117, 61, 99, 118],
    #[82, 120, 78, 82, 102, 77],
    #[35, 121, 84, 35, 105, 83],
    #[36, 122, 85, 36, 127, 124],
    #[34, 123, 124, 34, 107, 85],
    #[69, 124, 122, 69, 110, 123],
    #[44, 125, 93, 44, 113, 92],
    #[59, 126, 100, 59, 117, 99],
    #[67, 127, 111, 67, 122, 110]] : Array (Array ℕ)).getD k.val #[]).getD j.val 0)
set_option maxHeartbeats 1600000 in
private theorem cert56_2 : ∃ c, c ∈ Subgroup.centralizer (Subgroup.closure (Set.range e56_2) : Set SylowModel) ∧ c ∉ Subgroup.closure (Set.range e56_2) := by
  refine ⟨rootOne ^ 2 * root 2 * root 4 * root 8, centralizes_generators e56_2 _ (by decide +kernel), ?_⟩
  exact outside_of_table e56_2 a56_2 0 next56_2 prev56_2
    (by decide +kernel) (by decide +kernel) (by decide +kernel) _ (by decide +kernel)

private def e56_3 : Fin 6 → SylowModel := ![decode 0, decode 3348, decode 636, decode 2048, decode 1300, decode 684]
set_option maxHeartbeats 1600000 in
private theorem edgeEq56_3 : binaryFamily s56 (s56 0) (![true, true, false]) = e56_3 := by decide +kernel
private def a56_3 (k : Fin 128) : SylowModel :=
  decode ((#[0, 2048, 764, 384, 768, 512, 2172, 2432, 2816, 2560, 892, 508, 252, 464, 640, 896, 256, 2556, 2940, 2684, 2256, 2688, 2944, 2304, 300, 124, 380, 1020, 80, 720, 976, 128, 2732, 2812, 3068, 2428, 2384, 3024, 2768, 2176, 172, 556, 812, 636, 848, 592, 208, 1172, 1988, 2860, 2476, 2220, 2300, 2640, 2896, 2512, 940, 684, 44, 336, 3220, 3780, 1976, 1768, 1044, 1940, 1684, 1860, 1220, 1476, 2092, 2348, 2988, 2128, 428, 3128, 3176, 3092, 3988, 3732, 3652, 3524, 3268, 1848, 1208, 1464, 1640, 1512, 1256, 1812, 1556, 1428, 1092, 1348, 1732, 2604, 3256, 3896, 3640, 3304, 3944, 3688, 3860, 3604, 3476, 3396, 3140, 4036, 1080, 1336, 1720, 1384, 1128, 2024, 1300, 1604, 4024, 3768, 3384, 4072, 3816, 3432, 3348, 3908, 1592, 1896, 3512, 3560] : Array ℕ).getD k.val 0)
private def next56_3 (k : Fin 128) (j : Fin 6) : Fin 128 :=
  Fin.ofNat 128 (((#[#[0, 122, 43, 1, 114, 57],
    #[1, 114, 52, 0, 122, 71],
    #[2, 101, 5, 33, 86, 46],
    #[3, 60, 27, 7, 47, 42],
    #[4, 103, 26, 8, 90, 74],
    #[5, 102, 25, 9, 89, 40],
    #[6, 88, 9, 25, 99, 55],
    #[7, 47, 35, 3, 60, 51],
    #[8, 90, 34, 4, 103, 95],
    #[9, 89, 33, 5, 102, 49],
    #[10, 119, 15, 18, 113, 59],
    #[11, 121, 16, 17, 111, 30],
    #[12, 76, 0, 52, 112, 29],
    #[13, 81, 40, 55, 69, 25],
    #[14, 78, 12, 21, 65, 58],
    #[15, 79, 11, 22, 66, 24],
    #[16, 77, 10, 23, 64, 56],
    #[17, 111, 22, 11, 121, 73],
    #[18, 113, 23, 10, 119, 38],
    #[19, 63, 1, 43, 120, 37],
    #[20, 68, 49, 46, 82, 33],
    #[21, 65, 19, 14, 78, 72],
    #[22, 66, 18, 15, 79, 32],
    #[23, 64, 17, 16, 77, 70],
    #[24, 96, 29, 71, 84, 0],
    #[25, 99, 31, 6, 88, 45],
    #[26, 127, 3, 35, 87, 44],
    #[27, 100, 4, 34, 125, 13],
    #[28, 106, 24, 73, 92, 11],
    #[29, 61, 56, 38, 94, 10],
    #[30, 107, 57, 37, 48, 43],
    #[31, 104, 2, 39, 91, 41],
    #[32, 83, 37, 57, 97, 1],
    #[33, 86, 39, 2, 101, 54],
    #[34, 125, 7, 27, 100, 53],
    #[35, 87, 8, 26, 127, 20],
    #[36, 93, 32, 59, 105, 18],
    #[37, 48, 70, 30, 107, 17],
    #[38, 94, 71, 29, 61, 52],
    #[39, 91, 6, 31, 104, 50],
    #[40, 118, 44, 51, 109, 3],
    #[41, 116, 13, 95, 62, 4],
    #[42, 117, 46, 49, 110, 5],
    #[43, 120, 14, 19, 63, 28],
    #[44, 123, 41, 54, 67, 2],
    #[45, 80, 42, 53, 115, 27],
    #[46, 82, 74, 20, 68, 26],
    #[47, 14, 109, 60, 21, 125],
    #[48, 46, 111, 107, 20, 83],
    #[49, 110, 53, 42, 117, 7],
    #[50, 108, 20, 74, 75, 8],
    #[51, 109, 55, 40, 118, 9],
    #[52, 112, 21, 12, 76, 36],
    #[53, 115, 50, 45, 80, 6],
    #[54, 67, 51, 44, 123, 35],
    #[55, 69, 95, 13, 81, 34],
    #[56, 98, 28, 72, 124, 14],
    #[57, 97, 59, 32, 83, 15],
    #[58, 126, 30, 70, 85, 16],
    #[59, 105, 58, 36, 93, 12],
    #[60, 21, 117, 47, 14, 127],
    #[61, 55, 119, 94, 13, 96],
    #[62, 24, 91, 116, 71, 69],
    #[63, 26, 48, 120, 35, 65],
    #[64, 5, 85, 77, 9, 113],
    #[65, 3, 124, 78, 7, 112],
    #[66, 31, 83, 79, 39, 111],
    #[67, 28, 87, 123, 73, 62],
    #[68, 30, 86, 82, 37, 108],
    #[69, 29, 125, 81, 38, 109],
    #[70, 85, 36, 58, 126, 21],
    #[71, 84, 73, 24, 96, 22],
    #[72, 124, 38, 56, 98, 23],
    #[73, 92, 72, 28, 106, 19],
    #[74, 75, 45, 50, 108, 31],
    #[75, 32, 104, 108, 57, 82],
    #[76, 34, 61, 112, 27, 78],
    #[77, 9, 98, 64, 5, 121],
    #[78, 7, 126, 65, 3, 120],
    #[79, 39, 96, 66, 31, 119],
    #[80, 36, 100, 115, 59, 75],
    #[81, 38, 99, 69, 29, 116],
    #[82, 37, 127, 68, 30, 117],
    #[83, 74, 114, 97, 50, 93],
    #[84, 41, 66, 96, 95, 94],
    #[85, 42, 65, 126, 49, 48],
    #[86, 11, 67, 101, 17, 89],
    #[87, 43, 68, 127, 19, 47],
    #[88, 10, 69, 99, 18, 91],
    #[89, 16, 110, 102, 23, 88],
    #[90, 0, 62, 103, 1, 87],
    #[91, 15, 108, 104, 22, 86],
    #[92, 44, 63, 106, 54, 84],
    #[93, 45, 113, 105, 53, 85],
    #[94, 13, 112, 61, 55, 124],
    #[95, 62, 54, 41, 116, 39],
    #[96, 95, 122, 84, 41, 106],
    #[97, 50, 79, 83, 74, 107],
    #[98, 51, 78, 124, 40, 61],
    #[99, 18, 80, 88, 10, 102],
    #[100, 52, 81, 125, 12, 60],
    #[101, 17, 82, 86, 11, 104],
    #[102, 23, 118, 89, 16, 101],
    #[103, 1, 75, 90, 0, 100],
    #[104, 22, 116, 91, 15, 99],
    #[105, 53, 76, 93, 45, 97],
    #[106, 54, 121, 92, 44, 98],
    #[107, 20, 120, 48, 46, 126],
    #[108, 57, 90, 75, 32, 115],
    #[109, 56, 89, 118, 72, 67],
    #[110, 58, 47, 117, 70, 68],
    #[111, 2, 92, 121, 33, 64],
    #[112, 27, 93, 76, 34, 114],
    #[113, 25, 94, 119, 6, 66],
    #[114, 4, 84, 122, 8, 63],
    #[115, 59, 88, 80, 36, 110],
    #[116, 71, 103, 62, 24, 123],
    #[117, 70, 102, 110, 58, 80],
    #[118, 72, 60, 109, 56, 81],
    #[119, 6, 105, 113, 25, 77],
    #[120, 35, 106, 63, 26, 122],
    #[121, 33, 107, 111, 2, 79],
    #[122, 8, 97, 114, 4, 76],
    #[123, 73, 101, 67, 28, 118],
    #[124, 40, 64, 98, 51, 92],
    #[125, 12, 115, 100, 52, 90],
    #[126, 49, 77, 85, 42, 105],
    #[127, 19, 123, 87, 43, 103]] : Array (Array ℕ)).getD k.val #[]).getD j.val 0)
private def prev56_3 (k : Fin 128) (j : Fin 6) : Fin 128 :=
  Fin.ofNat 128 (((#[#[0, 90, 12, 1, 103, 24],
    #[1, 103, 19, 0, 90, 32],
    #[2, 111, 31, 33, 121, 44],
    #[3, 65, 26, 7, 78, 40],
    #[4, 114, 27, 8, 122, 41],
    #[5, 64, 2, 9, 77, 42],
    #[6, 119, 39, 25, 113, 53],
    #[7, 78, 34, 3, 65, 49],
    #[8, 122, 35, 4, 114, 50],
    #[9, 77, 6, 5, 64, 51],
    #[10, 88, 16, 18, 99, 29],
    #[11, 86, 15, 17, 101, 28],
    #[12, 125, 14, 52, 100, 59],
    #[13, 94, 41, 55, 61, 27],
    #[14, 47, 43, 21, 60, 56],
    #[15, 91, 10, 22, 104, 57],
    #[16, 89, 11, 23, 102, 58],
    #[17, 101, 23, 11, 86, 37],
    #[18, 99, 22, 10, 88, 36],
    #[19, 127, 21, 43, 87, 73],
    #[20, 107, 50, 46, 48, 35],
    #[21, 60, 52, 14, 47, 70],
    #[22, 104, 17, 15, 91, 71],
    #[23, 102, 18, 16, 89, 72],
    #[24, 62, 28, 71, 116, 15],
    #[25, 113, 5, 6, 119, 13],
    #[26, 63, 4, 35, 120, 46],
    #[27, 112, 3, 34, 76, 45],
    #[28, 67, 56, 73, 123, 43],
    #[29, 69, 24, 38, 81, 12],
    #[30, 68, 58, 37, 82, 11],
    #[31, 66, 25, 39, 79, 74],
    #[32, 75, 36, 57, 108, 22],
    #[33, 121, 9, 2, 111, 20],
    #[34, 76, 8, 27, 112, 55],
    #[35, 120, 7, 26, 63, 54],
    #[36, 80, 70, 59, 115, 52],
    #[37, 82, 32, 30, 68, 19],
    #[38, 81, 72, 29, 69, 18],
    #[39, 79, 33, 31, 66, 95],
    #[40, 124, 13, 51, 98, 5],
    #[41, 84, 44, 95, 96, 31],
    #[42, 85, 45, 49, 126, 3],
    #[43, 87, 0, 19, 127, 30],
    #[44, 92, 40, 54, 106, 26],
    #[45, 93, 74, 53, 105, 25],
    #[46, 48, 42, 20, 107, 2],
    #[47, 7, 110, 60, 3, 87],
    #[48, 37, 63, 107, 30, 85],
    #[49, 126, 20, 42, 85, 9],
    #[50, 97, 53, 74, 83, 39],
    #[51, 98, 54, 40, 124, 7],
    #[52, 100, 1, 12, 125, 38],
    #[53, 105, 49, 45, 93, 34],
    #[54, 106, 95, 44, 92, 33],
    #[55, 61, 51, 13, 94, 6],
    #[56, 109, 29, 72, 118, 16],
    #[57, 108, 30, 32, 75, 0],
    #[58, 110, 59, 70, 117, 14],
    #[59, 115, 57, 36, 80, 10],
    #[60, 3, 118, 47, 7, 100],
    #[61, 29, 76, 94, 38, 98],
    #[62, 95, 90, 116, 41, 67],
    #[63, 19, 92, 120, 43, 114],
    #[64, 23, 124, 77, 16, 111],
    #[65, 21, 85, 78, 14, 63],
    #[66, 22, 84, 79, 15, 113],
    #[67, 54, 86, 123, 44, 109],
    #[68, 20, 87, 82, 46, 110],
    #[69, 55, 88, 81, 13, 62],
    #[70, 117, 37, 58, 110, 23],
    #[71, 116, 38, 24, 62, 1],
    #[72, 118, 73, 56, 109, 21],
    #[73, 123, 71, 28, 67, 17],
    #[74, 83, 46, 50, 97, 4],
    #[75, 74, 103, 108, 50, 80],
    #[76, 12, 105, 112, 52, 122],
    #[77, 16, 126, 64, 23, 119],
    #[78, 14, 98, 65, 21, 76],
    #[79, 15, 97, 66, 22, 121],
    #[80, 45, 99, 115, 53, 117],
    #[81, 13, 100, 69, 55, 118],
    #[82, 46, 101, 68, 20, 75],
    #[83, 32, 66, 97, 57, 48],
    #[84, 71, 114, 96, 24, 92],
    #[85, 70, 64, 126, 58, 93],
    #[86, 33, 68, 101, 2, 91],
    #[87, 35, 67, 127, 26, 90],
    #[88, 6, 115, 99, 25, 89],
    #[89, 9, 109, 102, 5, 86],
    #[90, 8, 108, 103, 4, 125],
    #[91, 39, 62, 104, 31, 88],
    #[92, 73, 111, 106, 28, 124],
    #[93, 36, 112, 105, 59, 83],
    #[94, 38, 113, 61, 29, 84],
    #[95, 96, 55, 41, 84, 8],
    #[96, 24, 79, 84, 71, 61],
    #[97, 57, 122, 83, 32, 105],
    #[98, 56, 77, 124, 72, 106],
    #[99, 25, 81, 88, 6, 104],
    #[100, 27, 80, 125, 34, 103],
    #[101, 2, 123, 86, 33, 102],
    #[102, 5, 117, 89, 9, 99],
    #[103, 4, 116, 90, 8, 127],
    #[104, 31, 75, 91, 39, 101],
    #[105, 59, 119, 93, 36, 126],
    #[106, 28, 120, 92, 73, 96],
    #[107, 30, 121, 48, 37, 97],
    #[108, 50, 91, 75, 74, 68],
    #[109, 51, 47, 118, 40, 69],
    #[110, 49, 89, 117, 42, 115],
    #[111, 17, 48, 121, 11, 66],
    #[112, 52, 94, 76, 12, 65],
    #[113, 18, 93, 119, 10, 64],
    #[114, 1, 83, 122, 0, 112],
    #[115, 53, 125, 80, 45, 108],
    #[116, 41, 104, 62, 95, 81],
    #[117, 42, 60, 110, 49, 82],
    #[118, 40, 102, 109, 51, 123],
    #[119, 10, 61, 113, 18, 79],
    #[120, 43, 107, 63, 19, 78],
    #[121, 11, 106, 111, 17, 77],
    #[122, 0, 96, 114, 1, 120],
    #[123, 44, 127, 67, 54, 116],
    #[124, 72, 65, 98, 56, 94],
    #[125, 34, 69, 100, 27, 47],
    #[126, 58, 78, 85, 70, 107],
    #[127, 26, 82, 87, 35, 60]] : Array (Array ℕ)).getD k.val #[]).getD j.val 0)
set_option maxHeartbeats 1600000 in
private theorem cert56_3 : ∃ c, c ∈ Subgroup.centralizer (Subgroup.closure (Set.range e56_3) : Set SylowModel) ∧ c ∉ Subgroup.closure (Set.range e56_3) := by
  refine ⟨rootOne ^ 2 * root 2 * root 4 * root 8, centralizes_generators e56_3 _ (by decide +kernel), ?_⟩
  exact outside_of_table e56_3 a56_3 0 next56_3 prev56_3
    (by decide +kernel) (by decide +kernel) (by decide +kernel) _ (by decide +kernel)

private def e56_4 : Fin 6 → SylowModel := ![decode 1024, decode 276, decode 0, decode 2000, decode 916, decode 640]
set_option maxHeartbeats 1600000 in
private theorem edgeEq56_4 : binaryFamily s56 (s56 2) (![false, false, true]) = e56_4 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert56_4 : Represented smallParityCensusNode (Subgroup.closure (Set.range e56_4)) := by
  refine ⟨84, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node84]
  exact closure_eq_words _ o84 (![[1], [0], [], [0, 2, 0, 1], [0, 4, 6], [4, 6]]) (![[1], [0], [0, 0, 0, 3, 1, 4], [0, 0], [0, 3, 3, 0], [1, 1], [0, 3, 0, 3]]) (by decide +kernel) (by decide +kernel)

private def e56_5 : Fin 6 → SylowModel := ![decode 0, decode 276, decode 3708, decode 2048, decode 276, decode 1708]
set_option maxHeartbeats 1600000 in
private theorem edgeEq56_5 : binaryFamily s56 (s56 0) (![true, false, true]) = e56_5 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert56_5 : Represented smallParityCensusNode (Subgroup.closure (Set.range e56_5)) := by
  refine ⟨94, root 1 * root 2 * root 4 * root 5 * root 7 * root 9, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node94]
  exact closure_eq_words _ o94 (![[], [2, 0, 5], [1, 3, 2, 4], [2, 3], [2, 0, 5], [2, 1, 5]]) (![[1, 1, 1, 2, 3, 2], [1, 1, 3, 2], [5, 3, 5], [2, 2, 2, 5], [1, 1, 2, 5], [1, 1], [2, 2, 2, 2]]) (by decide +kernel) (by decide +kernel)

private def e56_6 : Fin 6 → SylowModel := ![decode 1024, decode 0, decode 488, decode 1024, decode 768, decode 104]
set_option maxHeartbeats 1600000 in
private theorem edgeEq56_6 : binaryFamily s56 (s56 1) (![false, true, true]) = e56_6 := by decide +kernel
private def a56_6 (k : Fin 128) : SylowModel :=
  decode ((#[0, 1024, 2048, 384, 768, 512, 3072, 1152, 1792, 1536, 2432, 2816, 2560, 464, 640, 896, 256, 3200, 3840, 3584, 1872, 1920, 1664, 1280, 2256, 2688, 2944, 2304, 80, 720, 976, 128, 232, 3664, 3968, 3712, 3328, 2000, 1104, 1360, 1408, 2384, 3024, 2768, 2176, 848, 592, 208, 2664, 360, 1000, 744, 3792, 3408, 3152, 3456, 1232, 1488, 1616, 2640, 2896, 2512, 336, 1976, 1768, 3048, 2408, 2152, 824, 616, 872, 488, 3536, 3280, 3920, 1744, 2128, 3128, 3176, 1848, 1208, 1464, 1640, 1512, 1256, 2232, 2280, 2536, 2920, 696, 56, 312, 104, 4048, 3256, 3896, 3640, 3304, 3944, 3688, 1080, 1336, 1720, 1384, 1128, 2024, 2360, 3000, 2744, 2792, 440, 184, 568, 4024, 3768, 3384, 4072, 3816, 3432, 1592, 1896, 2616, 2872, 2488, 952, 3512, 3560, 2104] : Array ℕ).getD k.val 0)
private def next56_6 (k : Fin 128) (j : Fin 6) : Fin 128 :=
  Fin.ofNat 128 (((#[#[1, 0, 71, 1, 4, 92],
    #[2, 1, 100, 2, 8, 80],
    #[6, 2, 88, 6, 11, 109],
    #[40, 3, 92, 40, 14, 71],
    #[8, 4, 51, 8, 0, 70],
    #[9, 5, 50, 9, 16, 69],
    #[0, 6, 113, 0, 18, 95],
    #[44, 7, 80, 44, 21, 100],
    #[11, 8, 79, 11, 1, 63],
    #[12, 9, 119, 12, 23, 102],
    #[55, 10, 109, 55, 25, 88],
    #[18, 11, 67, 18, 2, 87],
    #[19, 12, 66, 19, 27, 86],
    #[57, 13, 112, 57, 29, 124],
    #[22, 14, 70, 22, 3, 51],
    #[21, 15, 69, 21, 31, 50],
    #[23, 16, 32, 23, 5, 49],
    #[31, 17, 95, 31, 34, 113],
    #[4, 18, 94, 4, 6, 77],
    #[5, 19, 125, 5, 36, 115],
    #[60, 20, 103, 60, 38, 83],
    #[26, 21, 63, 26, 7, 79],
    #[25, 22, 102, 25, 40, 119],
    #[27, 23, 101, 27, 9, 81],
    #[73, 24, 123, 73, 42, 127],
    #[35, 25, 87, 35, 10, 67],
    #[34, 26, 86, 34, 44, 66],
    #[36, 27, 48, 36, 12, 65],
    #[38, 28, 124, 38, 45, 112],
    #[75, 29, 91, 75, 13, 111],
    #[37, 30, 90, 37, 47, 110],
    #[7, 31, 49, 7, 15, 32],
    #[84, 32, 5, 84, 50, 15],
    #[46, 33, 116, 46, 53, 98],
    #[15, 34, 77, 15, 17, 94],
    #[14, 35, 115, 14, 55, 125],
    #[16, 36, 114, 16, 19, 96],
    #[42, 37, 83, 42, 56, 103],
    #[76, 38, 82, 76, 20, 64],
    #[41, 39, 120, 41, 58, 105],
    #[10, 40, 81, 10, 22, 101],
    #[53, 41, 127, 53, 59, 123],
    #[93, 42, 108, 93, 24, 122],
    #[52, 43, 107, 52, 61, 121],
    #[17, 44, 65, 17, 26, 48],
    #[20, 45, 111, 20, 28, 91],
    #[58, 46, 110, 58, 62, 90],
    #[56, 47, 68, 56, 30, 89],
    #[99, 48, 12, 99, 66, 26],
    #[103, 49, 15, 103, 69, 5],
    #[105, 50, 16, 105, 32, 31],
    #[64, 51, 0, 64, 71, 3],
    #[29, 52, 98, 29, 72, 116],
    #[62, 53, 97, 62, 33, 78],
    #[28, 54, 126, 28, 74, 118],
    #[3, 55, 96, 3, 35, 114],
    #[24, 56, 64, 24, 37, 82],
    #[61, 57, 105, 61, 75, 120],
    #[59, 58, 104, 59, 39, 84],
    #[33, 59, 122, 33, 41, 108],
    #[74, 60, 121, 74, 76, 107],
    #[72, 61, 85, 72, 43, 106],
    #[39, 62, 89, 39, 46, 68],
    #[107, 63, 7, 107, 80, 1],
    #[109, 64, 37, 109, 83, 20],
    #[116, 65, 26, 116, 86, 12],
    #[118, 66, 27, 118, 48, 44],
    #[78, 67, 2, 78, 88, 10],
    #[79, 68, 30, 79, 90, 46],
    #[82, 69, 31, 82, 49, 16],
    #[120, 70, 3, 120, 92, 0],
    #[83, 71, 4, 83, 51, 14],
    #[13, 72, 78, 13, 52, 97],
    #[47, 73, 118, 47, 93, 126],
    #[45, 74, 117, 45, 54, 99],
    #[43, 75, 84, 43, 57, 104],
    #[54, 76, 106, 54, 60, 85],
    #[90, 77, 17, 90, 95, 6],
    #[92, 78, 52, 92, 98, 33],
    #[122, 79, 1, 122, 100, 7],
    #[85, 80, 21, 85, 63, 8],
    #[123, 81, 22, 123, 102, 9],
    #[48, 82, 20, 48, 103, 37],
    #[87, 83, 56, 87, 64, 38],
    #[86, 84, 57, 86, 105, 39],
    #[94, 85, 43, 94, 107, 60],
    #[97, 86, 44, 97, 65, 27],
    #[126, 87, 10, 126, 109, 2],
    #[98, 88, 11, 98, 67, 25],
    #[102, 89, 46, 102, 110, 30],
    #[100, 90, 47, 100, 68, 62],
    #[101, 91, 13, 101, 112, 28],
    #[104, 92, 14, 104, 70, 4],
    #[30, 93, 99, 30, 73, 117],
    #[111, 94, 6, 111, 113, 17],
    #[68, 95, 34, 68, 77, 18],
    #[112, 96, 35, 112, 115, 19],
    #[32, 97, 33, 32, 116, 52],
    #[70, 98, 72, 70, 78, 53],
    #[69, 99, 73, 69, 118, 54],
    #[127, 100, 8, 127, 79, 21],
    #[106, 101, 9, 106, 119, 22],
    #[108, 102, 40, 108, 81, 23],
    #[66, 103, 38, 66, 82, 56],
    #[67, 104, 39, 67, 120, 57],
    #[65, 105, 75, 65, 84, 58],
    #[115, 106, 60, 115, 121, 43],
    #[113, 107, 61, 113, 85, 76],
    #[114, 108, 24, 114, 123, 41],
    #[117, 109, 25, 117, 87, 11],
    #[81, 110, 62, 81, 89, 47],
    #[80, 111, 28, 80, 124, 13],
    #[119, 112, 29, 119, 91, 45],
    #[124, 113, 18, 124, 94, 34],
    #[89, 114, 19, 89, 125, 35],
    #[91, 115, 55, 91, 96, 36],
    #[50, 116, 53, 50, 97, 72],
    #[51, 117, 54, 51, 126, 73],
    #[49, 118, 93, 49, 99, 74],
    #[121, 119, 23, 121, 101, 40],
    #[88, 120, 58, 88, 104, 75],
    #[96, 121, 76, 96, 106, 61],
    #[95, 122, 41, 95, 127, 24],
    #[125, 123, 42, 125, 108, 59],
    #[63, 124, 45, 63, 111, 29],
    #[110, 125, 36, 110, 114, 55],
    #[71, 126, 74, 71, 117, 93],
    #[77, 127, 59, 77, 122, 42]] : Array (Array ℕ)).getD k.val #[]).getD j.val 0)
private def prev56_6 (k : Fin 128) (j : Fin 6) : Fin 128 :=
  Fin.ofNat 128 (((#[#[6, 0, 51, 6, 4, 70],
    #[0, 1, 79, 0, 8, 63],
    #[1, 2, 67, 1, 11, 87],
    #[55, 3, 70, 55, 14, 51],
    #[18, 4, 71, 18, 0, 92],
    #[19, 5, 32, 19, 16, 49],
    #[2, 6, 94, 2, 18, 77],
    #[31, 7, 63, 31, 21, 79],
    #[4, 8, 100, 4, 1, 80],
    #[5, 9, 101, 5, 23, 81],
    #[40, 10, 87, 40, 25, 67],
    #[8, 11, 88, 8, 2, 109],
    #[9, 12, 48, 9, 27, 65],
    #[72, 13, 91, 72, 29, 111],
    #[35, 14, 92, 35, 3, 71],
    #[34, 15, 49, 34, 31, 32],
    #[36, 16, 50, 36, 5, 69],
    #[44, 17, 77, 44, 34, 94],
    #[11, 18, 113, 11, 6, 95],
    #[12, 19, 114, 12, 36, 96],
    #[45, 20, 82, 45, 38, 64],
    #[15, 21, 80, 15, 7, 100],
    #[14, 22, 81, 14, 40, 101],
    #[16, 23, 119, 16, 9, 102],
    #[56, 24, 108, 56, 42, 122],
    #[22, 25, 109, 22, 10, 88],
    #[21, 26, 65, 21, 44, 48],
    #[23, 27, 66, 23, 12, 86],
    #[54, 28, 111, 54, 45, 91],
    #[52, 29, 112, 52, 13, 124],
    #[93, 30, 68, 93, 47, 89],
    #[17, 31, 69, 17, 15, 50],
    #[97, 32, 16, 97, 50, 31],
    #[59, 33, 97, 59, 53, 78],
    #[26, 34, 95, 26, 17, 113],
    #[25, 35, 96, 25, 55, 114],
    #[27, 36, 125, 27, 19, 115],
    #[30, 37, 64, 30, 56, 82],
    #[28, 38, 103, 28, 20, 83],
    #[62, 39, 104, 62, 58, 84],
    #[3, 40, 102, 3, 22, 119],
    #[39, 41, 122, 39, 59, 108],
    #[37, 42, 123, 37, 24, 127],
    #[75, 43, 85, 75, 61, 106],
    #[7, 44, 86, 7, 26, 66],
    #[74, 45, 124, 74, 28, 112],
    #[33, 46, 89, 33, 62, 68],
    #[73, 47, 90, 73, 30, 110],
    #[82, 48, 27, 82, 66, 44],
    #[118, 49, 31, 118, 69, 16],
    #[116, 50, 5, 116, 32, 15],
    #[117, 51, 4, 117, 71, 14],
    #[43, 52, 78, 43, 72, 97],
    #[41, 53, 116, 41, 33, 98],
    #[76, 54, 117, 76, 74, 99],
    #[10, 55, 115, 10, 35, 125],
    #[47, 56, 83, 47, 37, 103],
    #[13, 57, 84, 13, 75, 104],
    #[46, 58, 120, 46, 39, 105],
    #[58, 59, 127, 58, 41, 123],
    #[20, 60, 106, 20, 76, 85],
    #[57, 61, 107, 57, 43, 121],
    #[53, 62, 110, 53, 46, 90],
    #[124, 63, 21, 124, 80, 8],
    #[51, 64, 56, 51, 83, 38],
    #[105, 65, 44, 105, 86, 27],
    #[103, 66, 12, 103, 48, 26],
    #[104, 67, 11, 104, 88, 25],
    #[95, 68, 47, 95, 90, 62],
    #[99, 69, 15, 99, 49, 5],
    #[98, 70, 14, 98, 92, 4],
    #[126, 71, 0, 126, 51, 3],
    #[61, 72, 98, 61, 52, 116],
    #[24, 73, 99, 24, 93, 117],
    #[60, 74, 126, 60, 54, 118],
    #[29, 75, 105, 29, 57, 120],
    #[38, 76, 121, 38, 60, 107],
    #[127, 77, 34, 127, 95, 18],
    #[67, 78, 72, 67, 98, 53],
    #[68, 79, 8, 68, 100, 21],
    #[111, 80, 7, 111, 63, 1],
    #[110, 81, 40, 110, 102, 23],
    #[69, 82, 38, 69, 103, 56],
    #[71, 83, 37, 71, 64, 20],
    #[32, 84, 75, 32, 105, 58],
    #[80, 85, 61, 80, 107, 76],
    #[84, 86, 26, 84, 65, 12],
    #[83, 87, 25, 83, 109, 11],
    #[120, 88, 2, 120, 67, 10],
    #[114, 89, 62, 114, 110, 47],
    #[77, 90, 30, 77, 68, 46],
    #[115, 91, 29, 115, 112, 45],
    #[78, 92, 3, 78, 70, 0],
    #[42, 93, 118, 42, 73, 126],
    #[85, 94, 18, 85, 113, 34],
    #[122, 95, 17, 122, 77, 6],
    #[121, 96, 55, 121, 115, 36],
    #[86, 97, 53, 86, 116, 72],
    #[88, 98, 52, 88, 78, 33],
    #[48, 99, 93, 48, 118, 74],
    #[90, 100, 1, 90, 79, 7],
    #[91, 101, 23, 91, 119, 40],
    #[89, 102, 22, 89, 81, 9],
    #[49, 103, 20, 49, 82, 37],
    #[92, 104, 58, 92, 120, 75],
    #[50, 105, 57, 50, 84, 39],
    #[101, 106, 76, 101, 121, 61],
    #[63, 107, 43, 63, 85, 60],
    #[102, 108, 42, 102, 123, 59],
    #[64, 109, 10, 64, 87, 2],
    #[125, 110, 46, 125, 89, 30],
    #[94, 111, 45, 94, 124, 29],
    #[96, 112, 13, 96, 91, 28],
    #[107, 113, 6, 107, 94, 17],
    #[108, 114, 36, 108, 125, 55],
    #[106, 115, 35, 106, 96, 19],
    #[65, 116, 33, 65, 97, 52],
    #[109, 117, 74, 109, 126, 93],
    #[66, 118, 73, 66, 99, 54],
    #[112, 119, 9, 112, 101, 22],
    #[70, 120, 39, 70, 104, 57],
    #[119, 121, 60, 119, 106, 43],
    #[79, 122, 59, 79, 127, 42],
    #[81, 123, 24, 81, 108, 41],
    #[113, 124, 28, 113, 111, 13],
    #[123, 125, 19, 123, 114, 35],
    #[87, 126, 54, 87, 117, 73],
    #[100, 127, 41, 100, 122, 24]] : Array (Array ℕ)).getD k.val #[]).getD j.val 0)
set_option maxHeartbeats 1600000 in
private theorem cert56_6 : ∃ c, c ∈ Subgroup.centralizer (Subgroup.closure (Set.range e56_6) : Set SylowModel) ∧ c ∉ Subgroup.closure (Set.range e56_6) := by
  refine ⟨rootOne ^ 2 * root 2 * root 4 * root 8, centralizes_generators e56_6 _ (by decide +kernel), ?_⟩
  exact outside_of_table e56_6 a56_6 0 next56_6 prev56_6
    (by decide +kernel) (by decide +kernel) (by decide +kernel) _ (by decide +kernel)

private def e56_7 : Fin 6 → SylowModel := ![decode 0, decode 3348, decode 3708, decode 2048, decode 1300, decode 1708]
set_option maxHeartbeats 1600000 in
private theorem edgeEq56_7 : binaryFamily s56 (s56 0) (![true, true, true]) = e56_7 := by decide +kernel
private def a56_7 (k : Fin 128) : SylowModel :=
  decode ((#[0, 2048, 384, 768, 512, 1836, 2432, 2816, 2560, 464, 640, 896, 256, 3244, 1964, 1068, 1324, 2256, 2688, 2944, 2304, 80, 720, 976, 128, 232, 3116, 4012, 3756, 1660, 1196, 1452, 1580, 2384, 3024, 2768, 2176, 848, 592, 208, 1172, 1988, 2664, 360, 1000, 744, 3324, 3884, 3628, 3500, 1788, 1404, 1148, 1708, 2640, 2896, 2512, 336, 3220, 3780, 1044, 1940, 1684, 1860, 1220, 1476, 3048, 2408, 2152, 824, 616, 872, 488, 3196, 4092, 3836, 3372, 1532, 1276, 1916, 2128, 3092, 3988, 3732, 3652, 3524, 3268, 1812, 1556, 1428, 1092, 1348, 1732, 2232, 2280, 2536, 2920, 696, 56, 312, 104, 3964, 3708, 3580, 2044, 3860, 3604, 3476, 3396, 3140, 4036, 1300, 1604, 2360, 3000, 2744, 2792, 440, 184, 568, 3452, 3348, 3908, 2616, 2872, 2488, 952, 2104] : Array ℕ).getD k.val 0)
private def next56_7 (k : Fin 128) (j : Fin 6) : Fin 128 :=
  Fin.ofNat 128 (((#[#[0, 121, 102, 1, 111, 53],
    #[1, 111, 78, 0, 121, 76],
    #[2, 58, 74, 6, 40, 5],
    #[3, 106, 120, 7, 88, 31],
    #[4, 105, 73, 8, 87, 30],
    #[5, 97, 4, 47, 115, 54],
    #[6, 40, 51, 2, 58, 13],
    #[7, 88, 104, 3, 106, 48],
    #[8, 87, 50, 4, 105, 47],
    #[9, 85, 13, 56, 65, 52],
    #[10, 82, 46, 18, 61, 15],
    #[11, 83, 103, 19, 62, 16],
    #[12, 81, 101, 20, 60, 14],
    #[13, 113, 8, 30, 99, 37],
    #[14, 119, 10, 27, 123, 35],
    #[15, 117, 12, 26, 125, 33],
    #[16, 118, 0, 76, 93, 80],
    #[17, 64, 5, 39, 86, 75],
    #[18, 61, 29, 10, 82, 27],
    #[19, 62, 79, 11, 83, 28],
    #[20, 60, 77, 12, 81, 26],
    #[21, 109, 76, 80, 90, 77],
    #[22, 59, 27, 35, 92, 79],
    #[23, 110, 28, 34, 41, 29],
    #[24, 107, 75, 36, 89, 32],
    #[25, 101, 105, 94, 79, 65],
    #[26, 125, 18, 15, 117, 23],
    #[27, 123, 20, 14, 119, 21],
    #[28, 124, 1, 53, 69, 57],
    #[29, 45, 21, 102, 116, 1],
    #[30, 99, 2, 13, 113, 56],
    #[31, 98, 24, 49, 127, 17],
    #[32, 126, 3, 48, 114, 55],
    #[33, 91, 53, 57, 108, 101],
    #[34, 41, 15, 23, 110, 103],
    #[35, 92, 16, 22, 59, 46],
    #[36, 89, 52, 24, 107, 49],
    #[37, 122, 48, 55, 63, 50],
    #[38, 84, 47, 54, 112, 104],
    #[39, 86, 49, 17, 64, 51],
    #[40, 10, 99, 58, 18, 96],
    #[41, 39, 43, 110, 17, 124],
    #[42, 77, 87, 70, 103, 86],
    #[43, 75, 83, 67, 50, 90],
    #[44, 73, 81, 66, 52, 92],
    #[45, 120, 121, 116, 51, 41],
    #[46, 68, 33, 78, 100, 0],
    #[47, 115, 6, 5, 97, 39],
    #[48, 114, 36, 32, 126, 9],
    #[49, 127, 7, 31, 98, 38],
    #[50, 70, 39, 75, 42, 36],
    #[51, 72, 37, 120, 95, 7],
    #[52, 25, 38, 73, 94, 8],
    #[53, 69, 11, 28, 124, 34],
    #[54, 112, 31, 38, 84, 73],
    #[55, 63, 30, 37, 122, 120],
    #[56, 65, 32, 9, 85, 74],
    #[57, 108, 26, 33, 91, 78],
    #[58, 18, 115, 40, 10, 72],
    #[59, 56, 66, 92, 9, 118],
    #[60, 4, 117, 81, 8, 66],
    #[61, 2, 119, 82, 6, 68],
    #[62, 24, 69, 83, 36, 67],
    #[63, 21, 72, 122, 80, 114],
    #[64, 23, 70, 86, 34, 127],
    #[65, 22, 71, 85, 35, 113],
    #[66, 52, 62, 44, 73, 108],
    #[67, 50, 60, 43, 75, 110],
    #[68, 104, 111, 100, 74, 59],
    #[69, 49, 110, 124, 31, 111],
    #[70, 103, 107, 42, 77, 63],
    #[71, 46, 58, 96, 78, 112],
    #[72, 102, 106, 95, 29, 64],
    #[73, 94, 56, 52, 25, 24],
    #[74, 96, 54, 104, 71, 3],
    #[75, 42, 55, 50, 70, 4],
    #[76, 93, 19, 16, 118, 22],
    #[77, 43, 23, 103, 67, 19],
    #[78, 100, 22, 46, 68, 18],
    #[79, 44, 57, 101, 66, 20],
    #[80, 90, 14, 21, 109, 102],
    #[81, 8, 123, 60, 4, 43],
    #[82, 6, 125, 61, 2, 45],
    #[83, 36, 93, 62, 24, 44],
    #[84, 33, 96, 112, 57, 98],
    #[85, 35, 94, 65, 22, 126],
    #[86, 34, 95, 64, 23, 97],
    #[87, 12, 97, 105, 20, 94],
    #[88, 0, 126, 106, 1, 95],
    #[89, 11, 98, 107, 19, 42],
    #[90, 37, 45, 109, 55, 93],
    #[91, 38, 44, 108, 54, 125],
    #[92, 9, 100, 59, 56, 123],
    #[93, 32, 92, 118, 48, 121],
    #[94, 79, 89, 25, 101, 84],
    #[95, 29, 40, 72, 102, 122],
    #[96, 78, 88, 71, 46, 85],
    #[97, 26, 84, 115, 15, 40],
    #[98, 28, 86, 127, 53, 88],
    #[99, 27, 85, 113, 14, 87],
    #[100, 74, 82, 68, 104, 91],
    #[101, 66, 35, 79, 44, 11],
    #[102, 116, 34, 29, 45, 10],
    #[103, 67, 80, 77, 43, 12],
    #[104, 71, 9, 74, 96, 6],
    #[105, 20, 113, 87, 12, 70],
    #[106, 1, 127, 88, 0, 71],
    #[107, 19, 114, 89, 11, 25],
    #[108, 54, 68, 91, 38, 69],
    #[109, 55, 67, 90, 37, 119],
    #[110, 17, 116, 41, 39, 117],
    #[111, 3, 118, 121, 7, 116],
    #[112, 57, 25, 84, 33, 115],
    #[113, 14, 63, 99, 27, 58],
    #[114, 16, 65, 126, 76, 106],
    #[115, 15, 64, 97, 26, 105],
    #[116, 51, 61, 45, 120, 109],
    #[117, 47, 108, 125, 5, 61],
    #[118, 48, 109, 93, 32, 62],
    #[119, 13, 59, 123, 30, 60],
    #[120, 95, 17, 51, 72, 2],
    #[121, 7, 124, 111, 3, 100],
    #[122, 80, 42, 63, 21, 99],
    #[123, 30, 90, 119, 13, 82],
    #[124, 31, 91, 69, 49, 83],
    #[125, 5, 41, 117, 47, 81],
    #[126, 76, 122, 114, 16, 89],
    #[127, 53, 112, 98, 28, 107]] : Array (Array ℕ)).getD k.val #[]).getD j.val 0)
private def prev56_7 (k : Fin 128) (j : Fin 6) : Fin 128 :=
  Fin.ofNat 128 (((#[#[0, 88, 16, 1, 106, 46],
    #[1, 106, 28, 0, 88, 29],
    #[2, 61, 30, 6, 82, 120],
    #[3, 111, 32, 7, 121, 74],
    #[4, 60, 5, 8, 81, 75],
    #[5, 125, 17, 47, 117, 2],
    #[6, 82, 47, 2, 61, 104],
    #[7, 121, 49, 3, 111, 51],
    #[8, 81, 13, 4, 60, 52],
    #[9, 92, 104, 56, 59, 48],
    #[10, 40, 14, 18, 58, 102],
    #[11, 89, 53, 19, 107, 101],
    #[12, 87, 15, 20, 105, 103],
    #[13, 119, 9, 30, 123, 6],
    #[14, 113, 80, 27, 99, 12],
    #[15, 115, 34, 26, 97, 10],
    #[16, 114, 35, 76, 126, 11],
    #[17, 110, 120, 39, 41, 31],
    #[18, 58, 26, 10, 40, 78],
    #[19, 107, 76, 11, 89, 77],
    #[20, 105, 27, 12, 87, 79],
    #[21, 63, 29, 80, 122, 27],
    #[22, 65, 78, 35, 85, 76],
    #[23, 64, 77, 34, 86, 26],
    #[24, 62, 31, 36, 83, 73],
    #[25, 52, 112, 94, 73, 107],
    #[26, 97, 57, 15, 115, 20],
    #[27, 99, 22, 14, 113, 18],
    #[28, 98, 23, 53, 127, 19],
    #[29, 95, 18, 102, 72, 23],
    #[30, 123, 55, 13, 119, 4],
    #[31, 124, 54, 49, 69, 3],
    #[32, 93, 56, 48, 118, 24],
    #[33, 84, 46, 57, 112, 15],
    #[34, 86, 102, 23, 64, 53],
    #[35, 85, 101, 22, 65, 14],
    #[36, 83, 48, 24, 62, 50],
    #[37, 90, 51, 55, 109, 13],
    #[38, 91, 52, 54, 108, 49],
    #[39, 41, 50, 17, 110, 47],
    #[40, 6, 95, 58, 2, 97],
    #[41, 34, 125, 110, 23, 45],
    #[42, 75, 122, 70, 50, 89],
    #[43, 77, 41, 67, 103, 81],
    #[44, 79, 91, 66, 101, 83],
    #[45, 29, 90, 116, 102, 82],
    #[46, 71, 10, 78, 96, 35],
    #[47, 117, 38, 5, 125, 8],
    #[48, 118, 37, 32, 93, 7],
    #[49, 69, 39, 31, 124, 36],
    #[50, 67, 8, 75, 43, 37],
    #[51, 116, 6, 120, 45, 39],
    #[52, 66, 36, 73, 44, 9],
    #[53, 127, 33, 28, 98, 0],
    #[54, 108, 74, 38, 91, 5],
    #[55, 109, 75, 37, 90, 32],
    #[56, 59, 73, 9, 92, 30],
    #[57, 112, 79, 33, 84, 28],
    #[58, 2, 71, 40, 6, 113],
    #[59, 22, 119, 92, 35, 68],
    #[60, 20, 67, 81, 12, 119],
    #[61, 18, 116, 82, 10, 117],
    #[62, 19, 66, 83, 11, 118],
    #[63, 55, 113, 122, 37, 70],
    #[64, 17, 115, 86, 39, 72],
    #[65, 56, 114, 85, 9, 25],
    #[66, 101, 59, 44, 79, 60],
    #[67, 103, 109, 43, 77, 62],
    #[68, 46, 108, 100, 78, 61],
    #[69, 53, 62, 124, 28, 108],
    #[70, 50, 64, 42, 75, 105],
    #[71, 104, 65, 96, 74, 106],
    #[72, 51, 63, 95, 120, 58],
    #[73, 44, 4, 52, 66, 54],
    #[74, 100, 2, 104, 68, 56],
    #[75, 43, 24, 50, 67, 17],
    #[76, 126, 21, 16, 114, 1],
    #[77, 42, 20, 103, 70, 21],
    #[78, 96, 1, 46, 71, 57],
    #[79, 94, 19, 101, 25, 22],
    #[80, 122, 103, 21, 63, 16],
    #[81, 12, 44, 60, 20, 125],
    #[82, 10, 100, 61, 18, 123],
    #[83, 11, 43, 62, 19, 124],
    #[84, 38, 97, 112, 54, 94],
    #[85, 9, 99, 65, 56, 96],
    #[86, 39, 98, 64, 17, 42],
    #[87, 8, 42, 105, 4, 99],
    #[88, 7, 96, 106, 3, 98],
    #[89, 36, 94, 107, 24, 126],
    #[90, 80, 123, 109, 21, 43],
    #[91, 33, 124, 108, 57, 100],
    #[92, 35, 93, 59, 22, 44],
    #[93, 76, 83, 118, 16, 90],
    #[94, 73, 85, 25, 52, 87],
    #[95, 120, 86, 72, 51, 88],
    #[96, 74, 84, 71, 104, 40],
    #[97, 5, 87, 115, 47, 86],
    #[98, 31, 89, 127, 49, 84],
    #[99, 30, 40, 113, 13, 122],
    #[100, 78, 92, 68, 46, 121],
    #[101, 25, 12, 79, 94, 33],
    #[102, 72, 0, 29, 95, 80],
    #[103, 70, 11, 77, 42, 34],
    #[104, 68, 7, 74, 100, 38],
    #[105, 4, 25, 87, 8, 115],
    #[106, 3, 72, 88, 7, 114],
    #[107, 24, 70, 89, 36, 127],
    #[108, 57, 117, 91, 33, 66],
    #[109, 21, 118, 90, 80, 116],
    #[110, 23, 69, 41, 34, 67],
    #[111, 1, 68, 121, 0, 69],
    #[112, 54, 127, 84, 38, 71],
    #[113, 13, 105, 99, 30, 65],
    #[114, 48, 107, 126, 32, 63],
    #[115, 47, 58, 97, 5, 112],
    #[116, 102, 110, 45, 29, 111],
    #[117, 15, 60, 125, 26, 110],
    #[118, 16, 111, 93, 76, 59],
    #[119, 14, 61, 123, 27, 109],
    #[120, 45, 3, 51, 116, 55],
    #[121, 0, 45, 111, 1, 93],
    #[122, 37, 126, 63, 55, 95],
    #[123, 27, 81, 119, 14, 92],
    #[124, 28, 121, 69, 53, 41],
    #[125, 26, 82, 117, 15, 91],
    #[126, 32, 88, 114, 48, 85],
    #[127, 49, 106, 98, 31, 64]] : Array (Array ℕ)).getD k.val #[]).getD j.val 0)
set_option maxHeartbeats 1600000 in
private theorem cert56_7 : ∃ c, c ∈ Subgroup.centralizer (Subgroup.closure (Set.range e56_7) : Set SylowModel) ∧ c ∉ Subgroup.closure (Set.range e56_7) := by
  refine ⟨rootOne ^ 2 * root 2 * root 4 * root 8, centralizes_generators e56_7 _ (by decide +kernel), ?_⟩
  exact outside_of_table e56_7 a56_7 0 next56_7 prev56_7
    (by decide +kernel) (by decide +kernel) (by decide +kernel) _ (by decide +kernel)

private def s57 : Fin 3 → SylowModel := ![rootOne ^ 3, root 2 * root 3 * root 4 * root 5 * root 7 * root 8 * root 9, root 2 * root 4 * root 6 * root 7]
set_option maxHeartbeats 1600000 in
private theorem gen57 : Subgroup.closure (Set.range s57) = smallParityCensusNode 57 := by
  rw [node57]
  exact closure_eq_words s57 o57 (![[1], [2], [0]]) (![[2], [0], [1], [0, 0], [0, 0, 0, 1, 1, 1, 0, 1], [2, 2], [1, 1, 2, 2], [0, 0, 0, 1, 1, 0, 1, 1]]) (by decide +kernel) (by decide +kernel)

private def e57_1 : Fin 6 → SylowModel := ![decode 0, decode 956, decode 212, decode 2048, decode 492, decode 596]
set_option maxHeartbeats 1600000 in
private theorem edgeEq57_1 : binaryFamily s57 (s57 0) (![true, false, false]) = e57_1 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert57_1 : Subgroup.closure (Set.range e57_1) ≤ character.ker := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨j, rfl⟩
  exact (show ∀ j, e57_1 j ∈ character.ker from by decide +kernel) j

private def e57_2 : Fin 6 → SylowModel := ![decode 1024, decode 0, decode 212, decode 1360, decode 128, decode 84]
set_option maxHeartbeats 1600000 in
private theorem edgeEq57_2 : binaryFamily s57 (s57 1) (![false, true, false]) = e57_2 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert57_2 : Represented smallParityCensusNode (Subgroup.closure (Set.range e57_2)) := by
  refine ⟨86, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node86]
  exact closure_eq_words _ o86 (![[1], [], [0, 2], [0, 0, 1, 2], [4, 5], [0, 2, 4, 5]]) (![[0, 0, 0, 5, 3], [0], [0, 0, 3, 4, 0], [0, 0], [2, 5], [2, 2], [0, 3, 0, 3]]) (by decide +kernel) (by decide +kernel)

private def e57_3 : Fin 6 → SylowModel := ![decode 0, decode 4028, decode 212, decode 2048, decode 1516, decode 596]
set_option maxHeartbeats 1600000 in
private theorem edgeEq57_3 : binaryFamily s57 (s57 0) (![true, true, false]) = e57_3 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert57_3 : Represented smallParityCensusNode (Subgroup.closure (Set.range e57_3)) := by
  refine ⟨92, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node92]
  exact closure_eq_words _ o92 (![[], [1, 3, 6], [0, 4, 5], [3, 2], [4, 1], [0]]) (![[5], [2, 5, 4], [1, 1, 3], [1, 5, 1, 5], [2, 5], [2, 2], [1, 1, 1, 1]]) (by decide +kernel) (by decide +kernel)

private def e57_4 : Fin 6 → SylowModel := ![decode 1024, decode 956, decode 0, decode 1664, decode 828, decode 768]
set_option maxHeartbeats 1600000 in
private theorem edgeEq57_4 : binaryFamily s57 (s57 2) (![false, false, true]) = e57_4 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert57_4 : Represented smallParityCensusNode (Subgroup.closure (Set.range e57_4)) := by
  refine ⟨65, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node65]
  exact closure_eq_words _ o65 (![[0], [1], [], [0, 5], [1, 1, 1], [4]]) (![[0], [1], [0, 0], [0, 0, 0, 4, 0, 1], [5], [1, 1, 5], [0, 0, 3, 3]]) (by decide +kernel) (by decide +kernel)

private def e57_5 : Fin 6 → SylowModel := ![decode 0, decode 956, decode 3284, decode 2048, decode 492, decode 1620]
set_option maxHeartbeats 1600000 in
private theorem edgeEq57_5 : binaryFamily s57 (s57 0) (![true, false, true]) = e57_5 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert57_5 : Represented smallParityCensusNode (Subgroup.closure (Set.range e57_5)) := by
  refine ⟨73, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node73]
  exact closure_eq_words _ o73 (![[], [1, 5], [0, 3, 2], [1, 2, 1], [1, 3, 4], [3, 0, 4]]) (![[4, 5, 4], [2, 3, 4, 2], [1, 3, 1], [1, 4], [2, 3, 5, 3], [2, 1, 1, 5], [1, 1, 4, 4]]) (by decide +kernel) (by decide +kernel)

private def e57_6 : Fin 6 → SylowModel := ![decode 1024, decode 0, decode 744, decode 1360, decode 128, decode 744]
set_option maxHeartbeats 1600000 in
private theorem edgeEq57_6 : binaryFamily s57 (s57 1) (![false, true, true]) = e57_6 := by decide +kernel
private def a57_6 (k : Fin 128) : SylowModel :=
  decode ((#[0, 1024, 2048, 384, 768, 512, 3072, 1152, 1792, 1536, 2432, 2816, 2560, 464, 640, 896, 256, 3200, 3840, 3584, 1872, 1920, 1664, 1280, 2256, 2688, 2944, 2304, 80, 720, 976, 128, 232, 3664, 3968, 3712, 3328, 2000, 1104, 1360, 1408, 2384, 3024, 2768, 2176, 848, 592, 208, 2664, 360, 1000, 744, 3792, 3408, 3152, 3456, 1232, 1488, 1616, 2640, 2896, 2512, 336, 1976, 1768, 3048, 2408, 2152, 824, 616, 872, 488, 3536, 3280, 3920, 1744, 2128, 3128, 3176, 1848, 1208, 1464, 1640, 1512, 1256, 2232, 2280, 2536, 2920, 696, 56, 312, 104, 4048, 3256, 3896, 3640, 3304, 3944, 3688, 1080, 1336, 1720, 1384, 1128, 2024, 2360, 3000, 2744, 2792, 440, 184, 568, 4024, 3768, 3384, 4072, 3816, 3432, 1592, 1896, 2616, 2872, 2488, 952, 3512, 3560, 2104] : Array ℕ).getD k.val 0)
private def next57_6 (k : Fin 128) (j : Fin 6) : Fin 128 :=
  Fin.ofNat 128 (((#[#[1, 0, 51, 39, 31, 51],
    #[2, 1, 79, 43, 40, 79],
    #[6, 2, 67, 54, 44, 67],
    #[40, 3, 70, 56, 16, 70],
    #[8, 4, 71, 58, 15, 71],
    #[9, 5, 32, 20, 14, 32],
    #[0, 6, 94, 30, 55, 94],
    #[44, 7, 63, 59, 23, 63],
    #[11, 8, 100, 61, 22, 100],
    #[12, 9, 101, 24, 21, 101],
    #[55, 10, 87, 72, 27, 87],
    #[18, 11, 88, 74, 26, 88],
    #[19, 12, 48, 33, 25, 48],
    #[57, 13, 91, 7, 62, 91],
    #[22, 14, 92, 37, 5, 92],
    #[21, 15, 49, 75, 4, 49],
    #[23, 16, 50, 38, 3, 50],
    #[31, 17, 77, 45, 36, 77],
    #[4, 18, 113, 47, 35, 113],
    #[5, 19, 114, 13, 34, 114],
    #[60, 20, 82, 10, 75, 82],
    #[26, 21, 80, 41, 9, 80],
    #[25, 22, 81, 76, 8, 81],
    #[27, 23, 119, 42, 7, 119],
    #[73, 24, 108, 17, 76, 108],
    #[35, 25, 109, 52, 12, 109],
    #[34, 26, 65, 93, 11, 65],
    #[36, 27, 66, 53, 10, 66],
    #[38, 28, 111, 23, 47, 111],
    #[75, 29, 112, 21, 46, 112],
    #[37, 30, 68, 22, 45, 68],
    #[7, 31, 69, 57, 0, 69],
    #[84, 32, 16, 63, 92, 16],
    #[46, 33, 97, 3, 93, 97],
    #[15, 34, 95, 28, 19, 95],
    #[14, 35, 96, 62, 18, 96],
    #[16, 36, 125, 29, 17, 125],
    #[42, 37, 64, 27, 58, 64],
    #[76, 38, 103, 25, 57, 103],
    #[41, 39, 104, 26, 56, 104],
    #[10, 40, 102, 60, 1, 102],
    #[53, 41, 122, 36, 61, 122],
    #[93, 42, 123, 34, 60, 123],
    #[52, 43, 85, 35, 59, 85],
    #[17, 44, 86, 73, 2, 86],
    #[20, 45, 124, 9, 30, 124],
    #[58, 46, 89, 8, 29, 89],
    #[56, 47, 90, 40, 28, 90],
    #[99, 48, 27, 77, 109, 27],
    #[103, 49, 31, 119, 71, 31],
    #[105, 50, 5, 80, 70, 5],
    #[64, 51, 4, 81, 69, 4],
    #[29, 52, 78, 16, 74, 78],
    #[62, 53, 116, 14, 73, 116],
    #[28, 54, 117, 15, 72, 117],
    #[3, 55, 115, 46, 6, 115],
    #[24, 56, 83, 12, 39, 83],
    #[61, 57, 84, 11, 38, 84],
    #[59, 58, 120, 44, 37, 120],
    #[33, 59, 127, 19, 43, 127],
    #[74, 60, 106, 18, 42, 106],
    #[72, 61, 107, 55, 41, 107],
    #[39, 62, 110, 1, 13, 110],
    #[107, 63, 21, 88, 119, 21],
    #[109, 64, 56, 121, 120, 56],
    #[116, 65, 44, 125, 88, 44],
    #[118, 66, 12, 95, 87, 12],
    #[78, 67, 11, 96, 86, 11],
    #[79, 68, 47, 104, 124, 47],
    #[82, 69, 15, 101, 51, 15],
    #[120, 70, 14, 100, 50, 14],
    #[83, 71, 0, 102, 49, 0],
    #[13, 72, 98, 5, 54, 98],
    #[47, 73, 99, 4, 53, 99],
    #[45, 74, 126, 31, 52, 126],
    #[43, 75, 105, 2, 20, 105],
    #[54, 76, 121, 6, 24, 121],
    #[90, 77, 34, 71, 125, 34],
    #[92, 78, 72, 110, 126, 72],
    #[122, 79, 8, 65, 102, 8],
    #[85, 80, 7, 67, 101, 7],
    #[123, 81, 40, 66, 100, 40],
    #[48, 82, 38, 108, 105, 38],
    #[87, 83, 37, 106, 104, 37],
    #[86, 84, 75, 127, 103, 75],
    #[94, 85, 61, 117, 127, 61],
    #[97, 86, 26, 114, 67, 26],
    #[126, 87, 25, 113, 66, 25],
    #[98, 88, 2, 115, 65, 2],
    #[102, 89, 62, 83, 112, 62],
    #[100, 90, 30, 120, 111, 30],
    #[101, 91, 29, 82, 110, 29],
    #[104, 92, 3, 79, 32, 3],
    #[30, 93, 118, 0, 33, 118],
    #[111, 94, 18, 49, 115, 18],
    #[68, 95, 17, 51, 114, 17],
    #[112, 96, 55, 50, 113, 55],
    #[32, 97, 53, 91, 118, 53],
    #[70, 98, 52, 89, 117, 52],
    #[69, 99, 93, 124, 116, 93],
    #[127, 100, 1, 86, 81, 1],
    #[106, 101, 23, 87, 80, 23],
    #[108, 102, 22, 48, 79, 22],
    #[66, 103, 20, 123, 84, 20],
    #[67, 104, 58, 85, 83, 58],
    #[65, 105, 57, 122, 82, 57],
    #[115, 106, 76, 98, 123, 76],
    #[113, 107, 43, 126, 122, 43],
    #[114, 108, 42, 97, 121, 42],
    #[117, 109, 10, 94, 48, 10],
    #[81, 110, 46, 64, 91, 46],
    #[80, 111, 45, 105, 90, 45],
    #[119, 112, 13, 103, 89, 13],
    #[124, 113, 6, 69, 96, 6],
    #[89, 114, 36, 70, 95, 36],
    #[91, 115, 35, 32, 94, 35],
    #[50, 116, 33, 112, 99, 33],
    #[51, 117, 74, 68, 98, 74],
    #[49, 118, 73, 111, 97, 73],
    #[121, 119, 9, 109, 63, 9],
    #[88, 120, 39, 107, 64, 39],
    #[96, 121, 60, 78, 108, 60],
    #[95, 122, 59, 118, 107, 59],
    #[125, 123, 24, 116, 106, 24],
    #[63, 124, 28, 84, 68, 28],
    #[110, 125, 19, 92, 77, 19],
    #[71, 126, 54, 90, 78, 54],
    #[77, 127, 41, 99, 85, 41]] : Array (Array ℕ)).getD k.val #[]).getD j.val 0)
private def prev57_6 (k : Fin 128) (j : Fin 6) : Fin 128 :=
  Fin.ofNat 128 (((#[#[6, 0, 71, 93, 31, 71],
    #[0, 1, 100, 62, 40, 100],
    #[1, 2, 88, 75, 44, 88],
    #[55, 3, 92, 33, 16, 92],
    #[18, 4, 51, 73, 15, 51],
    #[19, 5, 50, 72, 14, 50],
    #[2, 6, 113, 76, 55, 113],
    #[31, 7, 80, 13, 23, 80],
    #[4, 8, 79, 46, 22, 79],
    #[5, 9, 119, 45, 21, 119],
    #[40, 10, 109, 20, 27, 109],
    #[8, 11, 67, 57, 26, 67],
    #[9, 12, 66, 56, 25, 66],
    #[72, 13, 112, 19, 62, 112],
    #[35, 14, 70, 53, 5, 70],
    #[34, 15, 69, 54, 4, 69],
    #[36, 16, 32, 52, 3, 32],
    #[44, 17, 95, 24, 36, 95],
    #[11, 18, 94, 60, 35, 94],
    #[12, 19, 125, 59, 34, 125],
    #[45, 20, 103, 5, 75, 103],
    #[15, 21, 63, 29, 9, 63],
    #[14, 22, 102, 30, 8, 102],
    #[16, 23, 101, 28, 7, 101],
    #[56, 24, 123, 9, 76, 123],
    #[22, 25, 87, 38, 12, 87],
    #[21, 26, 86, 39, 11, 86],
    #[23, 27, 48, 37, 10, 48],
    #[54, 28, 124, 34, 47, 124],
    #[52, 29, 91, 36, 46, 91],
    #[93, 30, 90, 6, 45, 90],
    #[17, 31, 49, 74, 0, 49],
    #[97, 32, 5, 115, 92, 5],
    #[59, 33, 116, 12, 93, 116],
    #[26, 34, 77, 42, 19, 77],
    #[25, 35, 115, 43, 18, 115],
    #[27, 36, 114, 41, 17, 114],
    #[30, 37, 83, 14, 58, 83],
    #[28, 38, 82, 16, 57, 82],
    #[62, 39, 120, 0, 56, 120],
    #[3, 40, 81, 47, 1, 81],
    #[39, 41, 127, 21, 61, 127],
    #[37, 42, 108, 23, 60, 108],
    #[75, 43, 107, 1, 59, 107],
    #[7, 44, 65, 58, 2, 65],
    #[74, 45, 111, 17, 30, 111],
    #[33, 46, 110, 55, 29, 110],
    #[73, 47, 68, 18, 28, 68],
    #[82, 48, 12, 102, 109, 12],
    #[118, 49, 15, 94, 71, 15],
    #[116, 50, 16, 96, 70, 16],
    #[117, 51, 0, 95, 69, 0],
    #[43, 52, 98, 25, 74, 98],
    #[41, 53, 97, 27, 73, 97],
    #[76, 54, 126, 2, 72, 126],
    #[10, 55, 96, 61, 6, 96],
    #[47, 56, 64, 3, 39, 64],
    #[13, 57, 105, 31, 38, 105],
    #[46, 58, 104, 4, 37, 104],
    #[58, 59, 122, 7, 43, 122],
    #[20, 60, 121, 40, 42, 121],
    #[57, 61, 85, 8, 41, 85],
    #[53, 62, 89, 35, 13, 89],
    #[124, 63, 7, 32, 119, 7],
    #[51, 64, 37, 110, 120, 37],
    #[105, 65, 26, 79, 88, 26],
    #[103, 66, 27, 81, 87, 27],
    #[104, 67, 2, 80, 86, 2],
    #[95, 68, 30, 117, 124, 30],
    #[99, 69, 31, 113, 51, 31],
    #[98, 70, 3, 114, 50, 3],
    #[126, 71, 4, 77, 49, 4],
    #[61, 72, 78, 10, 54, 78],
    #[24, 73, 118, 44, 53, 118],
    #[60, 74, 117, 11, 52, 117],
    #[29, 75, 84, 15, 20, 84],
    #[38, 76, 106, 22, 24, 106],
    #[127, 77, 17, 48, 125, 17],
    #[67, 78, 52, 121, 126, 52],
    #[68, 79, 1, 92, 102, 1],
    #[111, 80, 21, 50, 101, 21],
    #[110, 81, 22, 51, 100, 22],
    #[69, 82, 20, 91, 105, 20],
    #[71, 83, 56, 89, 104, 56],
    #[32, 84, 57, 124, 103, 57],
    #[80, 85, 43, 104, 127, 43],
    #[84, 86, 44, 100, 67, 44],
    #[83, 87, 10, 101, 66, 10],
    #[120, 88, 11, 63, 65, 11],
    #[114, 89, 46, 98, 112, 46],
    #[77, 90, 47, 126, 111, 47],
    #[115, 91, 13, 97, 110, 13],
    #[78, 92, 14, 125, 32, 14],
    #[42, 93, 99, 26, 33, 99],
    #[85, 94, 6, 109, 115, 6],
    #[122, 95, 34, 66, 114, 34],
    #[121, 96, 35, 67, 113, 35],
    #[86, 97, 33, 108, 118, 33],
    #[88, 98, 72, 106, 117, 72],
    #[48, 99, 73, 127, 116, 73],
    #[90, 100, 8, 70, 81, 8],
    #[91, 101, 9, 69, 80, 9],
    #[89, 102, 40, 71, 79, 40],
    #[49, 103, 38, 112, 84, 38],
    #[92, 104, 39, 68, 83, 39],
    #[50, 105, 75, 111, 82, 75],
    #[101, 106, 60, 83, 123, 60],
    #[63, 107, 61, 120, 122, 61],
    #[102, 108, 24, 82, 121, 24],
    #[64, 109, 25, 119, 48, 25],
    #[125, 110, 62, 78, 91, 62],
    #[94, 111, 28, 118, 90, 28],
    #[96, 112, 29, 116, 89, 29],
    #[107, 113, 18, 87, 96, 18],
    #[108, 114, 19, 86, 95, 19],
    #[106, 115, 55, 88, 94, 55],
    #[65, 116, 53, 123, 99, 53],
    #[109, 117, 54, 85, 98, 54],
    #[66, 118, 93, 122, 97, 93],
    #[112, 119, 23, 49, 63, 23],
    #[70, 120, 58, 90, 64, 58],
    #[119, 121, 76, 64, 108, 76],
    #[79, 122, 41, 105, 107, 41],
    #[81, 123, 42, 103, 106, 42],
    #[113, 124, 45, 99, 68, 45],
    #[123, 125, 36, 65, 77, 36],
    #[87, 126, 74, 107, 78, 74],
    #[100, 127, 59, 84, 85, 59]] : Array (Array ℕ)).getD k.val #[]).getD j.val 0)
set_option maxHeartbeats 1600000 in
private theorem cert57_6 : ∃ c, c ∈ Subgroup.centralizer (Subgroup.closure (Set.range e57_6) : Set SylowModel) ∧ c ∉ Subgroup.closure (Set.range e57_6) := by
  refine ⟨rootOne ^ 2 * root 2 * root 4 * root 8, centralizes_generators e57_6 _ (by decide +kernel), ?_⟩
  exact outside_of_table e57_6 a57_6 0 next57_6 prev57_6
    (by decide +kernel) (by decide +kernel) (by decide +kernel) _ (by decide +kernel)

private def e57_7 : Fin 6 → SylowModel := ![decode 0, decode 4028, decode 3284, decode 2048, decode 1516, decode 1620]
set_option maxHeartbeats 1600000 in
private theorem edgeEq57_7 : binaryFamily s57 (s57 0) (![true, true, true]) = e57_7 := by decide +kernel
private def a57_7 (k : Fin 128) : SylowModel :=
  decode ((#[0, 2048, 384, 768, 512, 2432, 2816, 2560, 464, 640, 896, 256, 1468, 1260, 2256, 2688, 2944, 2304, 80, 720, 976, 128, 1028, 232, 3644, 3692, 1340, 1724, 1980, 1132, 2028, 1772, 2384, 3024, 2768, 2176, 848, 592, 208, 3076, 1156, 1796, 1540, 2664, 360, 1000, 744, 3772, 3388, 3132, 3820, 3436, 3180, 1596, 1852, 1212, 1900, 1644, 1516, 2640, 2896, 2512, 336, 3204, 3844, 3588, 1876, 1924, 1668, 1284, 3048, 2408, 2152, 824, 616, 872, 488, 3516, 3260, 3900, 3564, 3308, 3948, 1084, 1388, 2128, 3668, 3972, 3716, 3332, 2004, 1108, 1364, 1412, 2232, 2280, 2536, 2920, 696, 56, 312, 104, 4028, 4076, 3796, 3412, 3156, 3460, 1236, 1492, 1620, 2360, 3000, 2744, 2792, 440, 184, 568, 3540, 3284, 3924, 1748, 2616, 2872, 2488, 952, 4052, 2104] : Array ℕ).getD k.val 0)
private def next57_7 (k : Fin 128) (j : Fin 6) : Fin 128 :=
  Fin.ofNat 128 (((#[#[0, 102, 119, 1, 58, 110],
    #[1, 83, 109, 0, 82, 120],
    #[2, 24, 105, 5, 29, 90],
    #[3, 78, 126, 6, 31, 92],
    #[4, 77, 104, 7, 30, 91],
    #[5, 12, 91, 2, 50, 104],
    #[6, 54, 121, 3, 52, 106],
    #[7, 53, 90, 4, 51, 105],
    #[8, 51, 39, 61, 54, 68],
    #[9, 48, 86, 15, 56, 108],
    #[10, 49, 120, 16, 57, 109],
    #[11, 47, 118, 17, 13, 66],
    #[12, 19, 74, 77, 17, 96],
    #[13, 21, 117, 81, 60, 124],
    #[14, 30, 22, 38, 78, 88],
    #[15, 27, 66, 9, 80, 118],
    #[16, 28, 110, 10, 81, 119],
    #[17, 26, 108, 11, 25, 86],
    #[18, 81, 107, 85, 27, 41],
    #[19, 25, 64, 34, 83, 93],
    #[20, 82, 65, 33, 26, 40],
    #[21, 79, 106, 35, 84, 121],
    #[22, 45, 18, 39, 122, 33],
    #[23, 104, 47, 95, 68, 83],
    #[24, 33, 95, 53, 11, 75],
    #[25, 35, 124, 57, 37, 117],
    #[26, 37, 46, 48, 5, 71],
    #[27, 8, 44, 47, 7, 114],
    #[28, 38, 101, 102, 6, 70],
    #[29, 0, 98, 52, 33, 111],
    #[30, 10, 100, 103, 85, 113],
    #[31, 9, 99, 50, 32, 112],
    #[32, 57, 93, 62, 48, 64],
    #[33, 13, 41, 20, 102, 107],
    #[34, 58, 42, 19, 47, 63],
    #[35, 55, 92, 21, 103, 126],
    #[36, 103, 88, 60, 12, 22],
    #[37, 50, 87, 59, 55, 69],
    #[38, 52, 89, 14, 53, 67],
    #[39, 71, 32, 22, 115, 19],
    #[40, 75, 38, 63, 113, 60],
    #[41, 23, 36, 64, 111, 14],
    #[42, 76, 37, 65, 127, 61],
    #[43, 90, 26, 74, 88, 102],
    #[44, 120, 79, 71, 41, 12],
    #[45, 118, 77, 70, 93, 54],
    #[46, 119, 78, 114, 40, 53],
    #[47, 60, 72, 27, 2, 45],
    #[48, 14, 70, 26, 4, 101],
    #[49, 61, 114, 83, 3, 44],
    #[50, 1, 111, 31, 19, 98],
    #[51, 16, 113, 84, 62, 100],
    #[52, 15, 112, 29, 18, 99],
    #[53, 62, 76, 24, 15, 43],
    #[54, 18, 23, 79, 16, 97],
    #[55, 20, 75, 78, 1, 95],
    #[56, 3, 115, 82, 14, 122],
    #[57, 4, 116, 25, 61, 123],
    #[58, 2, 73, 80, 59, 94],
    #[59, 84, 68, 37, 24, 39],
    #[60, 29, 67, 36, 79, 89],
    #[61, 31, 69, 8, 77, 87],
    #[62, 80, 63, 32, 28, 42],
    #[63, 96, 61, 40, 100, 37],
    #[64, 43, 59, 41, 98, 8],
    #[65, 97, 60, 42, 125, 38],
    #[66, 125, 4, 120, 43, 5],
    #[67, 101, 20, 87, 124, 85],
    #[68, 44, 19, 88, 94, 32],
    #[69, 46, 62, 89, 123, 34],
    #[70, 110, 55, 45, 64, 24],
    #[71, 108, 53, 44, 107, 78],
    #[72, 109, 54, 101, 63, 77],
    #[73, 65, 52, 123, 110, 31],
    #[74, 106, 49, 43, 22, 27],
    #[75, 105, 48, 97, 69, 28],
    #[76, 126, 102, 96, 67, 26],
    #[77, 85, 97, 12, 9, 23],
    #[78, 32, 43, 55, 10, 76],
    #[79, 34, 96, 54, 0, 74],
    #[80, 6, 122, 58, 8, 115],
    #[81, 7, 123, 13, 38, 116],
    #[82, 5, 94, 56, 36, 73],
    #[83, 36, 45, 49, 35, 72],
    #[84, 11, 125, 51, 34, 127],
    #[85, 56, 40, 18, 49, 65],
    #[86, 127, 7, 110, 23, 2],
    #[87, 114, 34, 67, 117, 62],
    #[88, 70, 33, 68, 73, 18],
    #[89, 72, 85, 69, 116, 20],
    #[90, 73, 9, 126, 114, 17],
    #[91, 116, 11, 106, 71, 15],
    #[92, 115, 0, 105, 72, 16],
    #[93, 74, 8, 107, 112, 59],
    #[94, 42, 31, 116, 120, 52],
    #[95, 92, 28, 23, 39, 48],
    #[96, 91, 27, 76, 89, 49],
    #[97, 121, 83, 75, 87, 47],
    #[98, 87, 80, 113, 90, 56],
    #[99, 89, 82, 127, 92, 58],
    #[100, 39, 25, 111, 91, 13],
    #[101, 86, 24, 72, 42, 55],
    #[102, 59, 71, 28, 21, 46],
    #[103, 17, 127, 30, 20, 125],
    #[104, 94, 15, 121, 101, 11],
    #[105, 123, 17, 92, 45, 9],
    #[106, 122, 1, 91, 46, 10],
    #[107, 95, 14, 93, 99, 36],
    #[108, 99, 2, 119, 96, 7],
    #[109, 100, 21, 118, 95, 6],
    #[110, 98, 3, 86, 97, 35],
    #[111, 67, 56, 100, 104, 80],
    #[112, 69, 58, 125, 106, 82],
    #[113, 22, 13, 98, 105, 25],
    #[114, 66, 12, 46, 65, 79],
    #[115, 63, 50, 124, 108, 29],
    #[116, 107, 103, 94, 109, 84],
    #[117, 64, 51, 122, 66, 30],
    #[118, 112, 5, 109, 75, 4],
    #[119, 113, 35, 108, 74, 3],
    #[120, 111, 6, 66, 76, 21],
    #[121, 117, 10, 104, 70, 1],
    #[122, 40, 29, 117, 118, 50],
    #[123, 93, 84, 73, 119, 103],
    #[124, 41, 30, 115, 86, 51],
    #[125, 88, 81, 112, 121, 57],
    #[126, 124, 16, 90, 44, 0],
    #[127, 68, 57, 99, 126, 81]] : Array (Array ℕ)).getD k.val #[]).getD j.val 0)
private def prev57_7 (k : Fin 128) (j : Fin 6) : Fin 128 :=
  Fin.ofNat 128 (((#[#[0, 29, 92, 1, 79, 126],
    #[1, 50, 106, 0, 55, 121],
    #[2, 58, 108, 5, 47, 86],
    #[3, 56, 110, 6, 49, 119],
    #[4, 57, 66, 7, 48, 118],
    #[5, 82, 118, 2, 26, 66],
    #[6, 80, 120, 3, 28, 109],
    #[7, 81, 86, 4, 27, 108],
    #[8, 27, 93, 61, 80, 64],
    #[9, 31, 90, 15, 77, 105],
    #[10, 30, 121, 16, 78, 106],
    #[11, 84, 91, 17, 24, 104],
    #[12, 5, 114, 77, 36, 44],
    #[13, 33, 113, 81, 11, 100],
    #[14, 48, 107, 38, 56, 41],
    #[15, 52, 104, 9, 53, 91],
    #[16, 51, 126, 10, 54, 92],
    #[17, 103, 105, 11, 12, 90],
    #[18, 54, 22, 85, 52, 88],
    #[19, 12, 68, 34, 50, 39],
    #[20, 55, 67, 33, 103, 89],
    #[21, 13, 109, 35, 102, 120],
    #[22, 113, 14, 39, 74, 36],
    #[23, 41, 54, 95, 86, 77],
    #[24, 2, 101, 53, 59, 70],
    #[25, 19, 100, 57, 17, 113],
    #[26, 17, 43, 48, 20, 76],
    #[27, 15, 96, 47, 18, 74],
    #[28, 16, 95, 102, 62, 75],
    #[29, 60, 122, 52, 2, 115],
    #[30, 14, 124, 103, 4, 117],
    #[31, 61, 94, 50, 3, 73],
    #[32, 78, 39, 62, 31, 68],
    #[33, 24, 88, 20, 29, 22],
    #[34, 79, 87, 19, 84, 69],
    #[35, 25, 119, 21, 83, 110],
    #[36, 83, 41, 60, 82, 107],
    #[37, 26, 42, 59, 25, 63],
    #[38, 28, 40, 14, 81, 65],
    #[39, 100, 8, 22, 95, 59],
    #[40, 122, 85, 63, 46, 20],
    #[41, 124, 33, 64, 44, 18],
    #[42, 94, 34, 65, 101, 62],
    #[43, 64, 78, 74, 66, 53],
    #[44, 68, 27, 71, 126, 49],
    #[45, 22, 83, 70, 105, 47],
    #[46, 69, 26, 114, 106, 102],
    #[47, 11, 23, 27, 34, 97],
    #[48, 9, 75, 26, 32, 95],
    #[49, 10, 74, 83, 85, 96],
    #[50, 37, 115, 31, 5, 122],
    #[51, 8, 117, 84, 7, 124],
    #[52, 38, 73, 29, 6, 94],
    #[53, 7, 71, 24, 38, 46],
    #[54, 6, 72, 79, 8, 45],
    #[55, 35, 70, 78, 37, 101],
    #[56, 85, 111, 82, 9, 98],
    #[57, 32, 127, 25, 10, 125],
    #[58, 34, 112, 80, 0, 99],
    #[59, 102, 64, 37, 58, 93],
    #[60, 47, 65, 36, 13, 40],
    #[61, 49, 63, 8, 57, 42],
    #[62, 53, 69, 32, 51, 87],
    #[63, 115, 62, 40, 72, 34],
    #[64, 117, 19, 41, 70, 32],
    #[65, 73, 20, 42, 114, 85],
    #[66, 114, 15, 120, 117, 11],
    #[67, 111, 60, 87, 76, 38],
    #[68, 127, 59, 88, 23, 8],
    #[69, 112, 61, 89, 75, 37],
    #[70, 88, 48, 45, 121, 28],
    #[71, 39, 102, 44, 91, 26],
    #[72, 89, 47, 101, 92, 83],
    #[73, 90, 58, 123, 88, 82],
    #[74, 93, 12, 43, 119, 79],
    #[75, 40, 55, 97, 118, 24],
    #[76, 42, 53, 96, 120, 78],
    #[77, 4, 45, 12, 61, 72],
    #[78, 3, 46, 55, 14, 71],
    #[79, 21, 44, 54, 60, 114],
    #[80, 62, 98, 58, 15, 111],
    #[81, 18, 125, 13, 16, 127],
    #[82, 20, 99, 56, 1, 112],
    #[83, 1, 97, 49, 19, 23],
    #[84, 59, 123, 51, 21, 116],
    #[85, 77, 89, 18, 30, 67],
    #[86, 101, 9, 110, 124, 17],
    #[87, 98, 37, 67, 97, 61],
    #[88, 125, 36, 68, 43, 14],
    #[89, 99, 38, 69, 96, 60],
    #[90, 43, 7, 126, 98, 2],
    #[91, 96, 5, 106, 100, 4],
    #[92, 95, 35, 105, 99, 3],
    #[93, 123, 32, 107, 45, 19],
    #[94, 104, 82, 116, 68, 58],
    #[95, 107, 24, 23, 109, 55],
    #[96, 63, 79, 76, 108, 12],
    #[97, 65, 77, 75, 110, 54],
    #[98, 110, 29, 113, 64, 50],
    #[99, 108, 31, 127, 107, 52],
    #[100, 109, 30, 111, 63, 51],
    #[101, 67, 28, 72, 104, 48],
    #[102, 0, 76, 28, 33, 43],
    #[103, 36, 116, 30, 35, 123],
    #[104, 23, 4, 121, 111, 5],
    #[105, 75, 2, 92, 113, 7],
    #[106, 74, 21, 91, 112, 6],
    #[107, 116, 18, 93, 71, 33],
    #[108, 71, 17, 119, 115, 9],
    #[109, 72, 1, 118, 116, 10],
    #[110, 70, 16, 86, 73, 0],
    #[111, 120, 50, 100, 41, 29],
    #[112, 118, 52, 125, 93, 31],
    #[113, 119, 51, 98, 40, 30],
    #[114, 87, 49, 46, 90, 27],
    #[115, 92, 56, 124, 39, 80],
    #[116, 91, 57, 94, 89, 81],
    #[117, 121, 13, 122, 87, 25],
    #[118, 45, 11, 109, 122, 15],
    #[119, 46, 0, 108, 123, 16],
    #[120, 44, 10, 66, 94, 1],
    #[121, 97, 6, 104, 125, 21],
    #[122, 106, 80, 117, 22, 56],
    #[123, 105, 81, 73, 69, 57],
    #[124, 126, 25, 115, 67, 13],
    #[125, 66, 84, 112, 65, 103],
    #[126, 76, 3, 90, 127, 35],
    #[127, 86, 103, 99, 42, 84]] : Array (Array ℕ)).getD k.val #[]).getD j.val 0)
set_option maxHeartbeats 1600000 in
private theorem cert57_7 : ∃ c, c ∈ Subgroup.centralizer (Subgroup.closure (Set.range e57_7) : Set SylowModel) ∧ c ∉ Subgroup.closure (Set.range e57_7) := by
  refine ⟨rootOne ^ 2 * root 2 * root 4 * root 7, centralizes_generators e57_7 _ (by decide +kernel), ?_⟩
  exact outside_of_table e57_7 a57_7 0 next57_7 prev57_7
    (by decide +kernel) (by decide +kernel) (by decide +kernel) _ (by decide +kernel)

private def s58 : Fin 3 → SylowModel := ![rootOne ^ 3, root 2 * root 3 * root 4 * root 5 * root 6 * root 9, root 2 * root 4 * root 6 * root 7]
set_option maxHeartbeats 1600000 in
private theorem gen58 : Subgroup.closure (Set.range s58) = smallParityCensusNode 58 := by
  rw [node58]
  exact closure_eq_words s58 o58 (![[1], [2], [0]]) (![[2], [0], [1], [0, 0], [0, 0, 0, 1, 0, 1], [2, 2], [0, 0, 0, 1, 1, 0], [1, 2, 1, 2]]) (by decide +kernel) (by decide +kernel)

private def e58_1 : Fin 6 → SylowModel := ![decode 0, decode 636, decode 212, decode 2048, decode 684, decode 596]
set_option maxHeartbeats 1600000 in
private theorem edgeEq58_1 : binaryFamily s58 (s58 0) (![true, false, false]) = e58_1 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert58_1 : Subgroup.closure (Set.range e58_1) ≤ character.ker := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨j, rfl⟩
  exact (show ∀ j, e58_1 j ∈ character.ker from by decide +kernel) j

private def e58_2 : Fin 6 → SylowModel := ![decode 1024, decode 0, decode 212, decode 2000, decode 640, decode 84]
set_option maxHeartbeats 1600000 in
private theorem edgeEq58_2 : binaryFamily s58 (s58 1) (![false, true, false]) = e58_2 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert58_2 : Represented smallParityCensusNode (Subgroup.closure (Set.range e58_2)) := by
  refine ⟨86, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node86]
  exact closure_eq_words _ o86 (![[1], [], [0, 2], [0, 0, 2, 1], [4, 6], [0, 2, 4, 5]]) (![[0, 0, 0, 3, 5], [0], [0, 0, 0, 2, 3, 2], [0, 0], [2, 5], [2, 2], [2, 4, 5]]) (by decide +kernel) (by decide +kernel)

private def e58_3 : Fin 6 → SylowModel := ![decode 0, decode 3708, decode 212, decode 2048, decode 1708, decode 596]
set_option maxHeartbeats 1600000 in
private theorem edgeEq58_3 : binaryFamily s58 (s58 0) (![true, true, false]) = e58_3 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert58_3 : Represented smallParityCensusNode (Subgroup.closure (Set.range e58_3)) := by
  refine ⟨92, root 1 * root 2 * root 4 * root 5 * root 7 * root 9, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node92]
  exact closure_eq_words _ o92 (![[], [1, 3, 2, 4], [0], [2, 3], [2, 1, 5], [0, 4, 5]]) (![[2], [1, 2, 3, 5], [4, 3, 4], [1, 1, 1, 4], [2, 5], [2, 2], [1, 1, 1, 1]]) (by decide +kernel) (by decide +kernel)

private def e58_4 : Fin 6 → SylowModel := ![decode 1024, decode 636, decode 0, decode 1664, decode 764, decode 768]
set_option maxHeartbeats 1600000 in
private theorem edgeEq58_4 : binaryFamily s58 (s58 2) (![false, false, true]) = e58_4 := by decide +kernel
private def a58_4 (k : Fin 128) : SylowModel :=
  decode ((#[0, 1024, 2048, 764, 384, 768, 512, 3072, 1836, 1152, 1792, 1536, 2172, 2432, 2816, 2560, 892, 508, 252, 464, 640, 896, 256, 3244, 3200, 3840, 3584, 1964, 1068, 1324, 1872, 1920, 1664, 1280, 2556, 2940, 2684, 2256, 2688, 2944, 2304, 300, 124, 380, 1020, 80, 720, 976, 128, 3116, 4012, 3756, 3664, 3968, 3712, 3328, 1660, 1196, 1452, 1580, 2000, 1104, 1360, 1408, 2732, 2812, 3068, 2428, 2384, 3024, 2768, 2176, 172, 556, 812, 636, 848, 592, 208, 3324, 3884, 3628, 3500, 3792, 3408, 3152, 3456, 1788, 1404, 1148, 1708, 1232, 1488, 1616, 2860, 2476, 2220, 2300, 2640, 2896, 2512, 940, 684, 44, 336, 3196, 4092, 3836, 3372, 3536, 3280, 3920, 1532, 1276, 1916, 1744, 2092, 2348, 2988, 2128, 428, 3964, 3708, 3580, 4048, 2044, 2604, 3452] : Array ℕ).getD k.val 0)
private def next58_4 (k : Fin 128) (j : Fin 6) : Fin 128 :=
  Fin.ofNat 128 (((#[#[1, 75, 0, 32, 3, 5],
    #[2, 90, 1, 39, 8, 10],
    #[7, 97, 2, 54, 12, 14],
    #[87, 6, 3, 89, 20, 17],
    #[63, 44, 4, 10, 16, 20],
    #[10, 43, 5, 63, 17, 0],
    #[11, 42, 6, 9, 18, 22],
    #[0, 108, 7, 21, 23, 25],
    #[94, 11, 8, 96, 31, 28],
    #[71, 59, 9, 14, 27, 31],
    #[14, 58, 10, 71, 28, 1],
    #[15, 57, 11, 13, 29, 33],
    #[105, 15, 12, 107, 38, 35],
    #[86, 67, 13, 25, 34, 38],
    #[25, 66, 14, 86, 35, 2],
    #[26, 65, 15, 24, 36, 40],
    #[114, 21, 16, 112, 5, 42],
    #[112, 22, 17, 114, 4, 3],
    #[113, 0, 18, 56, 48, 44],
    #[92, 72, 19, 30, 103, 46],
    #[32, 18, 20, 1, 42, 4],
    #[31, 17, 21, 33, 43, 48],
    #[33, 16, 22, 31, 44, 6],
    #[72, 26, 23, 74, 53, 50],
    #[48, 82, 24, 5, 49, 53],
    #[5, 81, 25, 48, 50, 7],
    #[6, 80, 26, 4, 51, 55],
    #[118, 32, 27, 116, 10, 57],
    #[116, 33, 28, 118, 9, 8],
    #[117, 1, 29, 64, 63, 59],
    #[99, 87, 30, 37, 114, 61],
    #[39, 29, 31, 2, 57, 9],
    #[38, 28, 32, 40, 58, 63],
    #[40, 27, 33, 38, 59, 11],
    #[123, 39, 34, 121, 14, 65],
    #[121, 40, 35, 123, 13, 12],
    #[122, 2, 36, 79, 71, 67],
    #[110, 94, 37, 52, 118, 69],
    #[54, 36, 38, 7, 65, 13],
    #[53, 35, 39, 55, 66, 71],
    #[55, 34, 40, 53, 67, 15],
    #[29, 46, 41, 27, 77, 73],
    #[89, 48, 42, 87, 0, 16],
    #[88, 4, 43, 125, 22, 75],
    #[125, 5, 44, 88, 21, 18],
    #[61, 41, 45, 115, 120, 76],
    #[115, 101, 46, 61, 74, 19],
    #[60, 102, 47, 62, 73, 78],
    #[9, 3, 48, 11, 75, 21],
    #[103, 54, 49, 101, 25, 80],
    #[101, 55, 50, 103, 24, 23],
    #[102, 7, 51, 41, 86, 82],
    #[77, 105, 52, 19, 123, 84],
    #[21, 51, 53, 0, 80, 24],
    #[20, 50, 54, 22, 81, 86],
    #[22, 49, 55, 20, 82, 26],
    #[36, 61, 56, 34, 92, 88],
    #[96, 63, 57, 94, 1, 27],
    #[95, 9, 58, 126, 33, 90],
    #[126, 10, 59, 95, 32, 29],
    #[69, 56, 60, 119, 125, 91],
    #[119, 112, 61, 69, 89, 30],
    #[68, 113, 62, 70, 88, 93],
    #[13, 8, 63, 15, 90, 32],
    #[51, 69, 64, 49, 99, 95],
    #[107, 71, 65, 105, 2, 34],
    #[106, 13, 66, 127, 40, 97],
    #[127, 14, 67, 106, 39, 36],
    #[84, 64, 68, 124, 126, 98],
    #[124, 116, 69, 84, 96, 37],
    #[83, 117, 70, 85, 95, 100],
    #[24, 12, 71, 26, 97, 39],
    #[57, 76, 72, 59, 47, 101],
    #[59, 19, 73, 57, 104, 41],
    #[8, 78, 74, 58, 45, 103],
    #[56, 20, 75, 113, 6, 43],
    #[30, 73, 76, 92, 102, 45],
    #[93, 74, 77, 91, 101, 104],
    #[91, 120, 78, 93, 41, 47],
    #[18, 84, 79, 16, 110, 106],
    #[74, 86, 80, 72, 7, 49],
    #[73, 24, 81, 120, 55, 108],
    #[120, 25, 82, 73, 54, 51],
    #[46, 79, 83, 104, 127, 109],
    #[104, 121, 84, 46, 107, 52],
    #[45, 122, 85, 47, 106, 111],
    #[4, 23, 86, 6, 108, 54],
    #[65, 91, 87, 67, 62, 112],
    #[67, 30, 88, 65, 115, 56],
    #[12, 93, 89, 66, 60, 114],
    #[64, 31, 90, 117, 11, 58],
    #[37, 88, 91, 99, 113, 60],
    #[100, 89, 92, 98, 112, 115],
    #[98, 125, 93, 100, 56, 62],
    #[80, 98, 94, 82, 70, 116],
    #[82, 37, 95, 80, 119, 64],
    #[23, 100, 96, 81, 68, 118],
    #[79, 38, 97, 122, 15, 66],
    #[52, 95, 98, 110, 117, 68],
    #[111, 96, 99, 109, 116, 119],
    #[109, 126, 100, 111, 64, 70],
    #[27, 45, 101, 29, 78, 72],
    #[90, 104, 102, 28, 19, 120],
    #[28, 47, 103, 90, 76, 74],
    #[62, 103, 104, 60, 72, 77],
    #[42, 109, 105, 44, 85, 121],
    #[44, 52, 106, 42, 124, 79],
    #[3, 111, 107, 43, 83, 123],
    #[41, 53, 108, 102, 26, 81],
    #[19, 106, 109, 77, 122, 83],
    #[78, 107, 110, 76, 121, 124],
    #[76, 127, 111, 78, 79, 85],
    #[34, 60, 112, 36, 93, 87],
    #[97, 115, 113, 35, 30, 125],
    #[35, 62, 114, 97, 91, 89],
    #[70, 114, 115, 68, 87, 92],
    #[49, 68, 116, 51, 100, 94],
    #[108, 119, 117, 50, 37, 126],
    #[50, 70, 118, 108, 98, 96],
    #[85, 118, 119, 83, 94, 99],
    #[58, 77, 120, 8, 46, 102],
    #[16, 83, 121, 18, 111, 105],
    #[75, 124, 122, 17, 52, 127],
    #[17, 85, 123, 75, 109, 107],
    #[47, 123, 124, 45, 105, 110],
    #[66, 92, 125, 12, 61, 113],
    #[81, 99, 126, 23, 69, 117],
    #[43, 110, 127, 3, 84, 122]] : Array (Array ℕ)).getD k.val #[]).getD j.val 0)
private def prev58_4 (k : Fin 128) (j : Fin 6) : Fin 128 :=
  Fin.ofNat 128 (((#[#[7, 18, 0, 53, 42, 5],
    #[0, 29, 1, 20, 57, 10],
    #[1, 36, 2, 31, 65, 14],
    #[107, 48, 3, 127, 0, 17],
    #[86, 43, 4, 26, 17, 20],
    #[25, 44, 5, 24, 16, 0],
    #[26, 3, 6, 86, 75, 22],
    #[2, 51, 7, 38, 80, 25],
    #[74, 63, 8, 120, 1, 28],
    #[48, 58, 9, 6, 28, 31],
    #[5, 59, 10, 4, 27, 1],
    #[6, 8, 11, 48, 90, 33],
    #[89, 71, 12, 125, 2, 35],
    #[63, 66, 13, 11, 35, 38],
    #[10, 67, 14, 9, 34, 2],
    #[11, 12, 15, 63, 97, 40],
    #[121, 22, 16, 79, 4, 42],
    #[123, 21, 17, 122, 5, 3],
    #[79, 20, 18, 121, 6, 44],
    #[109, 73, 19, 52, 102, 46],
    #[54, 75, 20, 55, 3, 4],
    #[53, 16, 21, 7, 44, 48],
    #[55, 17, 22, 54, 43, 6],
    #[96, 86, 23, 126, 7, 50],
    #[71, 81, 24, 15, 50, 53],
    #[14, 82, 25, 13, 49, 7],
    #[15, 23, 26, 71, 108, 55],
    #[101, 33, 27, 41, 9, 57],
    #[103, 32, 28, 102, 10, 8],
    #[41, 31, 29, 101, 11, 59],
    #[76, 88, 30, 19, 113, 61],
    #[21, 90, 31, 22, 8, 9],
    #[20, 27, 32, 0, 59, 63],
    #[22, 28, 33, 21, 58, 11],
    #[112, 40, 34, 56, 13, 65],
    #[114, 39, 35, 113, 14, 12],
    #[56, 38, 36, 112, 15, 67],
    #[91, 95, 37, 30, 117, 69],
    #[32, 97, 38, 33, 12, 13],
    #[31, 34, 39, 1, 67, 71],
    #[33, 35, 40, 32, 66, 15],
    #[108, 45, 41, 51, 78, 73],
    #[105, 6, 42, 106, 20, 16],
    #[127, 5, 43, 107, 21, 75],
    #[106, 4, 44, 105, 22, 18],
    #[85, 101, 45, 124, 74, 76],
    #[83, 41, 46, 84, 120, 19],
    #[124, 103, 47, 85, 72, 78],
    #[24, 42, 48, 25, 18, 21],
    #[116, 55, 49, 64, 24, 80],
    #[118, 54, 50, 117, 25, 23],
    #[64, 53, 51, 116, 26, 82],
    #[98, 106, 52, 37, 122, 84],
    #[39, 108, 53, 40, 23, 24],
    #[38, 49, 54, 2, 82, 86],
    #[40, 50, 55, 39, 81, 26],
    #[75, 60, 56, 18, 93, 88],
    #[72, 11, 57, 73, 31, 27],
    #[120, 10, 58, 74, 32, 90],
    #[73, 9, 59, 72, 33, 29],
    #[47, 112, 60, 104, 89, 91],
    #[45, 56, 61, 46, 125, 30],
    #[104, 114, 62, 47, 87, 93],
    #[4, 57, 63, 5, 29, 32],
    #[90, 68, 64, 29, 100, 95],
    #[87, 15, 65, 88, 38, 34],
    #[125, 14, 66, 89, 39, 97],
    #[88, 13, 67, 87, 40, 36],
    #[62, 116, 68, 115, 96, 98],
    #[60, 64, 69, 61, 126, 37],
    #[115, 118, 70, 62, 94, 100],
    #[9, 65, 71, 10, 36, 39],
    #[23, 19, 72, 80, 104, 101],
    #[81, 76, 73, 82, 47, 41],
    #[80, 77, 74, 23, 46, 103],
    #[122, 0, 75, 123, 48, 43],
    #[111, 72, 76, 110, 103, 45],
    #[52, 120, 77, 109, 41, 104],
    #[110, 74, 78, 111, 101, 47],
    #[97, 83, 79, 36, 111, 106],
    #[94, 26, 80, 95, 53, 49],
    #[126, 25, 81, 96, 54, 108],
    #[95, 24, 82, 94, 55, 51],
    #[70, 121, 83, 119, 107, 109],
    #[68, 79, 84, 69, 127, 52],
    #[119, 123, 85, 70, 105, 111],
    #[13, 80, 86, 14, 51, 54],
    #[3, 30, 87, 42, 115, 112],
    #[43, 91, 88, 44, 62, 56],
    #[42, 92, 89, 3, 61, 114],
    #[102, 1, 90, 103, 63, 58],
    #[78, 87, 91, 77, 114, 60],
    #[19, 125, 92, 76, 56, 115],
    #[77, 89, 93, 78, 112, 62],
    #[8, 37, 94, 57, 119, 116],
    #[58, 98, 95, 59, 70, 64],
    #[57, 99, 96, 8, 69, 118],
    #[113, 2, 97, 114, 71, 66],
    #[93, 94, 98, 92, 118, 68],
    #[30, 126, 99, 91, 64, 119],
    #[92, 96, 100, 93, 116, 70],
    #[50, 46, 101, 49, 77, 72],
    #[51, 47, 102, 108, 76, 120],
    #[49, 104, 103, 50, 19, 74],
    #[84, 102, 104, 83, 73, 77],
    #[12, 52, 105, 65, 124, 121],
    #[66, 109, 106, 67, 85, 79],
    #[65, 110, 107, 12, 84, 123],
    #[117, 7, 108, 118, 86, 81],
    #[100, 105, 109, 99, 123, 83],
    #[37, 127, 110, 98, 79, 124],
    #[99, 107, 111, 100, 121, 85],
    #[17, 61, 112, 16, 92, 87],
    #[18, 62, 113, 75, 91, 125],
    #[16, 115, 114, 17, 30, 89],
    #[46, 113, 115, 45, 88, 92],
    #[28, 69, 116, 27, 99, 94],
    #[29, 70, 117, 90, 98, 126],
    #[27, 119, 118, 28, 37, 96],
    #[61, 117, 119, 60, 95, 99],
    #[82, 78, 120, 81, 45, 102],
    #[35, 84, 121, 34, 110, 105],
    #[36, 85, 122, 97, 109, 127],
    #[34, 124, 123, 35, 52, 107],
    #[69, 122, 124, 68, 106, 110],
    #[44, 93, 125, 43, 60, 113],
    #[59, 100, 126, 58, 68, 117],
    #[67, 111, 127, 66, 83, 122]] : Array (Array ℕ)).getD k.val #[]).getD j.val 0)
set_option maxHeartbeats 1600000 in
private theorem cert58_4 : ∃ c, c ∈ Subgroup.centralizer (Subgroup.closure (Set.range e58_4) : Set SylowModel) ∧ c ∉ Subgroup.closure (Set.range e58_4) := by
  refine ⟨rootOne ^ 2 * root 2 * root 4 * root 8, centralizes_generators e58_4 _ (by decide +kernel), ?_⟩
  exact outside_of_table e58_4 a58_4 0 next58_4 prev58_4
    (by decide +kernel) (by decide +kernel) (by decide +kernel) _ (by decide +kernel)

private def e58_5 : Fin 6 → SylowModel := ![decode 0, decode 636, decode 3284, decode 2048, decode 684, decode 1620]
set_option maxHeartbeats 1600000 in
private theorem edgeEq58_5 : binaryFamily s58 (s58 0) (![true, false, true]) = e58_5 := by decide +kernel
private def a58_5 (k : Fin 128) : SylowModel :=
  decode ((#[0, 2048, 764, 384, 768, 512, 2172, 2432, 2816, 2560, 892, 508, 252, 464, 640, 896, 256, 2556, 2940, 2684, 2256, 2688, 2944, 2304, 300, 124, 380, 1020, 80, 720, 976, 128, 1028, 2732, 2812, 3068, 2428, 2384, 3024, 2768, 2176, 172, 556, 812, 636, 848, 592, 208, 3076, 1320, 1156, 1796, 1540, 2860, 2476, 2220, 2300, 2640, 2896, 2512, 940, 684, 44, 336, 3752, 3204, 3844, 3588, 1448, 1576, 1832, 1876, 1924, 1668, 1284, 2092, 2348, 2988, 2128, 428, 3624, 3496, 3240, 3668, 3972, 3716, 3332, 1144, 1704, 1960, 1064, 2004, 1108, 1364, 1412, 2604, 3832, 3368, 3112, 4008, 3796, 3412, 3156, 3460, 1272, 1912, 1656, 1192, 1236, 1492, 1620, 3704, 3576, 3320, 3880, 3540, 3284, 3924, 2040, 1784, 1400, 1748, 3448, 3192, 4088, 4052, 1528, 3960] : Array ℕ).getD k.val 0)
private def next58_5 (k : Fin 128) (j : Fin 6) : Fin 128 :=
  Fin.ofNat 128 (((#[#[0, 44, 116, 1, 61, 110],
    #[1, 56, 109, 0, 76, 117],
    #[2, 5, 99, 34, 47, 49],
    #[3, 27, 101, 7, 43, 91],
    #[4, 26, 125, 8, 79, 93],
    #[5, 25, 100, 9, 41, 92],
    #[6, 9, 90, 25, 59, 64],
    #[7, 36, 92, 3, 55, 100],
    #[8, 35, 121, 4, 95, 102],
    #[9, 34, 91, 5, 53, 101],
    #[10, 15, 80, 18, 63, 107],
    #[11, 16, 82, 17, 30, 69],
    #[12, 0, 81, 56, 29, 70],
    #[13, 41, 48, 59, 25, 73],
    #[14, 12, 83, 21, 62, 108],
    #[15, 11, 117, 22, 24, 109],
    #[16, 10, 115, 23, 60, 71],
    #[17, 22, 68, 11, 78, 114],
    #[18, 23, 70, 10, 39, 81],
    #[19, 1, 69, 44, 38, 82],
    #[20, 53, 32, 47, 34, 85],
    #[21, 19, 71, 14, 77, 115],
    #[22, 18, 110, 15, 33, 116],
    #[23, 17, 108, 16, 75, 83],
    #[24, 29, 122, 76, 0, 118],
    #[25, 31, 97, 6, 46, 89],
    #[26, 3, 98, 36, 45, 88],
    #[27, 4, 64, 35, 13, 90],
    #[28, 24, 103, 78, 11, 51],
    #[29, 60, 66, 39, 10, 94],
    #[30, 61, 67, 38, 44, 50],
    #[31, 2, 102, 40, 42, 121],
    #[32, 107, 28, 48, 119, 38],
    #[33, 38, 118, 61, 1, 122],
    #[34, 40, 88, 2, 58, 98],
    #[35, 7, 89, 27, 57, 97],
    #[36, 8, 49, 26, 20, 99],
    #[37, 33, 94, 63, 18, 66],
    #[38, 75, 51, 30, 17, 103],
    #[39, 76, 52, 29, 56, 65],
    #[40, 6, 93, 31, 54, 125],
    #[41, 45, 113, 55, 3, 106],
    #[42, 13, 111, 95, 4, 104],
    #[43, 47, 127, 53, 5, 126],
    #[44, 14, 114, 19, 28, 68],
    #[45, 42, 85, 58, 2, 32],
    #[46, 43, 84, 57, 27, 74],
    #[47, 79, 86, 20, 26, 72],
    #[48, 114, 37, 32, 123, 29],
    #[49, 52, 11, 97, 110, 19],
    #[50, 90, 47, 65, 106, 58],
    #[51, 89, 45, 66, 126, 20],
    #[52, 88, 46, 67, 104, 59],
    #[53, 57, 106, 43, 7, 113],
    #[54, 20, 104, 79, 8, 111],
    #[55, 59, 126, 41, 9, 127],
    #[56, 21, 107, 12, 37, 80],
    #[57, 54, 73, 46, 6, 48],
    #[58, 55, 72, 45, 36, 86],
    #[59, 95, 74, 13, 35, 84],
    #[60, 28, 124, 77, 14, 120],
    #[61, 63, 96, 33, 15, 87],
    #[62, 30, 123, 75, 16, 119],
    #[63, 62, 65, 37, 12, 52],
    #[64, 67, 18, 88, 117, 12],
    #[65, 99, 59, 50, 113, 46],
    #[66, 98, 57, 51, 127, 13],
    #[67, 97, 58, 52, 111, 47],
    #[68, 73, 26, 81, 121, 34],
    #[69, 74, 2, 80, 93, 36],
    #[70, 32, 27, 114, 92, 6],
    #[71, 104, 5, 117, 88, 7],
    #[72, 70, 30, 84, 120, 78],
    #[73, 69, 29, 85, 87, 37],
    #[74, 68, 63, 86, 118, 39],
    #[75, 37, 120, 62, 21, 124],
    #[76, 78, 87, 24, 22, 96],
    #[77, 39, 119, 60, 23, 123],
    #[78, 77, 50, 28, 19, 67],
    #[79, 46, 112, 54, 31, 105],
    #[80, 85, 35, 69, 125, 25],
    #[81, 86, 6, 68, 102, 27],
    #[82, 48, 36, 107, 101, 2],
    #[83, 111, 9, 110, 97, 3],
    #[84, 82, 39, 72, 124, 63],
    #[85, 81, 38, 73, 96, 28],
    #[86, 80, 78, 74, 122, 30],
    #[87, 92, 79, 123, 32, 95],
    #[88, 94, 44, 64, 109, 17],
    #[89, 50, 10, 99, 108, 56],
    #[90, 51, 12, 98, 71, 18],
    #[91, 87, 14, 125, 69, 23],
    #[92, 118, 16, 102, 68, 21],
    #[93, 119, 0, 101, 107, 22],
    #[94, 49, 13, 103, 105, 57],
    #[95, 58, 105, 42, 40, 112],
    #[96, 101, 95, 119, 48, 79],
    #[97, 103, 56, 49, 116, 10],
    #[98, 65, 17, 90, 115, 44],
    #[99, 66, 19, 89, 83, 11],
    #[100, 96, 21, 121, 81, 16],
    #[101, 122, 23, 93, 80, 14],
    #[102, 123, 1, 92, 114, 15],
    #[103, 64, 20, 94, 112, 45],
    #[104, 108, 24, 113, 50, 33],
    #[105, 71, 61, 127, 51, 76],
    #[106, 110, 60, 111, 52, 75],
    #[107, 72, 25, 82, 91, 35],
    #[108, 105, 3, 116, 49, 9],
    #[109, 106, 31, 115, 90, 8],
    #[110, 126, 4, 83, 89, 40],
    #[111, 115, 33, 106, 65, 24],
    #[112, 83, 76, 126, 66, 61],
    #[113, 117, 75, 104, 67, 60],
    #[114, 84, 34, 70, 100, 26],
    #[115, 112, 7, 109, 64, 5],
    #[116, 113, 40, 108, 99, 4],
    #[117, 127, 8, 71, 98, 31],
    #[118, 91, 42, 124, 72, 54],
    #[119, 121, 43, 96, 73, 55],
    #[120, 93, 41, 122, 74, 53],
    #[121, 120, 15, 100, 70, 1],
    #[122, 100, 54, 120, 84, 42],
    #[123, 125, 55, 87, 85, 43],
    #[124, 102, 53, 118, 86, 41],
    #[125, 124, 22, 91, 82, 0],
    #[126, 109, 62, 112, 94, 77],
    #[127, 116, 77, 105, 103, 62]] : Array (Array ℕ)).getD k.val #[]).getD j.val 0)
private def prev58_5 (k : Fin 128) (j : Fin 6) : Fin 128 :=
  Fin.ofNat 128 (((#[#[0, 12, 93, 1, 24, 125],
    #[1, 19, 102, 0, 33, 121],
    #[2, 31, 69, 34, 45, 82],
    #[3, 26, 108, 7, 41, 83],
    #[4, 27, 110, 8, 42, 116],
    #[5, 2, 71, 9, 43, 115],
    #[6, 40, 81, 25, 57, 70],
    #[7, 35, 115, 3, 53, 71],
    #[8, 36, 117, 4, 54, 109],
    #[9, 6, 83, 5, 55, 108],
    #[10, 16, 89, 18, 29, 97],
    #[11, 15, 49, 17, 28, 99],
    #[12, 14, 90, 56, 63, 64],
    #[13, 42, 94, 59, 27, 66],
    #[14, 44, 91, 21, 60, 101],
    #[15, 10, 121, 22, 61, 102],
    #[16, 11, 92, 23, 62, 100],
    #[17, 23, 98, 11, 38, 88],
    #[18, 22, 64, 10, 37, 90],
    #[19, 21, 99, 44, 78, 49],
    #[20, 54, 103, 47, 36, 51],
    #[21, 56, 100, 14, 75, 92],
    #[22, 17, 125, 15, 76, 93],
    #[23, 18, 101, 16, 77, 91],
    #[24, 28, 104, 76, 15, 111],
    #[25, 5, 107, 6, 13, 80],
    #[26, 4, 68, 36, 47, 114],
    #[27, 3, 70, 35, 46, 81],
    #[28, 60, 32, 78, 44, 85],
    #[29, 24, 73, 39, 12, 48],
    #[30, 62, 72, 38, 11, 86],
    #[31, 25, 109, 40, 79, 117],
    #[32, 70, 20, 48, 87, 45],
    #[33, 37, 111, 61, 22, 104],
    #[34, 9, 114, 2, 20, 68],
    #[35, 8, 80, 27, 59, 107],
    #[36, 7, 82, 26, 58, 69],
    #[37, 75, 48, 63, 56, 73],
    #[38, 33, 85, 30, 19, 32],
    #[39, 77, 84, 29, 18, 74],
    #[40, 34, 116, 31, 95, 110],
    #[41, 13, 120, 55, 5, 124],
    #[42, 45, 118, 95, 31, 122],
    #[43, 46, 119, 53, 3, 123],
    #[44, 0, 88, 19, 30, 98],
    #[45, 41, 51, 58, 26, 103],
    #[46, 79, 52, 57, 25, 65],
    #[47, 43, 50, 20, 2, 67],
    #[48, 82, 13, 32, 96, 57],
    #[49, 94, 36, 97, 108, 2],
    #[50, 89, 78, 65, 104, 30],
    #[51, 90, 38, 66, 105, 28],
    #[52, 49, 39, 67, 106, 63],
    #[53, 20, 124, 43, 9, 120],
    #[54, 57, 122, 79, 40, 118],
    #[55, 58, 123, 41, 7, 119],
    #[56, 1, 97, 12, 39, 89],
    #[57, 53, 66, 46, 35, 94],
    #[58, 95, 67, 45, 34, 50],
    #[59, 55, 65, 13, 6, 52],
    #[60, 29, 106, 77, 16, 113],
    #[61, 30, 105, 33, 0, 112],
    #[62, 63, 126, 75, 14, 127],
    #[63, 61, 74, 37, 10, 84],
    #[64, 103, 27, 88, 115, 6],
    #[65, 98, 63, 50, 111, 39],
    #[66, 99, 29, 51, 112, 37],
    #[67, 64, 30, 52, 113, 78],
    #[68, 74, 17, 81, 92, 44],
    #[69, 73, 19, 80, 91, 11],
    #[70, 72, 18, 114, 121, 12],
    #[71, 105, 21, 117, 90, 16],
    #[72, 107, 58, 84, 118, 47],
    #[73, 68, 57, 85, 119, 13],
    #[74, 69, 59, 86, 120, 46],
    #[75, 38, 113, 62, 23, 106],
    #[76, 39, 112, 24, 1, 105],
    #[77, 78, 127, 60, 21, 126],
    #[78, 76, 86, 28, 17, 72],
    #[79, 47, 87, 54, 4, 96],
    #[80, 86, 10, 69, 101, 56],
    #[81, 85, 12, 68, 100, 18],
    #[82, 84, 11, 107, 125, 19],
    #[83, 112, 14, 110, 99, 23],
    #[84, 114, 46, 72, 122, 59],
    #[85, 80, 45, 73, 123, 20],
    #[86, 81, 47, 74, 124, 58],
    #[87, 91, 76, 123, 73, 61],
    #[88, 52, 34, 64, 71, 26],
    #[89, 51, 35, 99, 110, 25],
    #[90, 50, 6, 98, 109, 27],
    #[91, 118, 9, 125, 107, 3],
    #[92, 87, 7, 102, 70, 5],
    #[93, 120, 40, 101, 69, 4],
    #[94, 88, 37, 103, 126, 29],
    #[95, 59, 96, 42, 8, 87],
    #[96, 100, 61, 119, 85, 76],
    #[97, 67, 25, 49, 83, 35],
    #[98, 66, 26, 90, 117, 34],
    #[99, 65, 2, 89, 116, 36],
    #[100, 122, 5, 121, 114, 7],
    #[101, 96, 3, 93, 82, 9],
    #[102, 124, 31, 92, 81, 8],
    #[103, 97, 28, 94, 127, 38],
    #[104, 71, 54, 113, 52, 42],
    #[105, 108, 95, 127, 94, 79],
    #[106, 109, 53, 111, 50, 41],
    #[107, 32, 56, 82, 93, 10],
    #[108, 104, 23, 116, 89, 14],
    #[109, 126, 1, 115, 88, 15],
    #[110, 106, 22, 83, 49, 0],
    #[111, 83, 42, 106, 67, 54],
    #[112, 115, 79, 126, 103, 95],
    #[113, 116, 41, 104, 65, 53],
    #[114, 48, 44, 70, 102, 17],
    #[115, 111, 16, 109, 98, 21],
    #[116, 127, 0, 108, 97, 22],
    #[117, 113, 15, 71, 64, 1],
    #[118, 92, 33, 124, 74, 24],
    #[119, 93, 77, 96, 32, 62],
    #[120, 121, 75, 122, 72, 60],
    #[121, 119, 8, 100, 68, 31],
    #[122, 101, 24, 120, 86, 33],
    #[123, 102, 62, 87, 48, 77],
    #[124, 125, 60, 118, 84, 75],
    #[125, 123, 4, 91, 80, 40],
    #[126, 110, 55, 112, 51, 43],
    #[127, 117, 43, 105, 66, 55]] : Array (Array ℕ)).getD k.val #[]).getD j.val 0)
set_option maxHeartbeats 1600000 in
private theorem cert58_5 : ∃ c, c ∈ Subgroup.centralizer (Subgroup.closure (Set.range e58_5) : Set SylowModel) ∧ c ∉ Subgroup.closure (Set.range e58_5) := by
  refine ⟨rootOne ^ 2 * root 2 * root 4 * root 7, centralizes_generators e58_5 _ (by decide +kernel), ?_⟩
  exact outside_of_table e58_5 a58_5 0 next58_5 prev58_5
    (by decide +kernel) (by decide +kernel) (by decide +kernel) _ (by decide +kernel)

private def e58_6 : Fin 6 → SylowModel := ![decode 1024, decode 0, decode 296, decode 2000, decode 640, decode 808]
set_option maxHeartbeats 1600000 in
private theorem edgeEq58_6 : binaryFamily s58 (s58 1) (![false, true, true]) = e58_6 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert58_6 : Represented smallParityCensusNode (Subgroup.closure (Set.range e58_6)) := by
  refine ⟨79, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node79]
  exact closure_eq_words _ o79 (![[1], [], [0], [3, 1], [5, 6], [0, 4]]) (![[2], [0], [0, 0], [0, 3, 3, 3], [2, 2, 2, 5], [2, 2, 4], [2, 2]]) (by decide +kernel) (by decide +kernel)

private def e58_7 : Fin 6 → SylowModel := ![decode 0, decode 3708, decode 3284, decode 2048, decode 1708, decode 1620]
set_option maxHeartbeats 1600000 in
private theorem edgeEq58_7 : binaryFamily s58 (s58 0) (![true, true, true]) = e58_7 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert58_7 : Represented smallParityCensusNode (Subgroup.closure (Set.range e58_7)) := by
  refine ⟨80, root 1 * root 2 * root 4 * root 5 * root 7 * root 9, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node80]
  exact closure_eq_words _ o80 (![[], [2, 3, 1], [0, 1, 2, 3], [3, 2, 4], [3, 1, 6], [0, 4, 5, 1]]) (![[2, 4], [1, 2, 2], [1, 1, 1, 4], [1, 1, 2, 2], [2, 3, 5, 3], [4, 1], [1, 1, 1, 1]]) (by decide +kernel) (by decide +kernel)

private def s59 : Fin 2 → SylowModel := ![rootOne * root 0 * root 1 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8 * root 9, rootOne * root 0 * root 1 * root 2 * root 3 * root 4 * root 6 * root 8 * root 9]
set_option maxHeartbeats 1600000 in
private theorem gen59 : Subgroup.closure (Set.range s59) = smallParityCensusNode 59 := by
  rw [node59]
  exact closure_eq_words s59 o59 (![[0], [1]]) (![[0], [1], [0, 0], [1, 1, 0, 0], [0, 0, 0, 0], [0, 0, 1, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 1, 1, 1], [0, 0, 0, 0, 0, 0, 0, 0]]) (by decide +kernel) (by decide +kernel)

private def e59_1 : Fin 4 → SylowModel := ![decode 0, decode 3705, decode 2522, decode 3401]
set_option maxHeartbeats 1600000 in
private theorem edgeEq59_1 : binaryFamily s59 (s59 0) (![true, false]) = e59_1 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert59_1 : Represented smallParityCensusNode (Subgroup.closure (Set.range e59_1)) := by
  refine ⟨68, root 1 * root 3 * root 5 * root 6 * root 7 * root 9, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node68]
  exact closure_eq_words _ o68 (![[], [2, 0, 3], [2, 1, 3, 4], [0, 6]]) (![[2, 2, 2, 2, 3], [3, 3], [3, 2, 3], [3, 3, 3, 3], [1, 2, 2, 3, 2], [1, 2, 3, 2, 2], [2, 2, 2, 2]]) (by decide +kernel) (by decide +kernel)

private def e59_2 : Fin 4 → SylowModel := ![decode 3073, decode 0, decode 3889, decode 2218]
set_option maxHeartbeats 1600000 in
private theorem edgeEq59_2 : binaryFamily s59 (s59 1) (![false, true]) = e59_2 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert59_2 : Represented smallParityCensusNode (Subgroup.closure (Set.range e59_2)) := by
  refine ⟨67, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node67]
  exact closure_eq_words _ o67 (![[0], [], [2, 0, 3], [1, 2, 3, 6]]) (![[0], [0, 0], [0, 0, 3], [0, 3, 2], [0, 3, 3, 2, 3], [0, 3, 2, 3, 3], [3, 3, 3, 3]]) (by decide +kernel) (by decide +kernel)

private def e59_3 : Fin 4 → SylowModel := ![decode 0, decode 728, decode 2522, decode 3058]
set_option maxHeartbeats 1600000 in
private theorem edgeEq59_3 : binaryFamily s59 (s59 0) (![true, true]) = e59_3 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert59_3 : Subgroup.closure (Set.range e59_3) ≤ character.ker := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨j, rfl⟩
  exact (show ∀ j, e59_3 j ∈ character.ker from by decide +kernel) j

private def s60 : Fin 3 → SylowModel := ![root 6, rootOne * root 0 * root 1 * root 2 * root 4 * root 5 * root 6 * root 7 * root 8 * root 9, rootOne * root 0 * root 1 * root 2 * root 3 * root 7 * root 8 * root 9]
set_option maxHeartbeats 1600000 in
private theorem gen60 : Subgroup.closure (Set.range s60) = smallParityCensusNode 60 := by
  rw [node60]
  exact closure_eq_words s60 o60 (![[3], [0], [1]]) (![[1], [2], [1, 1], [0], [1, 1, 1, 1], [1, 1, 2, 2], [0, 1, 0, 1, 2, 2], [1, 1, 1, 1, 1, 1, 1, 1]]) (by decide +kernel) (by decide +kernel)

private def e60_1 : Fin 6 → SylowModel := ![decode 0, decode 3073, decode 3881, decode 0, decode 3713, decode 4009]
set_option maxHeartbeats 1600000 in
private theorem edgeEq60_1 : binaryFamily s60 (s60 0) (![true, false, false]) = e60_1 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert60_1 : Represented smallParityCensusNode (Subgroup.closure (Set.range e60_1)) := by
  refine ⟨95, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node95]
  exact closure_eq_words _ o95 (![[], [0], [1], [], [3, 0], [1, 3, 5]]) (![[1], [2], [1, 1], [1, 1, 5, 5], [1, 1, 1, 1], [1, 1, 5, 2], [1, 1, 1, 1, 1, 1, 1, 1]]) (by decide +kernel) (by decide +kernel)

private def e60_2 : Fin 6 → SylowModel := ![decode 64, decode 0, decode 3881, decode 704, decode 2522, decode 3545]
set_option maxHeartbeats 1600000 in
private theorem edgeEq60_2 : binaryFamily s60 (s60 1) (![false, true, false]) = e60_2 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert60_2 : Represented smallParityCensusNode (Subgroup.closure (Set.range e60_2)) := by
  refine ⟨68, root 1 * root 2 * root 4 * root 5 * root 7 * root 9, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node68]
  exact closure_eq_words _ o68 (![[2], [], [1, 4, 0, 1], [2, 4, 5], [0, 3, 4, 0], [5, 0]]) (![[0, 2, 4, 0, 4], [0, 2, 2, 0], [0], [4, 4], [4, 2, 2], [0, 2, 0, 2, 4], [4, 4, 4, 4]]) (by decide +kernel) (by decide +kernel)

private def e60_3 : Fin 6 → SylowModel := ![decode 0, decode 3777, decode 3881, decode 0, decode 3137, decode 4009]
set_option maxHeartbeats 1600000 in
private theorem edgeEq60_3 : binaryFamily s60 (s60 0) (![true, true, false]) = e60_3 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert60_3 : Represented smallParityCensusNode (Subgroup.closure (Set.range e60_3)) := by
  refine ⟨96, root 4 * root 7 * root 8, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node96]
  exact closure_eq_words _ o96 (![[], [5, 0], [5, 1], [], [0, 3], [1, 3, 6]]) (![[1, 1, 2, 5, 4], [1, 1, 4, 2, 4], [1, 2, 1, 4, 2, 4], [1, 1, 5, 2], [1, 1, 1, 1], [1, 1, 5, 5], [1, 1, 1, 1, 1, 1, 1, 1]]) (by decide +kernel) (by decide +kernel)

private def e60_4 : Fin 6 → SylowModel := ![decode 64, decode 3073, decode 0, decode 192, decode 3825, decode 2922]
set_option maxHeartbeats 1600000 in
private theorem edgeEq60_4 : binaryFamily s60 (s60 2) (![false, false, true]) = e60_4 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert60_4 : Represented smallParityCensusNode (Subgroup.closure (Set.range e60_4)) := by
  refine ⟨67, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node67]
  exact closure_eq_words _ o67 (![[2, 5], [0], [], [2, 4, 6], [0, 3, 4], [3, 4, 1]]) (![[1], [1, 1], [1, 0, 1, 5], [5, 5], [1, 1, 5], [0, 1, 0, 1, 5], [5, 5, 5, 5]]) (by decide +kernel) (by decide +kernel)

private def e60_5 : Fin 6 → SylowModel := ![decode 0, decode 3073, decode 3561, decode 0, decode 3713, decode 3433]
set_option maxHeartbeats 1600000 in
private theorem edgeEq60_5 : binaryFamily s60 (s60 0) (![true, false, true]) = e60_5 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert60_5 : Represented smallParityCensusNode (Subgroup.closure (Set.range e60_5)) := by
  refine ⟨96, 1, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node96]
  exact closure_eq_words _ o96 (![[], [0], [1], [], [3, 0], [1, 3, 5]]) (![[1], [2], [1, 1], [1, 1, 5, 2], [1, 1, 1, 1], [1, 1, 5, 5], [1, 1, 1, 1, 1, 1, 1, 1]]) (by decide +kernel) (by decide +kernel)

private def e60_6 : Fin 6 → SylowModel := ![decode 64, decode 0, decode 840, decode 704, decode 2522, decode 2082]
set_option maxHeartbeats 1600000 in
private theorem edgeEq60_6 : binaryFamily s60 (s60 1) (![false, true, true]) = e60_6 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert60_6 : Subgroup.closure (Set.range e60_6) ≤ character.ker := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨j, rfl⟩
  exact (show ∀ j, e60_6 j ∈ character.ker from by decide +kernel) j

private def e60_7 : Fin 6 → SylowModel := ![decode 0, decode 3777, decode 3561, decode 0, decode 3137, decode 3433]
set_option maxHeartbeats 1600000 in
private theorem edgeEq60_7 : binaryFamily s60 (s60 0) (![true, true, true]) = e60_7 := by decide +kernel
set_option maxHeartbeats 1600000 in
private theorem cert60_7 : Represented smallParityCensusNode (Subgroup.closure (Set.range e60_7)) := by
  refine ⟨95, root 4 * root 7 * root 8, ?_⟩
  rw [MonoidHom.map_closure, ← Set.range_comp, node95]
  exact closure_eq_words _ o95 (![[], [5, 0], [5, 1], [], [0, 3], [1, 3, 6]]) (![[1, 1, 2, 2, 4], [1, 1, 4, 2, 1], [1, 2, 1, 1, 2, 4], [1, 1, 5, 5], [1, 1, 1, 1], [1, 1, 5, 2], [1, 1, 1, 1, 1, 1, 1, 1]]) (by decide +kernel) (by decide +kernel)

private def pivot29 (σ : Fin 3 → Bool) : Fin 3 := if σ 0 then 0 else if σ 1 then 1 else 2
set_option maxHeartbeats 1600000 in
private theorem step29 (H : Subgroup SylowModel) (hmax : H ⋖ smallParityCensusNode 29) (hcent : Subgroup.centralizer (H : Set SylowModel) ≤ H) (hpar : ¬ H ≤ character.ker) : Represented smallParityCensusNode H := by
  apply step_first 29 s29 gen29 pivot29 (by decide +kernel) ?_ H hmax hcent hpar
  intro σ hn
  have he : σ = ![σ 0, σ 1, σ 2] := by
    funext k
    fin_cases k <;> rfl
  rw [he] at hn ⊢
  cases h0 : σ 0 <;> cases h1 : σ 1 <;> cases h2 : σ 2
  · obtain ⟨j, hj⟩ := hn
    fin_cases j <;> simp_all
  · change let L := Subgroup.closure (Set.range (binaryFamily s29 (s29 2) (![false, false, true]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq29_4]
    exact Or.inr (Or.inr cert29_4)
  · change let L := Subgroup.closure (Set.range (binaryFamily s29 (s29 1) (![false, true, false]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq29_2]
    exact Or.inr (Or.inl cert29_2)
  · change let L := Subgroup.closure (Set.range (binaryFamily s29 (s29 1) (![false, true, true]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq29_6]
    exact Or.inr (Or.inr cert29_6)
  · change let L := Subgroup.closure (Set.range (binaryFamily s29 (s29 0) (![true, false, false]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq29_1]
    exact Or.inl cert29_1
  · change let L := Subgroup.closure (Set.range (binaryFamily s29 (s29 0) (![true, false, true]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq29_5]
    exact Or.inr (Or.inr cert29_5)
  · change let L := Subgroup.closure (Set.range (binaryFamily s29 (s29 0) (![true, true, false]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq29_3]
    exact Or.inr (Or.inl cert29_3)
  · change let L := Subgroup.closure (Set.range (binaryFamily s29 (s29 0) (![true, true, true]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq29_7]
    exact Or.inr (Or.inr cert29_7)

private def pivot30 (σ : Fin 3 → Bool) : Fin 3 := if σ 0 then 0 else if σ 1 then 1 else 2
set_option maxHeartbeats 1600000 in
private theorem step30 (H : Subgroup SylowModel) (hmax : H ⋖ smallParityCensusNode 30) (hcent : Subgroup.centralizer (H : Set SylowModel) ≤ H) (hpar : ¬ H ≤ character.ker) : Represented smallParityCensusNode H := by
  apply step_first 30 s30 gen30 pivot30 (by decide +kernel) ?_ H hmax hcent hpar
  intro σ hn
  have he : σ = ![σ 0, σ 1, σ 2] := by
    funext k
    fin_cases k <;> rfl
  rw [he] at hn ⊢
  cases h0 : σ 0 <;> cases h1 : σ 1 <;> cases h2 : σ 2
  · obtain ⟨j, hj⟩ := hn
    fin_cases j <;> simp_all
  · change let L := Subgroup.closure (Set.range (binaryFamily s30 (s30 2) (![false, false, true]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq30_4]
    exact Or.inr (Or.inr cert30_4)
  · change let L := Subgroup.closure (Set.range (binaryFamily s30 (s30 1) (![false, true, false]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq30_2]
    exact Or.inr (Or.inr cert30_2)
  · change let L := Subgroup.closure (Set.range (binaryFamily s30 (s30 1) (![false, true, true]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq30_6]
    exact Or.inr (Or.inr cert30_6)
  · change let L := Subgroup.closure (Set.range (binaryFamily s30 (s30 0) (![true, false, false]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq30_1]
    exact Or.inl cert30_1
  · change let L := Subgroup.closure (Set.range (binaryFamily s30 (s30 0) (![true, false, true]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq30_5]
    exact Or.inr (Or.inr cert30_5)
  · change let L := Subgroup.closure (Set.range (binaryFamily s30 (s30 0) (![true, true, false]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq30_3]
    exact Or.inr (Or.inr cert30_3)
  · change let L := Subgroup.closure (Set.range (binaryFamily s30 (s30 0) (![true, true, true]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq30_7]
    exact Or.inr (Or.inr cert30_7)

private def pivot31 (σ : Fin 3 → Bool) : Fin 3 := if σ 0 then 0 else if σ 1 then 1 else 2
set_option maxHeartbeats 1600000 in
private theorem step31 (H : Subgroup SylowModel) (hmax : H ⋖ smallParityCensusNode 31) (hcent : Subgroup.centralizer (H : Set SylowModel) ≤ H) (hpar : ¬ H ≤ character.ker) : Represented smallParityCensusNode H := by
  apply step_first 31 s31 gen31 pivot31 (by decide +kernel) ?_ H hmax hcent hpar
  intro σ hn
  have he : σ = ![σ 0, σ 1, σ 2] := by
    funext k
    fin_cases k <;> rfl
  rw [he] at hn ⊢
  cases h0 : σ 0 <;> cases h1 : σ 1 <;> cases h2 : σ 2
  · obtain ⟨j, hj⟩ := hn
    fin_cases j <;> simp_all
  · change let L := Subgroup.closure (Set.range (binaryFamily s31 (s31 2) (![false, false, true]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq31_4]
    exact Or.inr (Or.inr cert31_4)
  · change let L := Subgroup.closure (Set.range (binaryFamily s31 (s31 1) (![false, true, false]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq31_2]
    exact Or.inr (Or.inr cert31_2)
  · change let L := Subgroup.closure (Set.range (binaryFamily s31 (s31 1) (![false, true, true]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq31_6]
    exact Or.inr (Or.inl cert31_6)
  · change let L := Subgroup.closure (Set.range (binaryFamily s31 (s31 0) (![true, false, false]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq31_1]
    exact Or.inl cert31_1
  · change let L := Subgroup.closure (Set.range (binaryFamily s31 (s31 0) (![true, false, true]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq31_5]
    exact Or.inr (Or.inr cert31_5)
  · change let L := Subgroup.closure (Set.range (binaryFamily s31 (s31 0) (![true, true, false]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq31_3]
    exact Or.inr (Or.inr cert31_3)
  · change let L := Subgroup.closure (Set.range (binaryFamily s31 (s31 0) (![true, true, true]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq31_7]
    exact Or.inr (Or.inl cert31_7)

private def pivot32 (σ : Fin 3 → Bool) : Fin 3 := if σ 0 then 0 else if σ 1 then 1 else 2
set_option maxHeartbeats 1600000 in
private theorem step32 (H : Subgroup SylowModel) (hmax : H ⋖ smallParityCensusNode 32) (hcent : Subgroup.centralizer (H : Set SylowModel) ≤ H) (hpar : ¬ H ≤ character.ker) : Represented smallParityCensusNode H := by
  apply step_first 32 s32 gen32 pivot32 (by decide +kernel) ?_ H hmax hcent hpar
  intro σ hn
  have he : σ = ![σ 0, σ 1, σ 2] := by
    funext k
    fin_cases k <;> rfl
  rw [he] at hn ⊢
  cases h0 : σ 0 <;> cases h1 : σ 1 <;> cases h2 : σ 2
  · obtain ⟨j, hj⟩ := hn
    fin_cases j <;> simp_all
  · change let L := Subgroup.closure (Set.range (binaryFamily s32 (s32 2) (![false, false, true]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq32_4]
    exact Or.inl cert32_4
  · change let L := Subgroup.closure (Set.range (binaryFamily s32 (s32 1) (![false, true, false]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq32_2]
    exact Or.inr (Or.inr cert32_2)
  · change let L := Subgroup.closure (Set.range (binaryFamily s32 (s32 1) (![false, true, true]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq32_6]
    exact Or.inr (Or.inr cert32_6)
  · change let L := Subgroup.closure (Set.range (binaryFamily s32 (s32 0) (![true, false, false]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq32_1]
    exact Or.inr (Or.inr cert32_1)
  · change let L := Subgroup.closure (Set.range (binaryFamily s32 (s32 0) (![true, false, true]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq32_5]
    exact Or.inr (Or.inr cert32_5)
  · change let L := Subgroup.closure (Set.range (binaryFamily s32 (s32 0) (![true, true, false]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq32_3]
    exact Or.inr (Or.inr cert32_3)
  · change let L := Subgroup.closure (Set.range (binaryFamily s32 (s32 0) (![true, true, true]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq32_7]
    exact Or.inr (Or.inr cert32_7)

private def pivot33 (σ : Fin 2 → Bool) : Fin 2 := if σ 0 then 0 else 1
set_option maxHeartbeats 1600000 in
private theorem step33 (H : Subgroup SylowModel) (hmax : H ⋖ smallParityCensusNode 33) (hcent : Subgroup.centralizer (H : Set SylowModel) ≤ H) (hpar : ¬ H ≤ character.ker) : Represented smallParityCensusNode H := by
  apply step_first 33 s33 gen33 pivot33 (by decide +kernel) ?_ H hmax hcent hpar
  intro σ hn
  have he : σ = ![σ 0, σ 1] := by
    funext k
    fin_cases k <;> rfl
  rw [he] at hn ⊢
  cases h0 : σ 0 <;> cases h1 : σ 1
  · obtain ⟨j, hj⟩ := hn
    fin_cases j <;> simp_all
  · change let L := Subgroup.closure (Set.range (binaryFamily s33 (s33 1) (![false, true]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq33_2]
    exact Or.inl cert33_2
  · change let L := Subgroup.closure (Set.range (binaryFamily s33 (s33 0) (![true, false]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq33_1]
    exact Or.inr (Or.inr cert33_1)
  · change let L := Subgroup.closure (Set.range (binaryFamily s33 (s33 0) (![true, true]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq33_3]
    exact Or.inr (Or.inr cert33_3)

private def pivot34 (σ : Fin 2 → Bool) : Fin 2 := if σ 0 then 0 else 1
set_option maxHeartbeats 1600000 in
private theorem step34 (H : Subgroup SylowModel) (hmax : H ⋖ smallParityCensusNode 34) (hcent : Subgroup.centralizer (H : Set SylowModel) ≤ H) (hpar : ¬ H ≤ character.ker) : Represented smallParityCensusNode H := by
  apply step_first 34 s34 gen34 pivot34 (by decide +kernel) ?_ H hmax hcent hpar
  intro σ hn
  have he : σ = ![σ 0, σ 1] := by
    funext k
    fin_cases k <;> rfl
  rw [he] at hn ⊢
  cases h0 : σ 0 <;> cases h1 : σ 1
  · obtain ⟨j, hj⟩ := hn
    fin_cases j <;> simp_all
  · change let L := Subgroup.closure (Set.range (binaryFamily s34 (s34 1) (![false, true]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq34_2]
    exact Or.inl cert34_2
  · change let L := Subgroup.closure (Set.range (binaryFamily s34 (s34 0) (![true, false]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq34_1]
    exact Or.inr (Or.inr cert34_1)
  · change let L := Subgroup.closure (Set.range (binaryFamily s34 (s34 0) (![true, true]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq34_3]
    exact Or.inr (Or.inr cert34_3)

private def pivot35 (σ : Fin 3 → Bool) : Fin 3 := if σ 0 then 0 else if σ 1 then 1 else 2
set_option maxHeartbeats 1600000 in
private theorem step35 (H : Subgroup SylowModel) (hmax : H ⋖ smallParityCensusNode 35) (hcent : Subgroup.centralizer (H : Set SylowModel) ≤ H) (hpar : ¬ H ≤ character.ker) : Represented smallParityCensusNode H := by
  apply step_first 35 s35 gen35 pivot35 (by decide +kernel) ?_ H hmax hcent hpar
  intro σ hn
  have he : σ = ![σ 0, σ 1, σ 2] := by
    funext k
    fin_cases k <;> rfl
  rw [he] at hn ⊢
  cases h0 : σ 0 <;> cases h1 : σ 1 <;> cases h2 : σ 2
  · obtain ⟨j, hj⟩ := hn
    fin_cases j <;> simp_all
  · change let L := Subgroup.closure (Set.range (binaryFamily s35 (s35 2) (![false, false, true]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq35_4]
    exact Or.inr (Or.inr cert35_4)
  · change let L := Subgroup.closure (Set.range (binaryFamily s35 (s35 1) (![false, true, false]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq35_2]
    exact Or.inl cert35_2
  · change let L := Subgroup.closure (Set.range (binaryFamily s35 (s35 1) (![false, true, true]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq35_6]
    exact Or.inr (Or.inr cert35_6)
  · change let L := Subgroup.closure (Set.range (binaryFamily s35 (s35 0) (![true, false, false]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq35_1]
    exact Or.inr (Or.inl cert35_1)
  · change let L := Subgroup.closure (Set.range (binaryFamily s35 (s35 0) (![true, false, true]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq35_5]
    exact Or.inr (Or.inr cert35_5)
  · change let L := Subgroup.closure (Set.range (binaryFamily s35 (s35 0) (![true, true, false]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq35_3]
    exact Or.inr (Or.inl cert35_3)
  · change let L := Subgroup.closure (Set.range (binaryFamily s35 (s35 0) (![true, true, true]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq35_7]
    exact Or.inr (Or.inr cert35_7)

private def pivot36 (σ : Fin 3 → Bool) : Fin 3 := if σ 0 then 0 else if σ 1 then 1 else 2
set_option maxHeartbeats 1600000 in
private theorem step36 (H : Subgroup SylowModel) (hmax : H ⋖ smallParityCensusNode 36) (hcent : Subgroup.centralizer (H : Set SylowModel) ≤ H) (hpar : ¬ H ≤ character.ker) : Represented smallParityCensusNode H := by
  apply step_first 36 s36 gen36 pivot36 (by decide +kernel) ?_ H hmax hcent hpar
  intro σ hn
  have he : σ = ![σ 0, σ 1, σ 2] := by
    funext k
    fin_cases k <;> rfl
  rw [he] at hn ⊢
  cases h0 : σ 0 <;> cases h1 : σ 1 <;> cases h2 : σ 2
  · obtain ⟨j, hj⟩ := hn
    fin_cases j <;> simp_all
  · change let L := Subgroup.closure (Set.range (binaryFamily s36 (s36 2) (![false, false, true]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq36_4]
    exact Or.inl cert36_4
  · change let L := Subgroup.closure (Set.range (binaryFamily s36 (s36 1) (![false, true, false]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq36_2]
    exact Or.inr (Or.inr cert36_2)
  · change let L := Subgroup.closure (Set.range (binaryFamily s36 (s36 1) (![false, true, true]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq36_6]
    exact Or.inr (Or.inr cert36_6)
  · change let L := Subgroup.closure (Set.range (binaryFamily s36 (s36 0) (![true, false, false]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq36_1]
    exact Or.inr (Or.inr cert36_1)
  · change let L := Subgroup.closure (Set.range (binaryFamily s36 (s36 0) (![true, false, true]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq36_5]
    exact Or.inr (Or.inr cert36_5)
  · change let L := Subgroup.closure (Set.range (binaryFamily s36 (s36 0) (![true, true, false]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq36_3]
    exact Or.inr (Or.inr cert36_3)
  · change let L := Subgroup.closure (Set.range (binaryFamily s36 (s36 0) (![true, true, true]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq36_7]
    exact Or.inr (Or.inr cert36_7)

private def pivot37 (σ : Fin 3 → Bool) : Fin 3 := if σ 0 then 0 else if σ 1 then 1 else 2
set_option maxHeartbeats 1600000 in
private theorem step37 (H : Subgroup SylowModel) (hmax : H ⋖ smallParityCensusNode 37) (hcent : Subgroup.centralizer (H : Set SylowModel) ≤ H) (hpar : ¬ H ≤ character.ker) : Represented smallParityCensusNode H := by
  apply step_first 37 s37 gen37 pivot37 (by decide +kernel) ?_ H hmax hcent hpar
  intro σ hn
  have he : σ = ![σ 0, σ 1, σ 2] := by
    funext k
    fin_cases k <;> rfl
  rw [he] at hn ⊢
  cases h0 : σ 0 <;> cases h1 : σ 1 <;> cases h2 : σ 2
  · obtain ⟨j, hj⟩ := hn
    fin_cases j <;> simp_all
  · change let L := Subgroup.closure (Set.range (binaryFamily s37 (s37 2) (![false, false, true]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq37_4]
    exact Or.inr (Or.inr cert37_4)
  · change let L := Subgroup.closure (Set.range (binaryFamily s37 (s37 1) (![false, true, false]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq37_2]
    exact Or.inl cert37_2
  · change let L := Subgroup.closure (Set.range (binaryFamily s37 (s37 1) (![false, true, true]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq37_6]
    exact Or.inr (Or.inr cert37_6)
  · change let L := Subgroup.closure (Set.range (binaryFamily s37 (s37 0) (![true, false, false]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq37_1]
    exact Or.inr (Or.inl cert37_1)
  · change let L := Subgroup.closure (Set.range (binaryFamily s37 (s37 0) (![true, false, true]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq37_5]
    exact Or.inr (Or.inr cert37_5)
  · change let L := Subgroup.closure (Set.range (binaryFamily s37 (s37 0) (![true, true, false]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq37_3]
    exact Or.inr (Or.inl cert37_3)
  · change let L := Subgroup.closure (Set.range (binaryFamily s37 (s37 0) (![true, true, true]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq37_7]
    exact Or.inr (Or.inr cert37_7)

private def pivot38 (σ : Fin 3 → Bool) : Fin 3 := if σ 0 then 0 else if σ 1 then 1 else 2
set_option maxHeartbeats 1600000 in
private theorem step38 (H : Subgroup SylowModel) (hmax : H ⋖ smallParityCensusNode 38) (hcent : Subgroup.centralizer (H : Set SylowModel) ≤ H) (hpar : ¬ H ≤ character.ker) : Represented smallParityCensusNode H := by
  apply step_first 38 s38 gen38 pivot38 (by decide +kernel) ?_ H hmax hcent hpar
  intro σ hn
  have he : σ = ![σ 0, σ 1, σ 2] := by
    funext k
    fin_cases k <;> rfl
  rw [he] at hn ⊢
  cases h0 : σ 0 <;> cases h1 : σ 1 <;> cases h2 : σ 2
  · obtain ⟨j, hj⟩ := hn
    fin_cases j <;> simp_all
  · change let L := Subgroup.closure (Set.range (binaryFamily s38 (s38 2) (![false, false, true]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq38_4]
    exact Or.inl cert38_4
  · change let L := Subgroup.closure (Set.range (binaryFamily s38 (s38 1) (![false, true, false]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq38_2]
    exact Or.inr (Or.inr cert38_2)
  · change let L := Subgroup.closure (Set.range (binaryFamily s38 (s38 1) (![false, true, true]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq38_6]
    exact Or.inr (Or.inr cert38_6)
  · change let L := Subgroup.closure (Set.range (binaryFamily s38 (s38 0) (![true, false, false]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq38_1]
    exact Or.inr (Or.inr cert38_1)
  · change let L := Subgroup.closure (Set.range (binaryFamily s38 (s38 0) (![true, false, true]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq38_5]
    exact Or.inr (Or.inr cert38_5)
  · change let L := Subgroup.closure (Set.range (binaryFamily s38 (s38 0) (![true, true, false]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq38_3]
    exact Or.inr (Or.inr cert38_3)
  · change let L := Subgroup.closure (Set.range (binaryFamily s38 (s38 0) (![true, true, true]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq38_7]
    exact Or.inr (Or.inr cert38_7)

private def pivot39 (σ : Fin 3 → Bool) : Fin 3 := if σ 0 then 0 else if σ 1 then 1 else 2
set_option maxHeartbeats 1600000 in
private theorem step39 (H : Subgroup SylowModel) (hmax : H ⋖ smallParityCensusNode 39) (hcent : Subgroup.centralizer (H : Set SylowModel) ≤ H) (hpar : ¬ H ≤ character.ker) : Represented smallParityCensusNode H := by
  apply step_first 39 s39 gen39 pivot39 (by decide +kernel) ?_ H hmax hcent hpar
  intro σ hn
  have he : σ = ![σ 0, σ 1, σ 2] := by
    funext k
    fin_cases k <;> rfl
  rw [he] at hn ⊢
  cases h0 : σ 0 <;> cases h1 : σ 1 <;> cases h2 : σ 2
  · obtain ⟨j, hj⟩ := hn
    fin_cases j <;> simp_all
  · change let L := Subgroup.closure (Set.range (binaryFamily s39 (s39 2) (![false, false, true]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq39_4]
    exact Or.inr (Or.inr cert39_4)
  · change let L := Subgroup.closure (Set.range (binaryFamily s39 (s39 1) (![false, true, false]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq39_2]
    exact Or.inr (Or.inr cert39_2)
  · change let L := Subgroup.closure (Set.range (binaryFamily s39 (s39 1) (![false, true, true]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq39_6]
    exact Or.inr (Or.inr cert39_6)
  · change let L := Subgroup.closure (Set.range (binaryFamily s39 (s39 0) (![true, false, false]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq39_1]
    exact Or.inl cert39_1
  · change let L := Subgroup.closure (Set.range (binaryFamily s39 (s39 0) (![true, false, true]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq39_5]
    exact Or.inr (Or.inr cert39_5)
  · change let L := Subgroup.closure (Set.range (binaryFamily s39 (s39 0) (![true, true, false]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq39_3]
    exact Or.inr (Or.inr cert39_3)
  · change let L := Subgroup.closure (Set.range (binaryFamily s39 (s39 0) (![true, true, true]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq39_7]
    exact Or.inr (Or.inr cert39_7)

private def pivot40 (σ : Fin 3 → Bool) : Fin 3 := if σ 0 then 0 else if σ 1 then 1 else 2
set_option maxHeartbeats 1600000 in
private theorem step40 (H : Subgroup SylowModel) (hmax : H ⋖ smallParityCensusNode 40) (hcent : Subgroup.centralizer (H : Set SylowModel) ≤ H) (hpar : ¬ H ≤ character.ker) : Represented smallParityCensusNode H := by
  apply step_first 40 s40 gen40 pivot40 (by decide +kernel) ?_ H hmax hcent hpar
  intro σ hn
  have he : σ = ![σ 0, σ 1, σ 2] := by
    funext k
    fin_cases k <;> rfl
  rw [he] at hn ⊢
  cases h0 : σ 0 <;> cases h1 : σ 1 <;> cases h2 : σ 2
  · obtain ⟨j, hj⟩ := hn
    fin_cases j <;> simp_all
  · change let L := Subgroup.closure (Set.range (binaryFamily s40 (s40 2) (![false, false, true]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq40_4]
    exact Or.inl cert40_4
  · change let L := Subgroup.closure (Set.range (binaryFamily s40 (s40 1) (![false, true, false]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq40_2]
    exact Or.inr (Or.inr cert40_2)
  · change let L := Subgroup.closure (Set.range (binaryFamily s40 (s40 1) (![false, true, true]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq40_6]
    exact Or.inr (Or.inr cert40_6)
  · change let L := Subgroup.closure (Set.range (binaryFamily s40 (s40 0) (![true, false, false]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq40_1]
    exact Or.inr (Or.inr cert40_1)
  · change let L := Subgroup.closure (Set.range (binaryFamily s40 (s40 0) (![true, false, true]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq40_5]
    exact Or.inr (Or.inr cert40_5)
  · change let L := Subgroup.closure (Set.range (binaryFamily s40 (s40 0) (![true, true, false]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq40_3]
    exact Or.inr (Or.inr cert40_3)
  · change let L := Subgroup.closure (Set.range (binaryFamily s40 (s40 0) (![true, true, true]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq40_7]
    exact Or.inr (Or.inr cert40_7)

private def pivot41 (σ : Fin 3 → Bool) : Fin 3 := if σ 0 then 0 else if σ 1 then 1 else 2
set_option maxHeartbeats 1600000 in
private theorem step41 (H : Subgroup SylowModel) (hmax : H ⋖ smallParityCensusNode 41) (hcent : Subgroup.centralizer (H : Set SylowModel) ≤ H) (hpar : ¬ H ≤ character.ker) : Represented smallParityCensusNode H := by
  apply step_first 41 s41 gen41 pivot41 (by decide +kernel) ?_ H hmax hcent hpar
  intro σ hn
  have he : σ = ![σ 0, σ 1, σ 2] := by
    funext k
    fin_cases k <;> rfl
  rw [he] at hn ⊢
  cases h0 : σ 0 <;> cases h1 : σ 1 <;> cases h2 : σ 2
  · obtain ⟨j, hj⟩ := hn
    fin_cases j <;> simp_all
  · change let L := Subgroup.closure (Set.range (binaryFamily s41 (s41 2) (![false, false, true]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq41_4]
    exact Or.inr (Or.inr cert41_4)
  · change let L := Subgroup.closure (Set.range (binaryFamily s41 (s41 1) (![false, true, false]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq41_2]
    exact Or.inr (Or.inr cert41_2)
  · change let L := Subgroup.closure (Set.range (binaryFamily s41 (s41 1) (![false, true, true]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq41_6]
    exact Or.inr (Or.inl cert41_6)
  · change let L := Subgroup.closure (Set.range (binaryFamily s41 (s41 0) (![true, false, false]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq41_1]
    exact Or.inl cert41_1
  · change let L := Subgroup.closure (Set.range (binaryFamily s41 (s41 0) (![true, false, true]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq41_5]
    exact Or.inr (Or.inr cert41_5)
  · change let L := Subgroup.closure (Set.range (binaryFamily s41 (s41 0) (![true, true, false]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq41_3]
    exact Or.inr (Or.inr cert41_3)
  · change let L := Subgroup.closure (Set.range (binaryFamily s41 (s41 0) (![true, true, true]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq41_7]
    exact Or.inr (Or.inl cert41_7)

private def pivot42 (σ : Fin 3 → Bool) : Fin 3 := if σ 0 then 0 else if σ 1 then 1 else 2
set_option maxHeartbeats 1600000 in
private theorem step42 (H : Subgroup SylowModel) (hmax : H ⋖ smallParityCensusNode 42) (hcent : Subgroup.centralizer (H : Set SylowModel) ≤ H) (hpar : ¬ H ≤ character.ker) : Represented smallParityCensusNode H := by
  apply step_first 42 s42 gen42 pivot42 (by decide +kernel) ?_ H hmax hcent hpar
  intro σ hn
  have he : σ = ![σ 0, σ 1, σ 2] := by
    funext k
    fin_cases k <;> rfl
  rw [he] at hn ⊢
  cases h0 : σ 0 <;> cases h1 : σ 1 <;> cases h2 : σ 2
  · obtain ⟨j, hj⟩ := hn
    fin_cases j <;> simp_all
  · change let L := Subgroup.closure (Set.range (binaryFamily s42 (s42 2) (![false, false, true]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq42_4]
    exact Or.inr (Or.inr cert42_4)
  · change let L := Subgroup.closure (Set.range (binaryFamily s42 (s42 1) (![false, true, false]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq42_2]
    exact Or.inl cert42_2
  · change let L := Subgroup.closure (Set.range (binaryFamily s42 (s42 1) (![false, true, true]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq42_6]
    exact Or.inr (Or.inr cert42_6)
  · change let L := Subgroup.closure (Set.range (binaryFamily s42 (s42 0) (![true, false, false]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq42_1]
    exact Or.inr (Or.inr cert42_1)
  · change let L := Subgroup.closure (Set.range (binaryFamily s42 (s42 0) (![true, false, true]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq42_5]
    exact Or.inr (Or.inl cert42_5)
  · change let L := Subgroup.closure (Set.range (binaryFamily s42 (s42 0) (![true, true, false]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq42_3]
    exact Or.inr (Or.inr cert42_3)
  · change let L := Subgroup.closure (Set.range (binaryFamily s42 (s42 0) (![true, true, true]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq42_7]
    exact Or.inr (Or.inl cert42_7)

private def pivot43 (σ : Fin 3 → Bool) : Fin 3 := if σ 0 then 0 else if σ 1 then 1 else 2
set_option maxHeartbeats 1600000 in
private theorem step43 (H : Subgroup SylowModel) (hmax : H ⋖ smallParityCensusNode 43) (hcent : Subgroup.centralizer (H : Set SylowModel) ≤ H) (hpar : ¬ H ≤ character.ker) : Represented smallParityCensusNode H := by
  apply step_first 43 s43 gen43 pivot43 (by decide +kernel) ?_ H hmax hcent hpar
  intro σ hn
  have he : σ = ![σ 0, σ 1, σ 2] := by
    funext k
    fin_cases k <;> rfl
  rw [he] at hn ⊢
  cases h0 : σ 0 <;> cases h1 : σ 1 <;> cases h2 : σ 2
  · obtain ⟨j, hj⟩ := hn
    fin_cases j <;> simp_all
  · change let L := Subgroup.closure (Set.range (binaryFamily s43 (s43 2) (![false, false, true]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq43_4]
    exact Or.inr (Or.inr cert43_4)
  · change let L := Subgroup.closure (Set.range (binaryFamily s43 (s43 1) (![false, true, false]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq43_2]
    exact Or.inr (Or.inr cert43_2)
  · change let L := Subgroup.closure (Set.range (binaryFamily s43 (s43 1) (![false, true, true]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq43_6]
    exact Or.inr (Or.inr cert43_6)
  · change let L := Subgroup.closure (Set.range (binaryFamily s43 (s43 0) (![true, false, false]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq43_1]
    exact Or.inl cert43_1
  · change let L := Subgroup.closure (Set.range (binaryFamily s43 (s43 0) (![true, false, true]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq43_5]
    exact Or.inr (Or.inr cert43_5)
  · change let L := Subgroup.closure (Set.range (binaryFamily s43 (s43 0) (![true, true, false]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq43_3]
    exact Or.inr (Or.inr cert43_3)
  · change let L := Subgroup.closure (Set.range (binaryFamily s43 (s43 0) (![true, true, true]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq43_7]
    exact Or.inr (Or.inr cert43_7)

private def pivot44 (σ : Fin 3 → Bool) : Fin 3 := if σ 0 then 0 else if σ 1 then 1 else 2
set_option maxHeartbeats 1600000 in
private theorem step44 (H : Subgroup SylowModel) (hmax : H ⋖ smallParityCensusNode 44) (hcent : Subgroup.centralizer (H : Set SylowModel) ≤ H) (hpar : ¬ H ≤ character.ker) : Represented smallParityCensusNode H := by
  apply step_first 44 s44 gen44 pivot44 (by decide +kernel) ?_ H hmax hcent hpar
  intro σ hn
  have he : σ = ![σ 0, σ 1, σ 2] := by
    funext k
    fin_cases k <;> rfl
  rw [he] at hn ⊢
  cases h0 : σ 0 <;> cases h1 : σ 1 <;> cases h2 : σ 2
  · obtain ⟨j, hj⟩ := hn
    fin_cases j <;> simp_all
  · change let L := Subgroup.closure (Set.range (binaryFamily s44 (s44 2) (![false, false, true]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq44_4]
    exact Or.inr (Or.inr cert44_4)
  · change let L := Subgroup.closure (Set.range (binaryFamily s44 (s44 1) (![false, true, false]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq44_2]
    exact Or.inr (Or.inr cert44_2)
  · change let L := Subgroup.closure (Set.range (binaryFamily s44 (s44 1) (![false, true, true]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq44_6]
    exact Or.inr (Or.inr cert44_6)
  · change let L := Subgroup.closure (Set.range (binaryFamily s44 (s44 0) (![true, false, false]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq44_1]
    exact Or.inl cert44_1
  · change let L := Subgroup.closure (Set.range (binaryFamily s44 (s44 0) (![true, false, true]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq44_5]
    exact Or.inr (Or.inr cert44_5)
  · change let L := Subgroup.closure (Set.range (binaryFamily s44 (s44 0) (![true, true, false]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq44_3]
    exact Or.inr (Or.inr cert44_3)
  · change let L := Subgroup.closure (Set.range (binaryFamily s44 (s44 0) (![true, true, true]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq44_7]
    exact Or.inr (Or.inr cert44_7)

private def pivot45 (σ : Fin 4 → Bool) : Fin 4 := if σ 0 then 0 else if σ 1 then 1 else if σ 2 then 2 else 3
set_option maxHeartbeats 1600000 in
private theorem step45 (H : Subgroup SylowModel) (hmax : H ⋖ smallParityCensusNode 45) (hcent : Subgroup.centralizer (H : Set SylowModel) ≤ H) (hpar : ¬ H ≤ character.ker) : Represented smallParityCensusNode H := by
  apply step_first 45 s45 gen45 pivot45 (by decide +kernel) ?_ H hmax hcent hpar
  intro σ hn
  have he : σ = ![σ 0, σ 1, σ 2, σ 3] := by
    funext k
    fin_cases k <;> rfl
  rw [he] at hn ⊢
  cases h0 : σ 0 <;> cases h1 : σ 1 <;> cases h2 : σ 2 <;> cases h3 : σ 3
  · obtain ⟨j, hj⟩ := hn
    fin_cases j <;> simp_all
  · change let L := Subgroup.closure (Set.range (binaryFamily s45 (s45 3) (![false, false, false, true]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq45_8]
    exact Or.inr (Or.inr cert45_8)
  · change let L := Subgroup.closure (Set.range (binaryFamily s45 (s45 2) (![false, false, true, false]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq45_4]
    exact Or.inr (Or.inr cert45_4)
  · change let L := Subgroup.closure (Set.range (binaryFamily s45 (s45 2) (![false, false, true, true]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq45_12]
    exact Or.inr (Or.inr cert45_12)
  · change let L := Subgroup.closure (Set.range (binaryFamily s45 (s45 1) (![false, true, false, false]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq45_2]
    exact Or.inr (Or.inr cert45_2)
  · change let L := Subgroup.closure (Set.range (binaryFamily s45 (s45 1) (![false, true, false, true]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq45_10]
    exact Or.inr (Or.inr cert45_10)
  · change let L := Subgroup.closure (Set.range (binaryFamily s45 (s45 1) (![false, true, true, false]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq45_6]
    exact Or.inr (Or.inr cert45_6)
  · change let L := Subgroup.closure (Set.range (binaryFamily s45 (s45 1) (![false, true, true, true]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq45_14]
    exact Or.inr (Or.inr cert45_14)
  · change let L := Subgroup.closure (Set.range (binaryFamily s45 (s45 0) (![true, false, false, false]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq45_1]
    exact Or.inl cert45_1
  · change let L := Subgroup.closure (Set.range (binaryFamily s45 (s45 0) (![true, false, false, true]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq45_9]
    exact Or.inr (Or.inr cert45_9)
  · change let L := Subgroup.closure (Set.range (binaryFamily s45 (s45 0) (![true, false, true, false]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq45_5]
    exact Or.inr (Or.inr cert45_5)
  · change let L := Subgroup.closure (Set.range (binaryFamily s45 (s45 0) (![true, false, true, true]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq45_13]
    exact Or.inr (Or.inr cert45_13)
  · change let L := Subgroup.closure (Set.range (binaryFamily s45 (s45 0) (![true, true, false, false]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq45_3]
    exact Or.inr (Or.inr cert45_3)
  · change let L := Subgroup.closure (Set.range (binaryFamily s45 (s45 0) (![true, true, false, true]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq45_11]
    exact Or.inr (Or.inr cert45_11)
  · change let L := Subgroup.closure (Set.range (binaryFamily s45 (s45 0) (![true, true, true, false]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq45_7]
    exact Or.inr (Or.inr cert45_7)
  · change let L := Subgroup.closure (Set.range (binaryFamily s45 (s45 0) (![true, true, true, true]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq45_15]
    exact Or.inr (Or.inr cert45_15)

private def pivot46 (σ : Fin 3 → Bool) : Fin 3 := if σ 0 then 0 else if σ 1 then 1 else 2
set_option maxHeartbeats 1600000 in
private theorem step46 (H : Subgroup SylowModel) (hmax : H ⋖ smallParityCensusNode 46) (hcent : Subgroup.centralizer (H : Set SylowModel) ≤ H) (hpar : ¬ H ≤ character.ker) : Represented smallParityCensusNode H := by
  apply step_first 46 s46 gen46 pivot46 (by decide +kernel) ?_ H hmax hcent hpar
  intro σ hn
  have he : σ = ![σ 0, σ 1, σ 2] := by
    funext k
    fin_cases k <;> rfl
  rw [he] at hn ⊢
  cases h0 : σ 0 <;> cases h1 : σ 1 <;> cases h2 : σ 2
  · obtain ⟨j, hj⟩ := hn
    fin_cases j <;> simp_all
  · change let L := Subgroup.closure (Set.range (binaryFamily s46 (s46 2) (![false, false, true]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq46_4]
    exact Or.inr (Or.inr cert46_4)
  · change let L := Subgroup.closure (Set.range (binaryFamily s46 (s46 1) (![false, true, false]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq46_2]
    exact Or.inr (Or.inr cert46_2)
  · change let L := Subgroup.closure (Set.range (binaryFamily s46 (s46 1) (![false, true, true]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq46_6]
    exact Or.inr (Or.inl cert46_6)
  · change let L := Subgroup.closure (Set.range (binaryFamily s46 (s46 0) (![true, false, false]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq46_1]
    exact Or.inl cert46_1
  · change let L := Subgroup.closure (Set.range (binaryFamily s46 (s46 0) (![true, false, true]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq46_5]
    exact Or.inr (Or.inr cert46_5)
  · change let L := Subgroup.closure (Set.range (binaryFamily s46 (s46 0) (![true, true, false]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq46_3]
    exact Or.inr (Or.inr cert46_3)
  · change let L := Subgroup.closure (Set.range (binaryFamily s46 (s46 0) (![true, true, true]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq46_7]
    exact Or.inr (Or.inl cert46_7)

private def pivot47 (σ : Fin 3 → Bool) : Fin 3 := if σ 0 then 0 else if σ 1 then 1 else 2
set_option maxHeartbeats 1600000 in
private theorem step47 (H : Subgroup SylowModel) (hmax : H ⋖ smallParityCensusNode 47) (hcent : Subgroup.centralizer (H : Set SylowModel) ≤ H) (hpar : ¬ H ≤ character.ker) : Represented smallParityCensusNode H := by
  apply step_first 47 s47 gen47 pivot47 (by decide +kernel) ?_ H hmax hcent hpar
  intro σ hn
  have he : σ = ![σ 0, σ 1, σ 2] := by
    funext k
    fin_cases k <;> rfl
  rw [he] at hn ⊢
  cases h0 : σ 0 <;> cases h1 : σ 1 <;> cases h2 : σ 2
  · obtain ⟨j, hj⟩ := hn
    fin_cases j <;> simp_all
  · change let L := Subgroup.closure (Set.range (binaryFamily s47 (s47 2) (![false, false, true]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq47_4]
    exact Or.inr (Or.inr cert47_4)
  · change let L := Subgroup.closure (Set.range (binaryFamily s47 (s47 1) (![false, true, false]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq47_2]
    exact Or.inl cert47_2
  · change let L := Subgroup.closure (Set.range (binaryFamily s47 (s47 1) (![false, true, true]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq47_6]
    exact Or.inr (Or.inr cert47_6)
  · change let L := Subgroup.closure (Set.range (binaryFamily s47 (s47 0) (![true, false, false]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq47_1]
    exact Or.inr (Or.inr cert47_1)
  · change let L := Subgroup.closure (Set.range (binaryFamily s47 (s47 0) (![true, false, true]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq47_5]
    exact Or.inr (Or.inl cert47_5)
  · change let L := Subgroup.closure (Set.range (binaryFamily s47 (s47 0) (![true, true, false]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq47_3]
    exact Or.inr (Or.inr cert47_3)
  · change let L := Subgroup.closure (Set.range (binaryFamily s47 (s47 0) (![true, true, true]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq47_7]
    exact Or.inr (Or.inl cert47_7)

private def pivot48 (σ : Fin 3 → Bool) : Fin 3 := if σ 0 then 0 else if σ 1 then 1 else 2
set_option maxHeartbeats 1600000 in
private theorem step48 (H : Subgroup SylowModel) (hmax : H ⋖ smallParityCensusNode 48) (hcent : Subgroup.centralizer (H : Set SylowModel) ≤ H) (hpar : ¬ H ≤ character.ker) : Represented smallParityCensusNode H := by
  apply step_first 48 s48 gen48 pivot48 (by decide +kernel) ?_ H hmax hcent hpar
  intro σ hn
  have he : σ = ![σ 0, σ 1, σ 2] := by
    funext k
    fin_cases k <;> rfl
  rw [he] at hn ⊢
  cases h0 : σ 0 <;> cases h1 : σ 1 <;> cases h2 : σ 2
  · obtain ⟨j, hj⟩ := hn
    fin_cases j <;> simp_all
  · change let L := Subgroup.closure (Set.range (binaryFamily s48 (s48 2) (![false, false, true]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq48_4]
    exact Or.inl cert48_4
  · change let L := Subgroup.closure (Set.range (binaryFamily s48 (s48 1) (![false, true, false]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq48_2]
    exact Or.inr (Or.inr cert48_2)
  · change let L := Subgroup.closure (Set.range (binaryFamily s48 (s48 1) (![false, true, true]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq48_6]
    exact Or.inr (Or.inr cert48_6)
  · change let L := Subgroup.closure (Set.range (binaryFamily s48 (s48 0) (![true, false, false]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq48_1]
    exact Or.inr (Or.inr cert48_1)
  · change let L := Subgroup.closure (Set.range (binaryFamily s48 (s48 0) (![true, false, true]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq48_5]
    exact Or.inr (Or.inr cert48_5)
  · change let L := Subgroup.closure (Set.range (binaryFamily s48 (s48 0) (![true, true, false]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq48_3]
    exact Or.inr (Or.inr cert48_3)
  · change let L := Subgroup.closure (Set.range (binaryFamily s48 (s48 0) (![true, true, true]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq48_7]
    exact Or.inr (Or.inr cert48_7)

private def pivot49 (σ : Fin 3 → Bool) : Fin 3 := if σ 0 then 0 else if σ 1 then 1 else 2
set_option maxHeartbeats 1600000 in
private theorem step49 (H : Subgroup SylowModel) (hmax : H ⋖ smallParityCensusNode 49) (hcent : Subgroup.centralizer (H : Set SylowModel) ≤ H) (hpar : ¬ H ≤ character.ker) : Represented smallParityCensusNode H := by
  apply step_first 49 s49 gen49 pivot49 (by decide +kernel) ?_ H hmax hcent hpar
  intro σ hn
  have he : σ = ![σ 0, σ 1, σ 2] := by
    funext k
    fin_cases k <;> rfl
  rw [he] at hn ⊢
  cases h0 : σ 0 <;> cases h1 : σ 1 <;> cases h2 : σ 2
  · obtain ⟨j, hj⟩ := hn
    fin_cases j <;> simp_all
  · change let L := Subgroup.closure (Set.range (binaryFamily s49 (s49 2) (![false, false, true]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq49_4]
    exact Or.inl cert49_4
  · change let L := Subgroup.closure (Set.range (binaryFamily s49 (s49 1) (![false, true, false]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq49_2]
    exact Or.inr (Or.inr cert49_2)
  · change let L := Subgroup.closure (Set.range (binaryFamily s49 (s49 1) (![false, true, true]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq49_6]
    exact Or.inr (Or.inr cert49_6)
  · change let L := Subgroup.closure (Set.range (binaryFamily s49 (s49 0) (![true, false, false]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq49_1]
    exact Or.inr (Or.inr cert49_1)
  · change let L := Subgroup.closure (Set.range (binaryFamily s49 (s49 0) (![true, false, true]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq49_5]
    exact Or.inr (Or.inr cert49_5)
  · change let L := Subgroup.closure (Set.range (binaryFamily s49 (s49 0) (![true, true, false]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq49_3]
    exact Or.inr (Or.inr cert49_3)
  · change let L := Subgroup.closure (Set.range (binaryFamily s49 (s49 0) (![true, true, true]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq49_7]
    exact Or.inr (Or.inr cert49_7)

private def pivot50 (σ : Fin 4 → Bool) : Fin 4 := if σ 0 then 0 else if σ 1 then 1 else if σ 2 then 2 else 3
set_option maxHeartbeats 1600000 in
private theorem step50 (H : Subgroup SylowModel) (hmax : H ⋖ smallParityCensusNode 50) (hcent : Subgroup.centralizer (H : Set SylowModel) ≤ H) (hpar : ¬ H ≤ character.ker) : Represented smallParityCensusNode H := by
  apply step_first 50 s50 gen50 pivot50 (by decide +kernel) ?_ H hmax hcent hpar
  intro σ hn
  have he : σ = ![σ 0, σ 1, σ 2, σ 3] := by
    funext k
    fin_cases k <;> rfl
  rw [he] at hn ⊢
  cases h0 : σ 0 <;> cases h1 : σ 1 <;> cases h2 : σ 2 <;> cases h3 : σ 3
  · obtain ⟨j, hj⟩ := hn
    fin_cases j <;> simp_all
  · change let L := Subgroup.closure (Set.range (binaryFamily s50 (s50 3) (![false, false, false, true]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq50_8]
    exact Or.inl cert50_8
  · change let L := Subgroup.closure (Set.range (binaryFamily s50 (s50 2) (![false, false, true, false]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq50_4]
    exact Or.inr (Or.inr cert50_4)
  · change let L := Subgroup.closure (Set.range (binaryFamily s50 (s50 2) (![false, false, true, true]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq50_12]
    exact Or.inr (Or.inr cert50_12)
  · change let L := Subgroup.closure (Set.range (binaryFamily s50 (s50 1) (![false, true, false, false]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq50_2]
    exact Or.inr (Or.inr cert50_2)
  · change let L := Subgroup.closure (Set.range (binaryFamily s50 (s50 1) (![false, true, false, true]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq50_10]
    exact Or.inr (Or.inr cert50_10)
  · change let L := Subgroup.closure (Set.range (binaryFamily s50 (s50 1) (![false, true, true, false]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq50_6]
    exact Or.inr (Or.inr cert50_6)
  · change let L := Subgroup.closure (Set.range (binaryFamily s50 (s50 1) (![false, true, true, true]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq50_14]
    exact Or.inr (Or.inr cert50_14)
  · change let L := Subgroup.closure (Set.range (binaryFamily s50 (s50 0) (![true, false, false, false]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq50_1]
    exact Or.inr (Or.inr cert50_1)
  · change let L := Subgroup.closure (Set.range (binaryFamily s50 (s50 0) (![true, false, false, true]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq50_9]
    exact Or.inr (Or.inr cert50_9)
  · change let L := Subgroup.closure (Set.range (binaryFamily s50 (s50 0) (![true, false, true, false]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq50_5]
    exact Or.inr (Or.inr cert50_5)
  · change let L := Subgroup.closure (Set.range (binaryFamily s50 (s50 0) (![true, false, true, true]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq50_13]
    exact Or.inr (Or.inr cert50_13)
  · change let L := Subgroup.closure (Set.range (binaryFamily s50 (s50 0) (![true, true, false, false]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq50_3]
    exact Or.inr (Or.inr cert50_3)
  · change let L := Subgroup.closure (Set.range (binaryFamily s50 (s50 0) (![true, true, false, true]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq50_11]
    exact Or.inr (Or.inr cert50_11)
  · change let L := Subgroup.closure (Set.range (binaryFamily s50 (s50 0) (![true, true, true, false]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq50_7]
    exact Or.inr (Or.inr cert50_7)
  · change let L := Subgroup.closure (Set.range (binaryFamily s50 (s50 0) (![true, true, true, true]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq50_15]
    exact Or.inr (Or.inr cert50_15)

private def pivot51 (σ : Fin 3 → Bool) : Fin 3 := if σ 0 then 0 else if σ 1 then 1 else 2
set_option maxHeartbeats 1600000 in
private theorem step51 (H : Subgroup SylowModel) (hmax : H ⋖ smallParityCensusNode 51) (hcent : Subgroup.centralizer (H : Set SylowModel) ≤ H) (hpar : ¬ H ≤ character.ker) : Represented smallParityCensusNode H := by
  apply step_first 51 s51 gen51 pivot51 (by decide +kernel) ?_ H hmax hcent hpar
  intro σ hn
  have he : σ = ![σ 0, σ 1, σ 2] := by
    funext k
    fin_cases k <;> rfl
  rw [he] at hn ⊢
  cases h0 : σ 0 <;> cases h1 : σ 1 <;> cases h2 : σ 2
  · obtain ⟨j, hj⟩ := hn
    fin_cases j <;> simp_all
  · change let L := Subgroup.closure (Set.range (binaryFamily s51 (s51 2) (![false, false, true]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq51_4]
    exact Or.inr (Or.inr cert51_4)
  · change let L := Subgroup.closure (Set.range (binaryFamily s51 (s51 1) (![false, true, false]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq51_2]
    exact Or.inr (Or.inl cert51_2)
  · change let L := Subgroup.closure (Set.range (binaryFamily s51 (s51 1) (![false, true, true]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq51_6]
    exact Or.inr (Or.inr cert51_6)
  · change let L := Subgroup.closure (Set.range (binaryFamily s51 (s51 0) (![true, false, false]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq51_1]
    exact Or.inl cert51_1
  · change let L := Subgroup.closure (Set.range (binaryFamily s51 (s51 0) (![true, false, true]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq51_5]
    exact Or.inr (Or.inr cert51_5)
  · change let L := Subgroup.closure (Set.range (binaryFamily s51 (s51 0) (![true, true, false]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq51_3]
    exact Or.inr (Or.inl cert51_3)
  · change let L := Subgroup.closure (Set.range (binaryFamily s51 (s51 0) (![true, true, true]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq51_7]
    exact Or.inr (Or.inr cert51_7)

private def pivot52 (σ : Fin 3 → Bool) : Fin 3 := if σ 0 then 0 else if σ 1 then 1 else 2
set_option maxHeartbeats 1600000 in
private theorem step52 (H : Subgroup SylowModel) (hmax : H ⋖ smallParityCensusNode 52) (hcent : Subgroup.centralizer (H : Set SylowModel) ≤ H) (hpar : ¬ H ≤ character.ker) : Represented smallParityCensusNode H := by
  apply step_first 52 s52 gen52 pivot52 (by decide +kernel) ?_ H hmax hcent hpar
  intro σ hn
  have he : σ = ![σ 0, σ 1, σ 2] := by
    funext k
    fin_cases k <;> rfl
  rw [he] at hn ⊢
  cases h0 : σ 0 <;> cases h1 : σ 1 <;> cases h2 : σ 2
  · obtain ⟨j, hj⟩ := hn
    fin_cases j <;> simp_all
  · change let L := Subgroup.closure (Set.range (binaryFamily s52 (s52 2) (![false, false, true]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq52_4]
    exact Or.inr (Or.inr cert52_4)
  · change let L := Subgroup.closure (Set.range (binaryFamily s52 (s52 1) (![false, true, false]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq52_2]
    exact Or.inr (Or.inr cert52_2)
  · change let L := Subgroup.closure (Set.range (binaryFamily s52 (s52 1) (![false, true, true]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq52_6]
    exact Or.inr (Or.inl cert52_6)
  · change let L := Subgroup.closure (Set.range (binaryFamily s52 (s52 0) (![true, false, false]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq52_1]
    exact Or.inl cert52_1
  · change let L := Subgroup.closure (Set.range (binaryFamily s52 (s52 0) (![true, false, true]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq52_5]
    exact Or.inr (Or.inr cert52_5)
  · change let L := Subgroup.closure (Set.range (binaryFamily s52 (s52 0) (![true, true, false]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq52_3]
    exact Or.inr (Or.inr cert52_3)
  · change let L := Subgroup.closure (Set.range (binaryFamily s52 (s52 0) (![true, true, true]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq52_7]
    exact Or.inr (Or.inl cert52_7)

private def pivot53 (σ : Fin 3 → Bool) : Fin 3 := if σ 0 then 0 else if σ 1 then 1 else 2
set_option maxHeartbeats 1600000 in
private theorem step53 (H : Subgroup SylowModel) (hmax : H ⋖ smallParityCensusNode 53) (hcent : Subgroup.centralizer (H : Set SylowModel) ≤ H) (hpar : ¬ H ≤ character.ker) : Represented smallParityCensusNode H := by
  apply step_first 53 s53 gen53 pivot53 (by decide +kernel) ?_ H hmax hcent hpar
  intro σ hn
  have he : σ = ![σ 0, σ 1, σ 2] := by
    funext k
    fin_cases k <;> rfl
  rw [he] at hn ⊢
  cases h0 : σ 0 <;> cases h1 : σ 1 <;> cases h2 : σ 2
  · obtain ⟨j, hj⟩ := hn
    fin_cases j <;> simp_all
  · change let L := Subgroup.closure (Set.range (binaryFamily s53 (s53 2) (![false, false, true]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq53_4]
    exact Or.inr (Or.inl cert53_4)
  · change let L := Subgroup.closure (Set.range (binaryFamily s53 (s53 1) (![false, true, false]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq53_2]
    exact Or.inr (Or.inr cert53_2)
  · change let L := Subgroup.closure (Set.range (binaryFamily s53 (s53 1) (![false, true, true]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq53_6]
    exact Or.inr (Or.inl cert53_6)
  · change let L := Subgroup.closure (Set.range (binaryFamily s53 (s53 0) (![true, false, false]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq53_1]
    exact Or.inl cert53_1
  · change let L := Subgroup.closure (Set.range (binaryFamily s53 (s53 0) (![true, false, true]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq53_5]
    exact Or.inr (Or.inl cert53_5)
  · change let L := Subgroup.closure (Set.range (binaryFamily s53 (s53 0) (![true, true, false]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq53_3]
    exact Or.inr (Or.inr cert53_3)
  · change let L := Subgroup.closure (Set.range (binaryFamily s53 (s53 0) (![true, true, true]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq53_7]
    exact Or.inr (Or.inl cert53_7)

private def pivot54 (σ : Fin 3 → Bool) : Fin 3 := if σ 0 then 0 else if σ 1 then 1 else 2
set_option maxHeartbeats 1600000 in
private theorem step54 (H : Subgroup SylowModel) (hmax : H ⋖ smallParityCensusNode 54) (hcent : Subgroup.centralizer (H : Set SylowModel) ≤ H) (hpar : ¬ H ≤ character.ker) : Represented smallParityCensusNode H := by
  apply step_first 54 s54 gen54 pivot54 (by decide +kernel) ?_ H hmax hcent hpar
  intro σ hn
  have he : σ = ![σ 0, σ 1, σ 2] := by
    funext k
    fin_cases k <;> rfl
  rw [he] at hn ⊢
  cases h0 : σ 0 <;> cases h1 : σ 1 <;> cases h2 : σ 2
  · obtain ⟨j, hj⟩ := hn
    fin_cases j <;> simp_all
  · change let L := Subgroup.closure (Set.range (binaryFamily s54 (s54 2) (![false, false, true]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq54_4]
    exact Or.inr (Or.inr cert54_4)
  · change let L := Subgroup.closure (Set.range (binaryFamily s54 (s54 1) (![false, true, false]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq54_2]
    exact Or.inr (Or.inr cert54_2)
  · change let L := Subgroup.closure (Set.range (binaryFamily s54 (s54 1) (![false, true, true]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq54_6]
    exact Or.inr (Or.inr cert54_6)
  · change let L := Subgroup.closure (Set.range (binaryFamily s54 (s54 0) (![true, false, false]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq54_1]
    exact Or.inl cert54_1
  · change let L := Subgroup.closure (Set.range (binaryFamily s54 (s54 0) (![true, false, true]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq54_5]
    exact Or.inr (Or.inr cert54_5)
  · change let L := Subgroup.closure (Set.range (binaryFamily s54 (s54 0) (![true, true, false]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq54_3]
    exact Or.inr (Or.inr cert54_3)
  · change let L := Subgroup.closure (Set.range (binaryFamily s54 (s54 0) (![true, true, true]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq54_7]
    exact Or.inr (Or.inr cert54_7)

private def pivot55 (σ : Fin 3 → Bool) : Fin 3 := if σ 0 then 0 else if σ 1 then 1 else 2
set_option maxHeartbeats 1600000 in
private theorem step55 (H : Subgroup SylowModel) (hmax : H ⋖ smallParityCensusNode 55) (hcent : Subgroup.centralizer (H : Set SylowModel) ≤ H) (hpar : ¬ H ≤ character.ker) : Represented smallParityCensusNode H := by
  apply step_first 55 s55 gen55 pivot55 (by decide +kernel) ?_ H hmax hcent hpar
  intro σ hn
  have he : σ = ![σ 0, σ 1, σ 2] := by
    funext k
    fin_cases k <;> rfl
  rw [he] at hn ⊢
  cases h0 : σ 0 <;> cases h1 : σ 1 <;> cases h2 : σ 2
  · obtain ⟨j, hj⟩ := hn
    fin_cases j <;> simp_all
  · change let L := Subgroup.closure (Set.range (binaryFamily s55 (s55 2) (![false, false, true]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq55_4]
    exact Or.inr (Or.inr cert55_4)
  · change let L := Subgroup.closure (Set.range (binaryFamily s55 (s55 1) (![false, true, false]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq55_2]
    exact Or.inr (Or.inr cert55_2)
  · change let L := Subgroup.closure (Set.range (binaryFamily s55 (s55 1) (![false, true, true]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq55_6]
    exact Or.inr (Or.inr cert55_6)
  · change let L := Subgroup.closure (Set.range (binaryFamily s55 (s55 0) (![true, false, false]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq55_1]
    exact Or.inl cert55_1
  · change let L := Subgroup.closure (Set.range (binaryFamily s55 (s55 0) (![true, false, true]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq55_5]
    exact Or.inr (Or.inr cert55_5)
  · change let L := Subgroup.closure (Set.range (binaryFamily s55 (s55 0) (![true, true, false]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq55_3]
    exact Or.inr (Or.inr cert55_3)
  · change let L := Subgroup.closure (Set.range (binaryFamily s55 (s55 0) (![true, true, true]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq55_7]
    exact Or.inr (Or.inr cert55_7)

private def pivot56 (σ : Fin 3 → Bool) : Fin 3 := if σ 0 then 0 else if σ 1 then 1 else 2
set_option maxHeartbeats 1600000 in
private theorem step56 (H : Subgroup SylowModel) (hmax : H ⋖ smallParityCensusNode 56) (hcent : Subgroup.centralizer (H : Set SylowModel) ≤ H) (hpar : ¬ H ≤ character.ker) : Represented smallParityCensusNode H := by
  apply step_first 56 s56 gen56 pivot56 (by decide +kernel) ?_ H hmax hcent hpar
  intro σ hn
  have he : σ = ![σ 0, σ 1, σ 2] := by
    funext k
    fin_cases k <;> rfl
  rw [he] at hn ⊢
  cases h0 : σ 0 <;> cases h1 : σ 1 <;> cases h2 : σ 2
  · obtain ⟨j, hj⟩ := hn
    fin_cases j <;> simp_all
  · change let L := Subgroup.closure (Set.range (binaryFamily s56 (s56 2) (![false, false, true]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq56_4]
    exact Or.inr (Or.inr cert56_4)
  · change let L := Subgroup.closure (Set.range (binaryFamily s56 (s56 1) (![false, true, false]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq56_2]
    exact Or.inr (Or.inl cert56_2)
  · change let L := Subgroup.closure (Set.range (binaryFamily s56 (s56 1) (![false, true, true]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq56_6]
    exact Or.inr (Or.inl cert56_6)
  · change let L := Subgroup.closure (Set.range (binaryFamily s56 (s56 0) (![true, false, false]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq56_1]
    exact Or.inl cert56_1
  · change let L := Subgroup.closure (Set.range (binaryFamily s56 (s56 0) (![true, false, true]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq56_5]
    exact Or.inr (Or.inr cert56_5)
  · change let L := Subgroup.closure (Set.range (binaryFamily s56 (s56 0) (![true, true, false]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq56_3]
    exact Or.inr (Or.inl cert56_3)
  · change let L := Subgroup.closure (Set.range (binaryFamily s56 (s56 0) (![true, true, true]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq56_7]
    exact Or.inr (Or.inl cert56_7)

private def pivot57 (σ : Fin 3 → Bool) : Fin 3 := if σ 0 then 0 else if σ 1 then 1 else 2
set_option maxHeartbeats 1600000 in
private theorem step57 (H : Subgroup SylowModel) (hmax : H ⋖ smallParityCensusNode 57) (hcent : Subgroup.centralizer (H : Set SylowModel) ≤ H) (hpar : ¬ H ≤ character.ker) : Represented smallParityCensusNode H := by
  apply step_first 57 s57 gen57 pivot57 (by decide +kernel) ?_ H hmax hcent hpar
  intro σ hn
  have he : σ = ![σ 0, σ 1, σ 2] := by
    funext k
    fin_cases k <;> rfl
  rw [he] at hn ⊢
  cases h0 : σ 0 <;> cases h1 : σ 1 <;> cases h2 : σ 2
  · obtain ⟨j, hj⟩ := hn
    fin_cases j <;> simp_all
  · change let L := Subgroup.closure (Set.range (binaryFamily s57 (s57 2) (![false, false, true]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq57_4]
    exact Or.inr (Or.inr cert57_4)
  · change let L := Subgroup.closure (Set.range (binaryFamily s57 (s57 1) (![false, true, false]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq57_2]
    exact Or.inr (Or.inr cert57_2)
  · change let L := Subgroup.closure (Set.range (binaryFamily s57 (s57 1) (![false, true, true]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq57_6]
    exact Or.inr (Or.inl cert57_6)
  · change let L := Subgroup.closure (Set.range (binaryFamily s57 (s57 0) (![true, false, false]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq57_1]
    exact Or.inl cert57_1
  · change let L := Subgroup.closure (Set.range (binaryFamily s57 (s57 0) (![true, false, true]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq57_5]
    exact Or.inr (Or.inr cert57_5)
  · change let L := Subgroup.closure (Set.range (binaryFamily s57 (s57 0) (![true, true, false]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq57_3]
    exact Or.inr (Or.inr cert57_3)
  · change let L := Subgroup.closure (Set.range (binaryFamily s57 (s57 0) (![true, true, true]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq57_7]
    exact Or.inr (Or.inl cert57_7)

private def pivot58 (σ : Fin 3 → Bool) : Fin 3 := if σ 0 then 0 else if σ 1 then 1 else 2
set_option maxHeartbeats 1600000 in
private theorem step58 (H : Subgroup SylowModel) (hmax : H ⋖ smallParityCensusNode 58) (hcent : Subgroup.centralizer (H : Set SylowModel) ≤ H) (hpar : ¬ H ≤ character.ker) : Represented smallParityCensusNode H := by
  apply step_first 58 s58 gen58 pivot58 (by decide +kernel) ?_ H hmax hcent hpar
  intro σ hn
  have he : σ = ![σ 0, σ 1, σ 2] := by
    funext k
    fin_cases k <;> rfl
  rw [he] at hn ⊢
  cases h0 : σ 0 <;> cases h1 : σ 1 <;> cases h2 : σ 2
  · obtain ⟨j, hj⟩ := hn
    fin_cases j <;> simp_all
  · change let L := Subgroup.closure (Set.range (binaryFamily s58 (s58 2) (![false, false, true]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq58_4]
    exact Or.inr (Or.inl cert58_4)
  · change let L := Subgroup.closure (Set.range (binaryFamily s58 (s58 1) (![false, true, false]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq58_2]
    exact Or.inr (Or.inr cert58_2)
  · change let L := Subgroup.closure (Set.range (binaryFamily s58 (s58 1) (![false, true, true]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq58_6]
    exact Or.inr (Or.inr cert58_6)
  · change let L := Subgroup.closure (Set.range (binaryFamily s58 (s58 0) (![true, false, false]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq58_1]
    exact Or.inl cert58_1
  · change let L := Subgroup.closure (Set.range (binaryFamily s58 (s58 0) (![true, false, true]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq58_5]
    exact Or.inr (Or.inl cert58_5)
  · change let L := Subgroup.closure (Set.range (binaryFamily s58 (s58 0) (![true, true, false]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq58_3]
    exact Or.inr (Or.inr cert58_3)
  · change let L := Subgroup.closure (Set.range (binaryFamily s58 (s58 0) (![true, true, true]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq58_7]
    exact Or.inr (Or.inr cert58_7)

private def pivot59 (σ : Fin 2 → Bool) : Fin 2 := if σ 0 then 0 else 1
set_option maxHeartbeats 1600000 in
private theorem step59 (H : Subgroup SylowModel) (hmax : H ⋖ smallParityCensusNode 59) (hcent : Subgroup.centralizer (H : Set SylowModel) ≤ H) (hpar : ¬ H ≤ character.ker) : Represented smallParityCensusNode H := by
  apply step_first 59 s59 gen59 pivot59 (by decide +kernel) ?_ H hmax hcent hpar
  intro σ hn
  have he : σ = ![σ 0, σ 1] := by
    funext k
    fin_cases k <;> rfl
  rw [he] at hn ⊢
  cases h0 : σ 0 <;> cases h1 : σ 1
  · obtain ⟨j, hj⟩ := hn
    fin_cases j <;> simp_all
  · change let L := Subgroup.closure (Set.range (binaryFamily s59 (s59 1) (![false, true]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq59_2]
    exact Or.inr (Or.inr cert59_2)
  · change let L := Subgroup.closure (Set.range (binaryFamily s59 (s59 0) (![true, false]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq59_1]
    exact Or.inr (Or.inr cert59_1)
  · change let L := Subgroup.closure (Set.range (binaryFamily s59 (s59 0) (![true, true]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq59_3]
    exact Or.inl cert59_3

private def pivot60 (σ : Fin 3 → Bool) : Fin 3 := if σ 0 then 0 else if σ 1 then 1 else 2
set_option maxHeartbeats 1600000 in
private theorem step60 (H : Subgroup SylowModel) (hmax : H ⋖ smallParityCensusNode 60) (hcent : Subgroup.centralizer (H : Set SylowModel) ≤ H) (hpar : ¬ H ≤ character.ker) : Represented smallParityCensusNode H := by
  apply step_first 60 s60 gen60 pivot60 (by decide +kernel) ?_ H hmax hcent hpar
  intro σ hn
  have he : σ = ![σ 0, σ 1, σ 2] := by
    funext k
    fin_cases k <;> rfl
  rw [he] at hn ⊢
  cases h0 : σ 0 <;> cases h1 : σ 1 <;> cases h2 : σ 2
  · obtain ⟨j, hj⟩ := hn
    fin_cases j <;> simp_all
  · change let L := Subgroup.closure (Set.range (binaryFamily s60 (s60 2) (![false, false, true]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq60_4]
    exact Or.inr (Or.inr cert60_4)
  · change let L := Subgroup.closure (Set.range (binaryFamily s60 (s60 1) (![false, true, false]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq60_2]
    exact Or.inr (Or.inr cert60_2)
  · change let L := Subgroup.closure (Set.range (binaryFamily s60 (s60 1) (![false, true, true]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq60_6]
    exact Or.inl cert60_6
  · change let L := Subgroup.closure (Set.range (binaryFamily s60 (s60 0) (![true, false, false]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq60_1]
    exact Or.inr (Or.inr cert60_1)
  · change let L := Subgroup.closure (Set.range (binaryFamily s60 (s60 0) (![true, false, true]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq60_5]
    exact Or.inr (Or.inr cert60_5)
  · change let L := Subgroup.closure (Set.range (binaryFamily s60 (s60 0) (![true, true, false]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq60_3]
    exact Or.inr (Or.inr cert60_3)
  · change let L := Subgroup.closure (Set.range (binaryFamily s60 (s60 0) (![true, true, true]))); L ≤ character.ker ∨ (∃ c, c ∈ Subgroup.centralizer (L : Set SylowModel) ∧ c ∉ L) ∨ Represented smallParityCensusNode L
    dsimp only
    rw [edgeEq60_7]
    exact Or.inr (Or.inr cert60_7)

set_option maxHeartbeats 1600000 in
/-- Every centric maximal subgroup outside parity below nodes 29–60 is represented
by the prescribed census. No order or Frattini hypothesis is required. -/
public theorem smallParityCensusStep_order256 (i : Fin 131) (hlo : 29 ≤ i.val) (hhi : i.val < 61) (H : Subgroup SylowModel) (hmax : H ⋖ smallParityCensusNode i) (hcent : Subgroup.centralizer (H : Set SylowModel) ≤ H) (hpar : ¬ H ≤ character.ker) : Represented smallParityCensusNode H := by
  rcases i with ⟨i, hi⟩
  change 29 ≤ i at hlo
  change i < 61 at hhi
  interval_cases i
  · exact step29 H hmax hcent hpar
  · exact step30 H hmax hcent hpar
  · exact step31 H hmax hcent hpar
  · exact step32 H hmax hcent hpar
  · exact step33 H hmax hcent hpar
  · exact step34 H hmax hcent hpar
  · exact step35 H hmax hcent hpar
  · exact step36 H hmax hcent hpar
  · exact step37 H hmax hcent hpar
  · exact step38 H hmax hcent hpar
  · exact step39 H hmax hcent hpar
  · exact step40 H hmax hcent hpar
  · exact step41 H hmax hcent hpar
  · exact step42 H hmax hcent hpar
  · exact step43 H hmax hcent hpar
  · exact step44 H hmax hcent hpar
  · exact step45 H hmax hcent hpar
  · exact step46 H hmax hcent hpar
  · exact step47 H hmax hcent hpar
  · exact step48 H hmax hcent hpar
  · exact step49 H hmax hcent hpar
  · exact step50 H hmax hcent hpar
  · exact step51 H hmax hcent hpar
  · exact step52 H hmax hcent hpar
  · exact step53 H hmax hcent hpar
  · exact step54 H hmax hcent hpar
  · exact step55 H hmax hcent hpar
  · exact step56 H hmax hcent hpar
  · exact step57 H hmax hcent hpar
  · exact step58 H hmax hcent hpar
  · exact step59 H hmax hcent hpar
  · exact step60 H hmax hcent hpar
end ReeTwo.SylowModel
