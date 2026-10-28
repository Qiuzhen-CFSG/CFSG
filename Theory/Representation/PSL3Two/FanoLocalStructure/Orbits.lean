module

public import Theory.Representation.PSL3Two.FanoLocalStructure.Basic

/-!
# The four nonzero orbits of the binary Fano core

The literal point complements, line complements, two-point subsets, and
complements of bases are precisely the four nonzero orbits, of sizes
7, 7, 21, and 28. A matrix with basis vectors as columns carries the coordinate
basis to that basis; extending a pair of distinct points proves the other
transitivity assertion. Sums of point complements identify these actions
with the literal subset definitions. Kernel-checked finite certificates count
the last two families and prove that zero and the four families partition the
actual even-weight core. The first two orbit calculations are reused from Basic.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, H.5.3(3–4),
printed pp.385–386 (PDF pp.396–397).
-/

@[expose] public section

open Matrix Representation BinaryLinearThree BinaryLinearThree.FanoDecomposition
open BinaryLinearThree.FanoCoreStructure
set_option synthInstance.maxSize 256
namespace BinaryLinearThree.FanoLocalStructure

@[instance_reducible] private def coreDec : DecidablePred (fun a : BinaryPermutation.Full Point => a ∈ BinaryPermutation.core Point) :=
  fun a => inferInstanceAs (Decidable ((∑ p, a p) = 0))
attribute [local instance] coreDec

@[instance_reducible] private def coreFintype : Fintype Core := Subtype.fintype _
attribute [local instance] coreFintype

@[instance_reducible] private def twoDec : DecidablePred (· ∈ weightTwo) := fun a =>
  inferInstanceAs (Decidable ((support a).card = 2))
attribute [local instance] twoDec

@[instance_reducible] private def basisDec : DecidablePred (· ∈ basisComplements) := fun a =>
  inferInstanceAs (Decidable (∃ b : Fin 3 → Point, IsBasisTriple b ∧
    ∀ p : Point, a.val p = if ∃ i, b i = p then 0 else 1))

attribute [local instance] basisDec

/-- The three coordinate points used for the orbit representatives. -/
def orbitBasisPoint (i : Fin 3) : Point := ⟨Pi.single i 1, by
  intro h
  have he := congrFun h i
  simp at he⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
private theorem coordinate_basis : IsBasisTriple orbitBasisPoint := by decide +kernel

private def matrixOfTriple (b : Fin 3 → Point) (hb : IsBasisTriple b) : Group :=
  ⟨fun i j => (b j).val i, hb⟩

private theorem matrixOfTriple_action (b : Fin 3 → Point) (hb : IsBasisTriple b) (i : Fin 3) :
    pointPerm (matrixOfTriple b hb) (orbitBasisPoint i) = b i := by
  apply Subtype.ext
  change (fun i j => (b j).val i) *ᵥ Pi.single i 1 = (b i).val
  exact Matrix.mulVec_single_one _ _

/-- The actual point action carries a natural-module basis to a basis. -/
theorem isBasisTriple_action (g : Group) (b : Fin 3 → Point) (hb : IsBasisTriple b) :
    IsBasisTriple (fun i => pointPerm g (b i)) := by
  change Matrix.det (fun i j => (g.val *ᵥ (b j).val) i) = 1
  change Matrix.det (g.val * (of fun i j => (b j).val i)) = 1
  rw [Matrix.det_mul, g.property, one_mul]
  exact hb

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
private theorem pair_extension : ∀ p q : Point, p ≠ q → ∃ r : Point,
    IsBasisTriple ![p,q,r] := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
private theorem triple_value : ∀ b : Fin 3 → Point, IsBasisTriple b → ∀ p : Point,
    ((pointSpike (b 0) + pointSpike (b 1) + pointSpike (b 2) : Core).val p) =
      if ∃ i, b i = p then 0 else 1 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
private theorem pair_characterization : ∀ a : Core, a ∈ weightTwo ↔
    ∃ p q : Point, p ≠ q ∧ a = pointSpike p + pointSpike q := by decide +kernel

/-- Two-point subsets are exactly sums of two distinct point complements. -/
theorem mem_weightTwo_iff (a : Core) : a ∈ weightTwo ↔
    ∃ p q : Point, p ≠ q ∧ a = pointSpike p + pointSpike q := pair_characterization a

/-- The literal complement of a basis is the sum of its three point complements. -/
theorem mem_basisComplements_iff (a : Core) : a ∈ basisComplements ↔
    ∃ b : Fin 3 → Point, IsBasisTriple b ∧
      a = pointSpike (b 0) + pointSpike (b 1) + pointSpike (b 2) := by
  constructor
  · rintro ⟨b, hb, ha⟩
    exact ⟨b, hb, Subtype.ext (funext (fun p => (ha p).trans (triple_value b hb p).symm))⟩
  · rintro ⟨b, hb, rfl⟩
    exact ⟨b, hb, triple_value b hb⟩

/-- The two-point subset consisting of the first two coordinate points. -/
def weightTwoRepresentative : Core := pointSpike (orbitBasisPoint 0) + pointSpike (orbitBasisPoint 1)

/-- The complement of the coordinate basis. -/
def basisComplementRepresentative : Core :=
  pointSpike (orbitBasisPoint 0) + pointSpike (orbitBasisPoint 1) + pointSpike (orbitBasisPoint 2)

/-- The literal two-point subsets form one actual core orbit. -/
theorem weightTwo_eq_orbit : weightTwo = orbit weightTwoRepresentative := by
  ext a
  constructor
  · intro ha
    obtain ⟨p, q, hpq, rfl⟩ := (mem_weightTwo_iff a).mp ha
    obtain ⟨r, hr⟩ := pair_extension p q hpq
    refine ⟨matrixOfTriple ![p,q,r] hr, ?_⟩
    simp only [weightTwoRepresentative, map_add, ← pointSpike_action, matrixOfTriple_action,
      Matrix.cons_val_zero, Matrix.cons_val_one]
  · rintro ⟨g, rfl⟩
    rw [weightTwoRepresentative, map_add, ← pointSpike_action, ← pointSpike_action]
    exact (mem_weightTwo_iff _).mpr ⟨_, _,
      fun h => (by decide : orbitBasisPoint 0 ≠ orbitBasisPoint 1) ((pointPerm g).injective h), rfl⟩

/-- The literal complements of bases form one actual core orbit. -/
theorem basisComplements_eq_orbit : basisComplements = orbit basisComplementRepresentative := by
  ext a
  constructor
  · intro ha
    obtain ⟨b, hb, rfl⟩ := (mem_basisComplements_iff a).mp ha
    refine ⟨matrixOfTriple b hb, ?_⟩
    simp only [basisComplementRepresentative, map_add, ← pointSpike_action, matrixOfTriple_action]
  · rintro ⟨g, rfl⟩
    rw [basisComplementRepresentative, map_add, map_add,
      ← pointSpike_action, ← pointSpike_action, ← pointSpike_action]
    exact (mem_basisComplements_iff _).mpr ⟨_, isBasisTriple_action g _ coordinate_basis, rfl⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- There are twenty-one two-point subsets. -/
theorem card_weightTwo : Nat.card weightTwo = 21 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- There are twenty-eight distinct complements of bases. -/
theorem card_basisComplements : Nat.card basisComplements = 28 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

@[instance_reducible] private def pointDec : DecidablePred (· ∈ pointComplements) := fun a =>
  inferInstanceAs (Decidable (∃ p, pointSpike p = a))
attribute [local instance] pointDec

@[instance_reducible] private def lineDec : DecidablePred (· ∈ lineComplements) := fun a =>
  decidable_of_iff (∃ l : Line, ∀ p : Point,
    (if Matrix.PSL3Two.Fano.Incident p l then (0 : ZMod 2) else 1) = a.val p) (by
      simp only [lineComplements, Set.mem_range, Subtype.ext_iff, funext_iff, lineComplement_apply])

attribute [local instance] lineDec

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
private theorem partition_certificate : ∀ a : Core,
    (if a = 0 then 1 else 0) + (if a ∈ pointComplements then 1 else 0) +
      (if a ∈ lineComplements then 1 else 0) + (if a ∈ weightTwo then 1 else 0) +
      (if a ∈ basisComplements then 1 else 0) = (1 : ℕ) := by decide +kernel

/-- A core vector is nonzero exactly when it belongs to one of the four families. -/
theorem nonzero_iff_mem_four_families (a : Core) : a ≠ 0 ↔
    a ∈ pointComplements ∨ a ∈ lineComplements ∨ a ∈ weightTwo ∨ a ∈ basisComplements := by
  have h := partition_certificate a
  split_ifs at h <;> simp_all

/-- All six pairwise disjointness assertions for the four literal families. -/
theorem four_families_disjoint :
    Disjoint pointComplements lineComplements ∧ Disjoint pointComplements weightTwo ∧
    Disjoint pointComplements basisComplements ∧ Disjoint lineComplements weightTwo ∧
    Disjoint lineComplements basisComplements ∧ Disjoint weightTwo basisComplements := by
  simp only [Set.disjoint_left]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro a ha hb <;>
    have h := partition_certificate a <;> simp only [ha, hb, if_true] at h <;> omega

/-- Changing the base vector within its actual orbit does not change the orbit. -/
theorem orbit_eq_of_mem {a b : Core} (h : b ∈ orbit a) : orbit b = orbit a := by
  obtain ⟨g, rfl⟩ := h
  ext c
  constructor
  · rintro ⟨k, rfl⟩
    refine ⟨k * g, ?_⟩
    rw [map_mul]
    rfl
  · rintro ⟨k, rfl⟩
    refine ⟨k * g⁻¹, ?_⟩
    have hi : U₂ g⁻¹ (U₂ g a) = a := by
      change (U₂ g⁻¹ * U₂ g) a = a
      rw [← map_mul, inv_mul_cancel, map_one]
      rfl
    rw [map_mul]
    change U₂ k (U₂ g⁻¹ (U₂ g a)) = U₂ k a
    rw [hi]

private theorem mem_own_orbit (a : Core) : a ∈ orbit a := by
  refine ⟨1, ?_⟩
  rw [map_one]
  rfl

/-- The union of the four literal families is exactly the nonzero core. -/
theorem four_families_union :
    pointComplements ∪ lineComplements ∪ weightTwo ∪ basisComplements = {a : Core | a ≠ 0} := by
  ext a
  simpa only [Set.mem_union, Set.mem_ofPred_eq, or_assoc] using
    (nonzero_iff_mem_four_families a).symm

/-- H.5.3(3): every nonzero orbit is one of the four literal families, and conversely. -/
theorem nonzero_orbits (a : Core) : a ≠ 0 ↔
    orbit a = pointComplements ∨ orbit a = lineComplements ∨
    orbit a = weightTwo ∨ orbit a = basisComplements := by
  constructor
  · intro ha
    rcases (nonzero_iff_mem_four_families a).mp ha with h | h | h | h
    · left
      rw [pointComplements_eq_orbit] at h ⊢
      exact orbit_eq_of_mem h
    · right; left
      rw [lineComplements_eq_orbit] at h ⊢
      exact orbit_eq_of_mem h
    · right; right; left
      rw [weightTwo_eq_orbit] at h ⊢
      exact orbit_eq_of_mem h
    · right; right; right
      rw [basisComplements_eq_orbit] at h ⊢
      exact orbit_eq_of_mem h
  · intro h
    apply (nonzero_iff_mem_four_families a).mpr
    have ha := mem_own_orbit a
    rcases h with h | h | h | h
    · exact Or.inl (h ▸ ha)
    · exact Or.inr (Or.inl (h ▸ ha))
    · exact Or.inr (Or.inr (Or.inl (h ▸ ha)))
    · exact Or.inr (Or.inr (Or.inr (h ▸ ha)))

/-- H.5.3(4), with all four original literal families. -/
theorem four_families_card :
    Nat.card pointComplements = 7 ∧ Nat.card lineComplements = 7 ∧
    Nat.card weightTwo = 21 ∧ Nat.card basisComplements = 28 :=
  ⟨card_pointComplements, card_lineComplements, card_weightTwo, card_basisComplements⟩

end BinaryLinearThree.FanoLocalStructure
