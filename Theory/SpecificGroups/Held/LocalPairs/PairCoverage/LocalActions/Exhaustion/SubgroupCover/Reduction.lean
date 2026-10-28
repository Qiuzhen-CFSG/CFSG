module

public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.SubgroupCover.Data
public import Theory.GroupTheory.PCoreFromTwoNormalizers

/-!
# Reduction of local Held coverage to literal finite certificates

First conjugate the marked two-group into an odd-index subgroup, with the
coset action taken inside the local overgroup. A complete double-coset cover
then reduces membership to the 17 representatives. An order-five witness
excludes every inadmissible row for a subgroup with primes only two and three.
The surviving rows place the subgroup in a union of two aligned products,
hence in one. Finally undo that alignment.

The finite coverage, alignment, and row tests are explicit hypotheses here;
the assembly module discharges them using the literal word certificates.
Sources: the local Held argument on Aschbacher–Smith pp.509–511 and
GLS3 Table 5.3p; discovery words in Exhaustion/source.
-/

public section
namespace Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.SubgroupCover
open Subgroup

/-- Coverage in the local overgroup; both double-coset factors are in the
literal marked candidate, not merely in a two-group of the same order. -/
@[expose] def DoubleCosetCoverage : Prop :=
  ∀ (i : Bool) (x : He), x ∈ localOvergroup i →
    ∃ (r : Fin 17) (a b : He), a ∈ candidateTwo i 0 ∧ b ∈ candidateTwo i 0 ∧
      x = a * representative i r * b

private theorem obstruction_mem (i : Bool) (K : Subgroup He)
    (hT : candidateTwo i 0 ≤ K) (r : Fin 17) (hr : representative i r ∈ K) :
    obstruction i r ∈ K := by
  apply evalPowers_mem
  intro k
  match k with
  | 0 => exact hT (evenGenerator_mem i 0)
  | 1 => exact hT (evenGenerator_mem i 1)
  | 2 => exact hT (evenGenerator_mem i 2)
  | 3 => exact hT (evenGenerator_mem i 3)
  | 4 => exact hr

private theorem no_five (K : Subgroup He)
    (hK : ∀ p : ℕ, p.Prime → p ∣ Nat.card K → p = 2 ∨ p = 3)
    (x : He) (hx : x ∈ K) (ho : orderOf x = 5) : False := by
  have hdiv := K.orderOf_dvd_natCard hx
  rw [ho] at hdiv
  rcases hK 5 (by decide) hdiv with h | h <;> norm_num at h

/-- The prime-five obstructions force an overgroup of the marking into one
of the two aligned literal products. -/
theorem marked_subgroup_le_aligned
    (hcover : DoubleCosetCoverage)
    (halign : ∀ i j, candidateTwo i 0 ≤ alignedProduct i j)
    (hrows : ∀ i r, representative i r ∈ alignedProduct i 0 ∨
      representative i r ∈ alignedProduct i 1 ∨ orderOf (obstruction i r) = 5)
    (i : Bool) (K : Subgroup He) (hK : K ≤ localOvergroup i)
    (hT : candidateTwo i 0 ≤ K)
    (hprimes : ∀ p : ℕ, p.Prime → p ∣ Nat.card K → p = 2 ∨ p = 3) :
    K ≤ alignedProduct i 0 ∨ K ≤ alignedProduct i 1 := by
  apply SubgroupClass.subset_union.mp
  intro x hx
  obtain ⟨r, a, b, ha, hb, he⟩ := hcover i x (hK hx)
  have hr : representative i r ∈ K := by
    have ht := K.mul_mem (K.mul_mem (K.inv_mem (hT ha)) hx) (K.inv_mem (hT hb))
    simpa only [he, mul_assoc, inv_mul_cancel_left, mul_inv_cancel, mul_one] using ht
  rcases hrows i r with hr0 | hr1 | hf
  · exact Or.inl (he ▸ (alignedProduct i 0).mul_mem
      ((alignedProduct i 0).mul_mem (halign i 0 ha) hr0) (halign i 0 hb))
  · exact Or.inr (he ▸ (alignedProduct i 1).mul_mem
      ((alignedProduct i 1).mul_mem (halign i 1 ha) hr1) (halign i 1 hb))
  · exact (no_five K hprimes _ (obstruction_mem i K hT r hr) hf).elim

/-- Assemble local subgroup coverage from actual double-coset and row
certificates. The sole structural input about the marking is its being a
two-group; neither candidate orders nor Sylow maximality are needed. -/
theorem localProductCover_of_certificates
    (hmark : ∀ i : Bool, IsPGroup 2 (candidateTwo i 0))
    (hcover : DoubleCosetCoverage)
    (halign : ∀ i j, candidateTwo i 0 ≤ alignedProduct i j)
    (hrows : ∀ i r, representative i r ∈ alignedProduct i 0 ∨
      representative i r ∈ alignedProduct i 1 ∨ orderOf (obstruction i r) = 5) :
    LocalProductCover := by
  intro i K hK hindex hprimes
  let M := localOvergroup i
  let P := (candidateTwo i 0).subgroupOf M
  have hP : IsPGroup 2 P :=
    (hmark i).of_equiv (subgroupOfEquivOfLe (candidateTwo_le_localOvergroup i 0)).symm
  obtain ⟨g, hg⟩ := exists_conj_overgroup_of_index_primeTo P (K.subgroupOf M) hP hindex
  let L := K.comap (MulAut.conj (g : He)).toMonoidHom
  have hTL : candidateTwo i 0 ≤ L := by
    intro x hx
    exact hg (show (⟨x, candidateTwo_le_localOvergroup i 0 hx⟩ : M) ∈ P from hx)
  have hLM : L ≤ M := by
    intro x hx
    have ht := M.mul_mem (M.mul_mem (M.inv_mem g.property) (hK hx)) g.property
    change (g : He)⁻¹ * ((g : He) * x * (g : He)⁻¹) * g ∈ M at ht
    simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using ht
  have hmap : L = K.map (MulAut.conj (g : He)⁻¹).toMonoidHom :=
    comap_equiv_eq_map_symm' _ _
  have hcard : Nat.card L = Nat.card K := by
    rw [hmap]
    exact Nat.card_congr
      (K.equivMapOfInjective _ (MulAut.conj (g : He)⁻¹).injective).symm.toEquiv
  have hLprimes : ∀ p : ℕ, p.Prime → p ∣ Nat.card L → p = 2 ∨ p = 3 := by
    simpa only [hcard] using hprimes
  rcases marked_subgroup_le_aligned hcover halign hrows i L hLM hTL hLprimes with h0 | h1
  · refine ⟨0, (g : He)⁻¹, M.inv_mem g.property, ?_⟩
    rw [← hmap]
    exact h0
  · refine ⟨1, alignment i * (g : He)⁻¹,
      M.mul_mem (alignment_mem i) (M.inv_mem g.property), ?_⟩
    rintro x ⟨y, hy, rfl⟩
    have hyL : (MulAut.conj (g : He)⁻¹) y ∈ L := by
      rw [hmap]
      exact mem_map_of_mem _ hy
    have ht := h1 hyL
    change alignment i * ((g : He)⁻¹ * y * ((g : He)⁻¹)⁻¹) * (alignment i)⁻¹ ∈
      candidateProduct i 1 at ht
    change (alignment i * (g : He)⁻¹) * y * (alignment i * (g : He)⁻¹)⁻¹ ∈
      candidateProduct i 1
    simpa only [mul_inv_rev, inv_inv, mul_assoc] using ht

end Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.SubgroupCover
