module

public import Theory.SpecificGroups.Rudvalis.Model.OuterNormalizer.Relation

/-!
# Normalizer reduction for the concrete Rudvalis orbital

Assume the two ATLAS generators preserve the relation defined in `Relation`.
The checked stabilizer forest then identifies all three full suborbits.
A normalizing permutation fixing zero permutes these suborbits; their distinct
sizes force it to preserve the component rooted at 1. Conjugating the base
point gives preservation of the entire binary relation.

This proves containment of the full permutation normalizer in the relation's
automorphism group, conditional only on the generator invariance calculation.
It does not assert rigidity of the relation. Source: GLS3, Table 5.3r,
printed p.279; the ATLAS permutation tables in `Model.PermutationData`.
-/

namespace Rudvalis.OuterNormalizer
open PrimitiveData

section Invariance

variable (hG : modelSubgroup ≤ relationAut)
include hG

private theorem root_smul (g : Model) (hg : g • (0 : Fin 4060) = 0) (x : Fin 4060) :
    root (g • x) = root x := by
  have h1 : root (g • x) = 1 ↔ root x = 1 := by
    have h := hG g.property 0 x
    change adj (g • 0) (g • x) ↔ adj 0 x at h
    simpa only [hg, adj_zero] using h
  have h0 : root (g • x) = 0 ↔ root x = 0 := by
    rw [root_zero, root_zero]
    simpa only [hg] using
      (smul_left_cancel_iff g : g • x = g • (0 : Fin 4060) ↔ x = 0)
  rcases root_cases x with hx | hx | hx <;>
    rcases root_cases (g • x) with hy | hy | hy <;> simp_all

/-- Conditional identification of the full stabilizer orbits with the forest
components. The hypothesis is invariance of the concrete relation. -/
public theorem root_eq_iff (x y : Fin 4060) :
    root x = root y ↔ ∃ g : Model, g • (0 : Fin 4060) = 0 ∧ g • x = y := by
  constructor
  · intro hxy
    obtain ⟨g, hg0, hgx⟩ := root_reachable x
    obtain ⟨k, hk0, hky⟩ := root_reachable y
    refine ⟨k * g⁻¹, ?_, ?_⟩
    · rw [mul_smul, inv_smul_eq_iff.mpr hg0.symm, hk0]
    · rw [mul_smul, inv_smul_eq_iff.mpr hgx.symm, hxy, hky]
  · rintro ⟨g, hg0, rfl⟩
    exact (root_smul hG g hg0 x).symm

/-- The candidate relation is the actual orbital of the ordered pair `(0,1)`
once the two generator invariance checks have been supplied. -/
public theorem adj_iff (x y : Fin 4060) :
    adj x y ↔ ∃ g : Model, g • (0 : Fin 4060) = x ∧ g • (1 : Fin 4060) = y := by
  constructor
  · intro hxy
    let t := toBase (transDepth x) x
    have hr : root (t • y) = 1 := hxy
    obtain ⟨s, hs0, hs1⟩ := root_reachable (t • y)
    rw [hr] at hs1
    refine ⟨t⁻¹ * s, ?_, ?_⟩
    · rw [mul_smul, hs0]
      exact inv_smul_eq_iff.mpr (toBase_smul x).symm
    · rw [mul_smul, hs1, inv_smul_smul]
  · rintro ⟨g, rfl, rfl⟩
    apply (hG g.property 0 1).mpr
    rw [adj_zero]
    decide +kernel

omit hG in
private theorem conjugate_pair (p : Equiv.Perm (Fin 4060))
    (hp : p ∈ Subgroup.normalizer (modelSubgroup : Set (Equiv.Perm (Fin 4060))))
    (g : Model) (x y : Fin 4060) :
    ∃ k : Model, k • p x = p (g • x) ∧ k • p y = p (g • y) := by
  let k : Model := ⟨p * g.val * p⁻¹, (hp g.val).mp g.property⟩
  refine ⟨k, ?_, ?_⟩ <;> change p (g • (p⁻¹ (p _))) = _ <;> simp

private theorem root_conj_forward (p : Equiv.Perm (Fin 4060))
    (hp : p ∈ Subgroup.normalizer (modelSubgroup : Set (Equiv.Perm (Fin 4060))))
    (hp0 : p 0 = 0) (x y : Fin 4060) (hxy : root x = root y) :
    root (p x) = root (p y) := by
  obtain ⟨g, hg0, hgxy⟩ := (root_eq_iff hG x y).mp hxy
  obtain ⟨k, hk0, hkx⟩ := conjugate_pair p hp g 0 x
  rw [hp0, hg0, hp0] at hk0
  rw [hgxy] at hkx
  exact (root_eq_iff hG (p x) (p y)).mpr ⟨k, hk0, hkx⟩

private theorem root_conj_iff (p : Equiv.Perm (Fin 4060))
    (hp : p ∈ Subgroup.normalizer (modelSubgroup : Set (Equiv.Perm (Fin 4060))))
    (hp0 : p 0 = 0) (x y : Fin 4060) :
    root (p x) = root (p y) ↔ root x = root y := by
  constructor
  · intro hxy
    have hi0 : p⁻¹ 0 = 0 := by
      apply p.injective
      simpa using hp0.symm
    have h := root_conj_forward hG p⁻¹ (Subgroup.inv_mem _ hp) hi0 (p x) (p y) hxy
    simpa using h
  · exact root_conj_forward hG p hp hp0 x y

/-- A normalizing permutation fixing zero cannot exchange the unequal
nontrivial suborbits. -/
public theorem normalizer_fix_zero_root_one (p : Equiv.Perm (Fin 4060))
    (hp : p ∈ Subgroup.normalizer (modelSubgroup : Set (Equiv.Perm (Fin 4060))))
    (hp0 : p 0 = 0) : root (p 1) = 1 := by
  have h1 : root 1 = 1 := by decide +kernel
  have himage : p '' {x : Fin 4060 | root x = 1} =
      {x : Fin 4060 | root x = root (p 1)} := by
    ext y
    obtain ⟨x, rfl⟩ := p.surjective y
    simp only [Set.mem_image, Set.mem_ofPred, p.injective.eq_iff, exists_eq_right]
    simpa only [h1] using (root_conj_iff hG p hp hp0 x 1).symm
  have hc : {x : Fin 4060 | root x = root (p 1)}.ncard = 1755 := by
    rw [← himage, Set.ncard_image_of_injective _ p.injective, root_one_card]
  rcases root_cases (p 1) with h0 | h | h6
  · have he : p 1 = p 0 := (root_zero _).mp h0 |>.trans hp0.symm
    have hn : (1 : Fin 4060) ≠ 0 := by decide
    exact (hn (p.injective he)).elim
  · exact h
  · rw [h6, root_six_card] at hc
    omega

private theorem normalizer_base_pair (p : Equiv.Perm (Fin 4060))
    (hp : p ∈ Subgroup.normalizer (modelSubgroup : Set (Equiv.Perm (Fin 4060)))) :
    adj (p 0) (p 1) := by
  let t := toBase (transDepth (p 0)) (p 0)
  have ht : t.val ∈ Subgroup.normalizer
      (modelSubgroup : Set (Equiv.Perm (Fin 4060))) := Subgroup.le_normalizer t.property
  have hq := normalizer_fix_zero_root_one hG (t.val * p)
    (Subgroup.mul_mem _ ht hp) (toBase_smul (p 0))
  exact hq

private theorem normalizer_preserves_forward (p : Equiv.Perm (Fin 4060))
    (hp : p ∈ Subgroup.normalizer (modelSubgroup : Set (Equiv.Perm (Fin 4060))))
    (x y : Fin 4060) (hxy : adj x y) : adj (p x) (p y) := by
  obtain ⟨g, hg0, hg1⟩ := (adj_iff hG x y).mp hxy
  obtain ⟨s, hs0, hs1⟩ := (adj_iff hG (p 0) (p 1)).mp (normalizer_base_pair hG p hp)
  obtain ⟨k, hk0, hk1⟩ := conjugate_pair p hp g 0 1
  apply (adj_iff hG (p x) (p y)).mpr
  refine ⟨k * s, ?_, ?_⟩
  · rw [mul_smul, hs0, hk0, hg0]
  · rw [mul_smul, hs1, hk1, hg1]

/-- All normalizing permutations preserve the concrete relation. The unequal
subdegrees, rather than centralizer information, force this conclusion. -/
public theorem normalizer_le_relationAut :
    Subgroup.normalizer (modelSubgroup : Set (Equiv.Perm (Fin 4060))) ≤ relationAut := by
  intro p hp x y
  constructor
  · intro hxy
    have h := normalizer_preserves_forward hG p⁻¹ (Subgroup.inv_mem _ hp) (p x) (p y) hxy
    simpa using h
  · exact normalizer_preserves_forward hG p hp x y

end Invariance

end Rudvalis.OuterNormalizer
