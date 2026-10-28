module

public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.Calculations.Representative
public import Theory.SpecificGroups.Held.Automorphisms.OuterInvolution.Noninner
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.IntrinsicEnumeration.ExtensionChecks.Action
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.IntrinsicEnumeration.WordCoverage
public import Theory.SpecificGroups.Held.Model.FourPointBase
public import Theory.GroupTheory.TwoCosetExtension
/-!
# A concrete binary extension of the Held Sylow subgroup

The existing outer involution, multiplied by a sixteen-letter Held word,
normalizes the published four-generator Sylow subgroup. Four-point checks
certify the conjugates of its generators and its square. Thus its two cosets
form an actual subgroup of the full degree-2058 permutation normalizer.
The 2048 binary words below cover this subgroup without assuming the order
of Held or full realization of its abstract automorphisms.

Source: the ATLAS HeG1-p2058B0 and HeG1-a2W1 permutations; the rank bound
used in Aschbacher--Smith, Lemma G.7.3, printed p.348. Discovery scripts and
left-action conventions are retained in `Coloring/Source`.
-/

@[expose] public section
open Subgroup
namespace Held.TwoRank
open LocalPairs LocalPairs.SylowGeometry
open LocalPairs.SylowGeometry.Calculations
open TwoLocalCandidates.MaximalNormalizerCatalogue.IntrinsicEnumeration

def correction : He :=
  ([(-2 : ℤ), -2, -2, -1, 2, 2, -1, 2, -1, 2, 2, 1, 2, 1, 2, 1].map
    (fun k => (if k.natAbs = 1 then a else b) ^ (if k < 0 then (-1 : ℤ) else 1))).prod

def outside : PermutationNormalizer := innerEmbedding correction * OuterInvolution.representative

def conjugateIndex : Fin 4 → Fin 1024
  | 0 => 176 | 1 => 287 | 2 => 354 | _ => 966

set_option maxRecDepth 8192 in
theorem conjugate_generator (i : Fin 4) :
    permutationGroup.normalizerMonoidHom outside⁻¹ (generator i) =
      (normalForm (conjugateIndex i)).val := by
  apply eq_of_four_point_images
  rw [show representation (permutationGroup.normalizerMonoidHom outside⁻¹ (generator i)) =
    outside.val⁻¹ * representation (generator i) * (outside.val⁻¹)⁻¹ from rfl, inv_inv]
  rw [← ExtensionChecks.generatorAction_eq, ← ExtensionChecks.normalFormAction_eq]
  fin_cases i <;> decide +kernel

theorem conjugate_inner (n : PermutationNormalizer) (g : He) :
    innerEmbedding (permutationGroup.normalizerMonoidHom n g) =
      n * innerEmbedding g * n⁻¹ := rfl

theorem outside_square_inner : outside * outside =
    innerEmbedding (correction * OuterInvolution.action correction) := by
  rw [map_mul]
  change outside * outside = innerEmbedding correction *
    innerEmbedding (permutationGroup.normalizerMonoidHom OuterInvolution.representative correction)
  rw [conjugate_inner]
  have ht : OuterInvolution.representative⁻¹ = OuterInvolution.representative :=
    inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using OuterInvolution.representative_sq)
  rw [ht]
  simp only [outside, mul_assoc]

set_option maxRecDepth 8192 in
theorem square_inner_eq : correction * OuterInvolution.action correction = (normalForm 144).val := by
  apply eq_of_four_point_images
  rw [← ExtensionChecks.normalFormAction_eq]
  decide +kernel

theorem outside_square : outside * outside = innerEmbedding (normalForm 144).val := by
  rw [outside_square_inner, square_inner_eq]

/-- The embedded, previously certified Held Sylow subgroup. -/
def innerSylow : Subgroup PermutationNormalizer := representative.map innerEmbedding

theorem outside_square_mem : outside * outside ∈ innerSylow := by
  rw [outside_square]
  exact mem_map_of_mem innerEmbedding (normalForm 144).property

private theorem conjugates_of_generators (n : PermutationNormalizer)
    (h : ∀ i, permutationGroup.normalizerMonoidHom n (generator i) ∈ representative)
    (k : PermutationNormalizer) (hk : k ∈ innerSylow) :
    n * k * n⁻¹ ∈ innerSylow := by
  have hS : representative ≤ representative.comap
      (permutationGroup.normalizerMonoidHom n).toMonoidHom := by
    apply (closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    exact h i
  obtain ⟨g, hg, rfl⟩ := hk
  have hg' : permutationGroup.normalizerMonoidHom n g ∈ representative := hS hg
  have hm : innerEmbedding (permutationGroup.normalizerMonoidHom n g) ∈ innerSylow :=
    mem_map_of_mem innerEmbedding hg'
  rw [conjugate_inner] at hm
  exact hm

theorem outside_inverse_conjugates (k : PermutationNormalizer) (hk : k ∈ innerSylow) :
    outside⁻¹ * k * outside ∈ innerSylow := by
  have h (i : Fin 4) : permutationGroup.normalizerMonoidHom outside⁻¹ (generator i) ∈
      representative := (conjugate_generator i).symm ▸ (normalForm (conjugateIndex i)).property
  have hm := conjugates_of_generators outside⁻¹ h k hk
  rwa [inv_inv] at hm

/-- Both binary cosets, as an actual subgroup of the permutation normalizer. -/
def extendedSylow : Subgroup PermutationNormalizer :=
  twoCosetExtension innerSylow outside outside_square_mem outside_inverse_conjugates

/-- The original 1024 words, followed by their left translates by `outside`. -/
def extensionWord (n : Fin 2048) : extendedSylow :=
  if n.val < 1024 then
    ⟨innerEmbedding (normalForm ⟨n.val % 1024, Nat.mod_lt _ (by decide)⟩).val,
      Or.inl (mem_map_of_mem _ (normalForm _).property)⟩
  else
    ⟨outside * innerEmbedding (normalForm ⟨n.val % 1024, Nat.mod_lt _ (by decide)⟩).val,
      Or.inr ⟨_, mem_map_of_mem _ (normalForm _).property, rfl⟩⟩

theorem extensionWord_surjective : Function.Surjective extensionWord := by
  intro ⟨x, hx⟩
  rcases hx with hx | ⟨k, hk, rfl⟩
  · obtain ⟨g, hg, rfl⟩ := hx
    obtain ⟨m, hm⟩ := normalForm_surjective ⟨g, hg⟩
    refine ⟨⟨m.val, by omega⟩, Subtype.ext ?_⟩
    simp only [extensionWord, m.isLt, ↓reduceIte, Nat.mod_eq_of_lt m.isLt]
    have hm' := congrArg Subtype.val hm
    change (normalForm m).val = g at hm'
    rw [hm']
  · obtain ⟨g, hg, rfl⟩ := hk
    obtain ⟨m, hm⟩ := normalForm_surjective ⟨g, hg⟩
    refine ⟨⟨1024 + m.val, by omega⟩, Subtype.ext ?_⟩
    have hh : ¬1024 + m.val < 1024 := by omega
    have hr : (1024 + m.val) % 1024 = m.val := by omega
    simp only [extensionWord, hh, ↓reduceIte, hr]
    have hm' := congrArg Subtype.val hm
    change (normalForm m).val = g at hm'
    rw [hm']

set_option maxRecDepth 8192 in
/-- The added element is outside the original Held group, using its sign. -/
theorem outside_not_inner : outside ∉ innerSubgroup := by
  have heven (g : He) : Equiv.Perm.sign (representation g) = 1 := by
    have h := hom_to_commGroup_trivial (Equiv.Perm.sign.comp representation) g
    exact h
  have hsign : Equiv.Perm.sign outside.val = -1 := by
    change Equiv.Perm.sign (representation correction * OuterInvolution.representative.val) = -1
    rw [map_mul, heven, OuterInvolution.representative_sign, one_mul]
  intro hx
  have h := heven ⟨outside.val, hx⟩
  change Equiv.Perm.sign outside.val = 1 at h
  rw [hsign] at h
  exact (by decide : (-1 : ℤˣ) ≠ 1) h

end Held.TwoRank
