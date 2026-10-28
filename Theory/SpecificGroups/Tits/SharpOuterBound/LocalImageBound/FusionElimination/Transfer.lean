module
public import Theory.SpecificGroups.Tits.SharpOuterBound.LocalImageBound.FusionElimination.Checks
public import Theory.SpecificGroups.Tits.OuterOddSubgroups.OverlapCentralizers.FirstCover
public import Theory.SpecificGroups.Tits.RelativeSecondBlockLayers.SecondOrder

/-!
# Transporting the finite label checks to actual parabolic conjugacy

The stabilizer of a label under conjugation is a subgroup. The two certified
Sylow generators belong to it, hence it is the whole Sylow group. Every
parabolic conjugator is a Sylow element times a certified coset rotation;
the rotation check therefore proves invariance under internal conjugacy.

Source: Parrott (1972), §5, p.683, with the five- and three-coset covers.
-/

@[expose] public section
namespace Tits.SharpOuterBound.LocalImageBound.FusionElimination
open Subgroup ExceptionalParabolics OuterOddSubgroups.OverlapCentralizers
open Atlas1600SylowTwoCertificate

/-- The finite label, evaluated on an element of the actual Sylow subgroup. -/
def sylowLabel (k : Fin 2) (s : S) : Nat := label k (coordinate (sylowPerm s))

private theorem sylowLabel_nf (k : Fin 2) (n : Fin 2048) :
    sylowLabel k (atlas1600SylowTwoEquiv n) = label k n := by
  rw [sylowLabel, sylowPerm_nf, coordinate_normalForm]

private def labelStabilizer (k : Fin 2) : Subgroup S where
  carrier := {g | ∀ s, sylowLabel k (g * s * g⁻¹) = sylowLabel k s}
  one_mem' := by intro s; simp
  mul_mem' {a b} ha hb := by
    intro s
    simpa only [mul_inv_rev, mul_assoc] using (ha (b * s * b⁻¹)).trans (hb s)
  inv_mem' {a} ha := by
    intro s
    have h := ha (a⁻¹ * s * a)
    have he : a * (a⁻¹ * s * a) * a⁻¹ = s := by group
    rw [he] at h
    simpa only [inv_inv] using h.symm

private def gen : Fin 2 → S := ![sylowGenerator 2, sylowGenerator 7]

private theorem gen_perm (j : Fin 2) : sylowPerm (gen j) = fastGenerator j := by
  change (gen j).val.val = _
  fin_cases j <;> simp [gen, sylowGenerator, fastGenerator, Packed.perm_eq,
    Packed.generator, atlas1600ParrottAssignment_val, Atlas1600ParrottData.permutation]

private theorem gen_mem (k j : Fin 2) : gen j ∈ labelStabilizer k := by
  intro s
  obtain ⟨n, rfl⟩ := atlas1600SylowTwoEquiv.surjective s
  simp only [sylowLabel, map_mul, map_inv, gen_perm, sylowPerm_nf, coordinate_normalForm]
  simpa only [fastNormalForm_eq, fastGeneratorInv_eq] using label_generator_check k j n

private theorem word_mem {G : Type*} [Group G] (H : Subgroup G) {x y : G}
    (hx : x ∈ H) (hy : y ∈ H) (n : Fin 2048) : normalFormWord x y n ∈ H := by
  let v := normalFormWord (⟨x, hx⟩ : H) (⟨y, hy⟩ : H) n
  have hv : H.subtype v = normalFormWord x y n :=
    map_normalFormWord H.subtype ⟨x, hx⟩ ⟨y, hy⟩ n
  exact hv ▸ v.property

/-- Both labels are invariant under every actual Sylow conjugation. -/
theorem sylowLabel_conj (k : Fin 2) (g s : S) :
    sylowLabel k (g * s * g⁻¹) = sylowLabel k s := by
  have hg : g ∈ labelStabilizer k := by
    obtain ⟨n, rfl⟩ := atlas1600SylowTwoEquiv.surjective g
    rw [← normalFormWord_eq]
    exact word_mem (labelStabilizer k) (gen_mem k 0) (gen_mem k 1) n
  exact hg s

private theorem rotation_label (k : Fin 2) (j : Nat)
    (hc : ∀ n, rotationCheck k j n) (a b : Fin 2048)
    (h : normalForm a = fastRotation k ^ j * normalForm b * (fastRotation k ^ j)⁻¹) :
    label k a = label k b := by
  have ht := hc b
  simp only [rotationCheck, fastRotationInv_eq, inv_pow, fastNormalForm_eq] at ht
  rw [← h, coordinate_normalForm] at ht
  apply ht
  simpa only [fastNormalForm_eq] using pairValid_nf a

private theorem sylowLabel_rotation (k : Fin 2) (j : Nat)
    (hc : ∀ n, rotationCheck k j n) (a b : S)
    (h : sylowPerm a = fastRotation k ^ j * sylowPerm b * (fastRotation k ^ j)⁻¹) :
    sylowLabel k a = sylowLabel k b := by
  obtain ⟨n, rfl⟩ := atlas1600SylowTwoEquiv.surjective a
  obtain ⟨m, rfl⟩ := atlas1600SylowTwoEquiv.surjective b
  simp only [sylowLabel_nf]
  apply rotation_label k j hc n m
  simpa only [sylowPerm_nf] using h

private theorem conjugacy_step (k : Fin 2) (j : Nat)
    (hc : ∀ n, rotationCheck k j n) (a b s : S)
    (h : (sylowPerm s * fastRotation k ^ j) * sylowPerm a *
      (sylowPerm s * fastRotation k ^ j)⁻¹ = sylowPerm b) :
    sylowLabel k a = sylowLabel k b := by
  have hz : sylowPerm (s⁻¹ * b * s) =
      fastRotation k ^ j * sylowPerm a * (fastRotation k ^ j)⁻¹ := by
    simp only [map_mul, map_inv]
    rw [← h]
    group
  have hrot := sylowLabel_rotation k j hc (s⁻¹ * b * s) a hz
  have hs := sylowLabel_conj k s⁻¹ b
  simp only [inv_inv] at hs
  exact hrot.symm.trans hs

private theorem nf_val (n : Fin 2048) :
    (atlas1600SylowTwoNormalForm n).val = normalForm n := atlas1600SylowTwoNormalForm_val n

private theorem firstNF_perm (p : Fin 2048 × Fin 5) :
    (firstNormalForm p).val.val = normalForm p.1 * fastRotation 0 ^ p.2.val := by
  change (atlas1600SylowTwoNormalForm p.1).val * firstRotation.val ^ p.2.val = _
  rw [nf_val]
  congr 1
  change ((atlas1600ParrottAssignment .s1).val *
    (atlas1600ParrottAssignment .r1).val) ^ p.2.val = _
  simp [fastRotation, Packed.perm_eq, Packed.generator,
    atlas1600ParrottAssignment_val, Atlas1600ParrottData.permutation]

private theorem secondNF_perm (p : Fin 2048 × Fin 3) :
    (RelativeSecondBlockLayers.secondNormalForm p).val.val =
      normalForm p.1 * fastRotation 1 ^ p.2.val := by
  change (atlas1600SylowTwoNormalForm p.1).val *
    (RelativeSecondBlockLayers.SecondOrder.rep p.2).val = _
  rw [nf_val]
  congr 1
  change ((atlas1600ParrottAssignment .s8).val *
    (atlas1600ParrottAssignment .r8).val) ^ p.2.val = _
  simp [fastRotation, Packed.perm_eq, Packed.generator,
    atlas1600ParrottAssignment_val, Atlas1600ParrottData.permutation]

/-- Internal conjugacy in the first parabolic preserves the first label. -/
theorem first_label_isConj (a b : S) (h : IsConj (firstInclusion a) (firstInclusion b)) :
    sylowLabel 0 a = sylowLabel 0 b := by
  obtain ⟨g, hg⟩ := isConj_iff.mp h
  obtain ⟨⟨n, j⟩, rfl⟩ := firstNormalForm_surjective g
  apply conjugacy_step 0 j.val (first_rotation_check j) a b (atlas1600SylowTwoEquiv n)
  have hp := congrArg (fun x : first => x.val.val) hg
  change (firstNormalForm (n,j)).val.val * sylowPerm a *
    ((firstNormalForm (n,j)).val.val)⁻¹ = sylowPerm b at hp
  simpa only [firstNF_perm, sylowPerm_nf] using hp

/-- Internal conjugacy in the second parabolic preserves the second label. -/
theorem second_label_isConj (a b : S) (h : IsConj (secondInclusion a) (secondInclusion b)) :
    sylowLabel 1 a = sylowLabel 1 b := by
  obtain ⟨g, hg⟩ := isConj_iff.mp h
  obtain ⟨⟨n, j⟩, rfl⟩ := RelativeSecondBlockLayers.secondNormalForm_surjective g
  apply conjugacy_step 1 j.val (second_rotation_check j) a b (atlas1600SylowTwoEquiv n)
  have hp := congrArg (fun x : second => x.val.val) hg
  change (RelativeSecondBlockLayers.secondNormalForm (n,j)).val.val * sylowPerm a *
    ((RelativeSecondBlockLayers.secondNormalForm (n,j)).val.val)⁻¹ = sylowPerm b at hp
  simpa only [secondNF_perm, sylowPerm_nf] using hp

end Tits.SharpOuterBound.LocalImageBound.FusionElimination
end
