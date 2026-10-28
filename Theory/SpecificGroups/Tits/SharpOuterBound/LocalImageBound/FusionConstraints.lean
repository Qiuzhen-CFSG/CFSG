module
public import Theory.SpecificGroups.Tits.SharpOuterBound.LocalImageBound.TwoGenerators

/-!
# Two necessary conjugacy constraints for compatible local restrictions

Normal forms 37 and 260 are conjugate in the first marked parabolic; normal
forms 4 and 260 are conjugate in the second. Explicit conjugators are checked
on all 1600 points. The actual parabolic extension witnesses transport these
conjugacies to the substituted generator images.

Source: the Atlas realization of Parrott (1972), §5, p.683. All indices use
`Atlas1600SylowTwoCertificate.normalForm`. Conjugacy is internal to the
respective parabolic, and no assertion about its two-core is used.
-/

@[expose] public section
namespace Tits.SharpOuterBound.LocalImageBound
open Subgroup ExceptionalParabolics
open Atlas1600ParrottData Atlas1600SylowTwoCertificate
open OuterOddSubgroups.OverlapCentralizers

def firstInclusion : S →* first := inclusion sylow_le_first
def secondInclusion : S →* second := inclusion sylow_le_second

/-- Conjugacy required by the first parabolic, after substituting a proposed pair. -/
def FirstFusionCondition (p : Fin 2048 × Fin 2048) : Prop :=
  IsConj (firstInclusion (pairEvaluation p 37)) (firstInclusion (pairEvaluation p 260))

/-- Conjugacy required by the second parabolic, after substituting a proposed pair. -/
def SecondFusionCondition (p : Fin 2048 × Fin 2048) : Prop :=
  IsConj (secondInclusion (pairEvaluation p 4)) (secondInclusion (pairEvaluation p 260))

private def fastNormalForm (n : Fin 2048) : Equiv.Perm (Fin 1600) :=
  Packed.perm 2 ^ (n.val % 2) * Packed.perm 3 ^ (n.val / 2 % 2) *
  Packed.perm 4 ^ (n.val / 4 % 4) * Packed.perm 5 ^ (n.val / 16 % 2) *
  Packed.perm 6 ^ (n.val / 32 % 4) * Packed.perm 7 ^ (n.val / 128 % 2) *
  Packed.perm 8 ^ (n.val / 256 % 4) * Packed.perm 9 ^ (n.val / 1024 % 2)

private theorem fastNormalForm_eq (n : Fin 2048) : fastNormalForm n = normalForm n := by
  simp [fastNormalForm, Packed.perm_eq, Packed.generator, normalForm]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1600000 in
private theorem first_certificate :
    normalForm 37 * (normalForm 58 * (s1Perm * r1Perm) ^ 4) =
      (normalForm 58 * (s1Perm * r1Perm) ^ 4) * normalForm 260 := by
  have h : ∀ p : Fin 1600,
      (fastNormalForm 37 * (fastNormalForm 58 * (Packed.perm 2 * Packed.perm 0) ^ 4)) p =
      ((fastNormalForm 58 * (Packed.perm 2 * Packed.perm 0) ^ 4) * fastNormalForm 260) p := by
    apply Atlas1600OrderCertificate.allFin
    decide +kernel
  apply Equiv.ext
  simpa [fastNormalForm_eq, Packed.perm_eq, Packed.generator] using h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1600000 in
private theorem second_certificate :
    normalForm 4 * (normalForm 1541 * (s8Perm * r8Perm)) =
      (normalForm 1541 * (s8Perm * r8Perm)) * normalForm 260 := by
  have h : ∀ p : Fin 1600,
      (fastNormalForm 4 * (fastNormalForm 1541 * (Packed.perm 9 * Packed.perm 1))) p =
      ((fastNormalForm 1541 * (Packed.perm 9 * Packed.perm 1)) * fastNormalForm 260) p := by
    apply Atlas1600OrderCertificate.allFin
    decide +kernel
  apply Equiv.ext
  simpa [fastNormalForm_eq, Packed.perm_eq, Packed.generator] using h

private def firstConjugator : first :=
  ⟨atlas1600SylowTwoNormalForm 58 *
      (atlas1600ParrottAssignment .s1 * atlas1600ParrottAssignment .r1) ^ 4,
    first.mul_mem (sylow_le_first (atlas1600SylowTwoNormalForm_mem _))
      (first.pow_mem (first.mul_mem (sylow_le_first (sylowGenerator 0).property)
        reflection_mem_first) _)⟩

private def secondConjugator : second :=
  ⟨atlas1600SylowTwoNormalForm 1541 *
      (atlas1600ParrottAssignment .s8 * atlas1600ParrottAssignment .r8),
    second.mul_mem (sylow_le_second (atlas1600SylowTwoNormalForm_mem _))
      (second.mul_mem (sylow_le_second (sylowGenerator 7).property) reflection_mem_second)⟩

private theorem atlas_val_mul (x y : Atlas1600Group) : (x * y).val = x.val * y.val := rfl
private theorem atlas_val_pow (x : Atlas1600Group) (n : Nat) : (x ^ n).val = x.val ^ n := rfl
private theorem first_val_mul (x y : first) : (x * y).val = x.val * y.val := rfl
private theorem second_val_mul (x y : second) : (x * y).val = x.val * y.val := rfl
private theorem nf_val (n : Fin 2048) : (atlas1600SylowTwoNormalForm n).val = normalForm n :=
  atlas1600SylowTwoNormalForm_val n

private theorem firstInclusion_nf_val (n : Fin 2048) :
    (firstInclusion (atlas1600SylowTwoEquiv n)).val.val = normalForm n := by
  change (atlas1600SylowTwoEquiv n).val.val = _
  rw [atlas1600SylowTwoEquiv_apply, nf_val]

private theorem secondInclusion_nf_val (n : Fin 2048) :
    (secondInclusion (atlas1600SylowTwoEquiv n)).val.val = normalForm n := by
  change (atlas1600SylowTwoEquiv n).val.val = _
  rw [atlas1600SylowTwoEquiv_apply, nf_val]

private theorem firstConjugator_val :
    firstConjugator.val.val = normalForm 58 * (s1Perm * r1Perm) ^ 4 := by
  change (atlas1600SylowTwoNormalForm 58 *
    (atlas1600ParrottAssignment .s1 * atlas1600ParrottAssignment .r1) ^ 4).val = _
  simp only [atlas_val_mul, atlas_val_pow, nf_val,
    atlas1600ParrottAssignment_val, permutation]

private theorem secondConjugator_val :
    secondConjugator.val.val = normalForm 1541 * (s8Perm * r8Perm) := by
  change (atlas1600SylowTwoNormalForm 1541 *
    (atlas1600ParrottAssignment .s8 * atlas1600ParrottAssignment .r8)).val = _
  simp only [atlas_val_mul, nf_val,
    atlas1600ParrottAssignment_val, permutation]

/-- The first required conjugacy holds inside the actual first parabolic. -/
theorem first_marked_isConj :
    IsConj (firstInclusion (atlas1600SylowTwoEquiv 37))
      (firstInclusion (atlas1600SylowTwoEquiv 260)) := by
  apply IsConj.symm
  apply isConj_iff.mpr
  refine ⟨firstConjugator, mul_inv_eq_iff_eq_mul.mpr ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  simp only [first_val_mul, atlas_val_mul, firstConjugator_val, firstInclusion_nf_val]
  exact first_certificate.symm

/-- The second required conjugacy holds inside the actual second parabolic. -/
theorem second_marked_isConj :
    IsConj (secondInclusion (atlas1600SylowTwoEquiv 4))
      (secondInclusion (atlas1600SylowTwoEquiv 260)) := by
  apply IsConj.symm
  apply isConj_iff.mpr
  refine ⟨secondConjugator, mul_inv_eq_iff_eq_mul.mpr ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  simp only [second_val_mul, atlas_val_mul, secondConjugator_val, secondInclusion_nf_val]
  exact second_certificate.symm

/-- Both extension witnesses transport the two certified local conjugacies. -/
theorem compatible_fusionConditions (f : MulAut S) (hf : HasCompatibleParabolicExtensions f) :
    FirstFusionCondition (generatorPair f) ∧ SecondFusionCondition (generatorPair f) := by
  obtain ⟨a, b, ha, hb⟩ := hf
  have ha' (s : S) : a (firstInclusion s) = firstInclusion (f s) := Subtype.ext (ha s)
  have hb' (s : S) : b (secondInclusion s) = secondInclusion (f s) := Subtype.ext (hb s)
  constructor
  · have h := a.toMonoidHom.map_isConj first_marked_isConj
    simpa only [FirstFusionCondition, pairEvaluation_generatorPair, MulEquiv.coe_toMonoidHom,
      ha'] using h
  · have h := b.toMonoidHom.map_isConj second_marked_isConj
    simpa only [SecondFusionCondition, pairEvaluation_generatorPair, MulEquiv.coe_toMonoidHom,
      hb'] using h

end Tits.SharpOuterBound.LocalImageBound
end
