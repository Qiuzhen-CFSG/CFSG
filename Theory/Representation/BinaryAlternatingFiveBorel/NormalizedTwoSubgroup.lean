module
public import Theory.Representation.BinaryAlternatingFiveBorel

/-!
# Two-subgroups normalized by the marked A₄ Borel

A two-subgroup of the five-letter symmetric group normalized by the standard
A₄ point stabilizer lies in its Klein four core. No fixed-point condition is
required of the two-subgroup. Three explicit three-cycles detect this: if a
permutation and its three commutators all have two-power order, it fixes the
fifth point and is even. Normality inside the Borel then gives core containment.

The finite certificate only ranges over the 120 permutations; the exponent
bound and the passage to the intrinsic two-core are structural. The inclusion
retains the actual five-point action needed for the paired point-core cover in
Aschbacher–Smith, original 14.6.9(l), printed p.1027.
-/

@[expose] public section
open Equiv Subgroup
namespace BinaryPermutation.AlternatingFiveBorel

/-- The literal inclusion of the marked Borel into the five-letter symmetric group. -/
abbrev borelToPerm : B →* Perm (Fin 5) :=
  (alternatingGroup (Fin 5)).subtype.comp B.subtype

theorem borelToPerm_injective : Function.Injective borelToPerm :=
  Subtype.val_injective.comp Subtype.val_injective

private def cubic0 : B :=
  ⟨⟨Equiv.swap 0 1 * Equiv.swap 1 2,
    by rw [Equiv.Perm.mem_alternatingGroup]; decide +kernel⟩, by decide +kernel⟩
private def cubic1 : B :=
  ⟨⟨Equiv.swap 0 1 * Equiv.swap 1 3,
    by rw [Equiv.Perm.mem_alternatingGroup]; decide +kernel⟩, by decide +kernel⟩
private def cubic2 : B :=
  ⟨⟨Equiv.swap 0 2 * Equiv.swap 2 3,
    by rw [Equiv.Perm.mem_alternatingGroup]; decide +kernel⟩, by decide +kernel⟩

private theorem finite_certificate : ∀ a : Perm (Fin 5),
    a ^ 8 = 1 →
    (borelToPerm cubic0 * a * (borelToPerm cubic0)⁻¹ * a⁻¹) ^ 8 = 1 →
    (borelToPerm cubic1 * a * (borelToPerm cubic1)⁻¹ * a⁻¹) ^ 8 = 1 →
    (borelToPerm cubic2 * a * (borelToPerm cubic2)⁻¹ * a⁻¹) ^ 8 = 1 →
    a 4 = 4 ∧ a.sign = 1 := by decide +kernel

private theorem pow_eight (P : Subgroup (Perm (Fin 5))) (hP : IsPGroup 2 P)
    (a : P) : (a : Perm (Fin 5)) ^ 8 = 1 := by
  have h120 : (a : Perm (Fin 5)) ^ 120 = 1 := by
    have h := pow_card_eq_one (x := (a : Perm (Fin 5)))
    have hcard : Fintype.card (Perm (Fin 5)) = 120 := by
      rw [Fintype.card_perm, Fintype.card_fin]
      decide
    rwa [hcard] at h
  have h15 : (a ^ 8) ^ 15 = (1 : P) := by
    apply Subtype.ext
    simpa only [Subgroup.coe_pow, Subgroup.coe_one, ← pow_mul] using h120
  have h8 : a ^ 8 = 1 := (hP.powEquiv (by decide : Nat.Coprime 2 15)).injective
    (by change (a ^ 8) ^ 15 = (1 : P) ^ 15; simpa using h15)
  exact congrArg Subtype.val h8

/-- Normalization by A₄ already forces a two-subgroup to fix the marked point
and to act by even permutations. -/
theorem normalizes_twoSubgroup_point_even (P : Subgroup (Perm (Fin 5)))
    (hP : IsPGroup 2 P)
    (hN : ∀ b : B, borelToPerm b ∈ normalizer (P : Set (Perm (Fin 5))))
    (a : Perm (Fin 5)) (ha : a ∈ P) : a 4 = 4 ∧ a.sign = 1 := by
  have hc (b : B) : (borelToPerm b * a * (borelToPerm b)⁻¹ * a⁻¹) ^ 8 = 1 :=
    pow_eight P hP ⟨_, P.mul_mem
      ((mem_normalizer_iff.mp (hN b) a).mp ha) (P.inv_mem ha)⟩
  exact finite_certificate a (pow_eight P hP ⟨a, ha⟩) (hc cubic0) (hc cubic1) (hc cubic2)

/-- Every two-subgroup normalized by the marked A₄ lies in the image of its
intrinsic two-core, under the literal permutation inclusion. -/
theorem normalizes_twoSubgroup_le_core (P : Subgroup (Perm (Fin 5)))
    (hP : IsPGroup 2 P)
    (hN : ∀ b : B, borelToPerm b ∈ normalizer (P : Set (Perm (Fin 5)))) :
    P ≤ (pCore 2 B).map borelToPerm := by
  let Q := P.comap borelToPerm
  have hQn : Q.Normal := by
    refine ⟨?_⟩
    intro a ha b
    change borelToPerm b * borelToPerm a * (borelToPerm b)⁻¹ ∈ P
    exact (mem_normalizer_iff.mp (hN b) (borelToPerm a)).mp ha
  have hQp : IsPGroup 2 Q := hP.comap_of_injective borelToPerm borelToPerm_injective
  have hQc : Q ≤ pCore 2 B := le_sSup ⟨hQn, hQp⟩
  intro a ha
  obtain ⟨hf, hs⟩ := normalizes_twoSubgroup_point_even P hP hN a ha
  let b : B := ⟨⟨a, hs⟩, hf⟩
  exact ⟨b, hQc ha, rfl⟩

/-- The same conclusion for the existing kernel of the two-dimensional Borel section. -/
theorem normalizes_twoSubgroup_le_sectionKernel (P : Subgroup (Perm (Fin 5)))
    (hP : IsPGroup 2 P)
    (hN : ∀ b : B, borelToPerm b ∈ normalizer (P : Set (Perm (Fin 5)))) :
    P ≤ sectionKernel.map borelToPerm := by
  rw [sectionKernel_eq_twoCore]
  exact normalizes_twoSubgroup_le_core P hP hN

end BinaryPermutation.AlternatingFiveBorel
