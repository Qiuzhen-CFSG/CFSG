module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22KernelCertificate.Involution
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22KernelCertificate.GraphData
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22KernelCertificate.GraphInvariance
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22KernelCertificate.GraphSeparation
public import Theory.GroupAction.CentralizerFixedPointsExponent

/-!
# The Fi22 involution and its fixed-point kernel

The exact first ATLAS generator has order two: its decoded cycles are disjoint
transpositions and it sends point zero to 523. For the fixed-point kernel,
an invariant Boolean relation separating points up to this involution forces
every kernel element to have square one.

The graph certificates prove invariance under the original ATLAS generators
and separation by actual fixed points, so both the order and 2-group kernel
theorems are unconditional. They supply the involution and kernel premises
of the centralizer quotient construction associated with GLS3 Table 5.3t
(`refs/KGroup/GLS3/Chapter5(sec3-).tex`). Identification of the fixed-point
image with U₆(2) remains a separate result.
-/

public section

namespace Sporadic.Fischer.Fi22

theorem atlasA_sq_eq_one : atlasA ^ 2 = 1 := by
  apply inclusion_injective
  simpa only [map_pow, map_one, inclusion_atlasA] using KernelCertificate.generatorA_sq

theorem orderOf_atlasA : orderOf atlasA = 2 := by
  apply orderOf_eq_prime atlasA_sq_eq_one
  intro h
  have hz := congrArg (fun g : Carrier => inclusion g (0 : Fin 3510)) h
  simp only [inclusion_atlasA, KernelCertificate.generatorA_zero, map_one,
    Equiv.Perm.one_apply] at hz
  exact (by decide : (523 : Fin 3510) ≠ 0) hz

private theorem relation_invariant_of_generators (R : Fin 3510 → Fin 3510 → Bool)
    (hA : ∀ x y, R (generatorA x) (generatorA y) = R x y)
    (hB : ∀ x y, R (generatorB x) (generatorB y) = R x y)
    (g : Carrier) (x y : Fin 3510) : R (inclusion g x) (inclusion g y) = R x y := by
  have hp (p : Equiv.Perm (Fin 3510)) (h : p ∈ generated) :
      ∀ x y, R (p x) (p y) = R x y := by
    induction h using Subgroup.closure_induction with
    | mem p hp =>
      rcases hp with rfl | hp
      · exact hA
      · have he : p = generatorB := hp
        subst p
        exact hB
    | one => intro x y; rfl
    | mul p q _ _ hp hq =>
      intro x y
      simp only [Equiv.Perm.mul_apply, hp, hq]
    | inv p _ hp =>
      intro x y
      simpa using (hp (p⁻¹ x) (p⁻¹ y)).symm
  exact hp g.val g.property x y

/-- The final kernel assembly, conditional on the two concrete graph certificates. -/
theorem isPGroup_fixedPointAction_ker_of_graph
    (hA : ∀ x y, KernelCertificate.related (generatorA x) (generatorA y) =
      KernelCertificate.related x y)
    (hB : ∀ x y, KernelCertificate.related (generatorB x) (generatorB y) =
      KernelCertificate.related x y)
    (hsep : ∀ x y : Fin 3510,
      (∀ f : FixedPointsA, KernelCertificate.related x f.val =
        KernelCertificate.related y f.val) → y = x ∨ y = generatorA x) :
    IsPGroup 2 fixedPointAction.ker :=
  Theory.GroupAction.CentralizerFixedPoints.isPGroup_two_of_separating_relation
    inclusion inclusion_injective atlasA atlasA_sq_eq_one KernelCertificate.related
    (relation_invariant_of_generators KernelCertificate.related hA hB) hsep

/-- The kernel of the actual ATLAS centralizer action on the fixed points
of its first generator is a 2-group. -/
theorem isPGroup_fixedPointAction_ker : IsPGroup 2 fixedPointAction.ker :=
  isPGroup_fixedPointAction_ker_of_graph
    KernelCertificate.related_generatorA KernelCertificate.related_generatorB
    (KernelCertificate.related_separates_of_fastA KernelCertificate.generatorA_apply_eq_fastA)

end Sporadic.Fischer.Fi22
