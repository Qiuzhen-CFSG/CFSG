module
public import Theory.SpecificGroups.ExceptionalOuterDisplacements.HS.Outer.PermutationFusion.Membership
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.GeneratorCover

/-!
# Short non-two-central displacement candidates for both outer HS classes

Write a,b for the defining HS generators. For the elementary outer
representative use x = b⁻¹ b⁻¹ a b a b b; for the symmetric representative
use x = a b⁻¹ a b b a. Kernel checks on the actual degree-100 action prove
that x * β(x)⁻¹ is a fixed-point-free involution in both cases.

The calculations use the existing packed permutations p0,p1, whose equality
with a,b is already proved. This avoids repeatedly reducing the original
cycle-list representation. Membership is by words in the literal carrier.
The non-two-central mark is supplied by `Center.lean` in the final assembly.

Source: Aschbacher–Smith I.2.2 observation (iii), printed p.411 / PDF p.422.
`source/discover.py` reproduces the word search; it supplies no proof premise.
ATLAS HSG1-p100B0 attribution and license are retained in LICENSES/ATLAS.txt
and the carrier's source directory.
-/

public section
namespace Theory.SpecificGroups.ExceptionalOuterDisplacements.HS.Witnesses
open Sporadic.LeechRelated.HS Outer
set_option maxRecDepth 10000

@[expose] def actor (i : Fin 2) : PermutationNormalizer :=
  if i = 0 then elementaryNormalizer else symmetricNormalizer

-- The packed tables are already proved equal to the defining generators.
private def a : Carrier :=
  ⟨OrderCertificate.p0, by rw [OrderCertificate.a_eq_generator]; exact generatorAElement.property⟩
private def b : Carrier :=
  ⟨OrderCertificate.p1, by rw [OrderCertificate.b_eq_generator]; exact generatorBElement.property⟩

def witness (i : Fin 2) : Carrier :=
  if i = 0 then b⁻¹ * b⁻¹ * a * b * a * b * b
  else a * b⁻¹ * a * b * b * a

@[expose] def displacement (i : Fin 2) : Carrier :=
  witness i * (generated.normalizerMonoidHom (actor i) (witness i))⁻¹

private theorem square_check : ∀ i : Fin 2, ∀ p : Fin 100,
    inclusion (displacement i) (inclusion (displacement i) p) = p := by
  apply OrderCertificate.allFin
  decide +kernel

/-- Both explicit displacements have no fixed points on the actual 100 letters. -/
theorem fixed_point_free : ∀ i : Fin 2, ∀ p : Fin 100,
    inclusion (displacement i) p ≠ p := by
  apply OrderCertificate.allFin
  decide +kernel

/-- Both explicit displacements are involutions in HS. -/
theorem displacement_order (i : Fin 2) : orderOf (displacement i) = 2 := by
  apply orderOf_eq_prime
  · apply inclusion_injective
    exact Equiv.ext (square_check i)
  · intro h
    exact fixed_point_free i 0 (congrArg (fun x : Carrier => inclusion x 0) h)

end Theory.SpecificGroups.ExceptionalOuterDisplacements.HS.Witnesses
