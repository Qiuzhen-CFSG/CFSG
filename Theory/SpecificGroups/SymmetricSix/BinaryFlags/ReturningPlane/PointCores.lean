module

public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.CoreGeometry
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.SylowGeometry

/-!
# Disjoint point cores for the returning syntheme rotation

The even two-core of the canonical duad stabilizer consists of the
identity and three double transpositions on its complementary four letters.
Rotating the three duads of the canonical syntheme gives another point
core with trivial intersection. A four-by-four kernel-checked calculation
proves the assertion; conjugation transports it to every marked flag.

Source: Aschbacher–Smith,13.5.16, printed p.921, using the natural A₆
configuration of13.2.1–2 and13.3.3.
-/

@[expose] public section
open Subgroup
namespace Theory.SpecificGroups.SymmetricSix.BinaryFlags.ReturningPlane

private abbrev a : S := swap01 * swap23
private abbrev b : S := Equiv.swap 0 2 * Equiv.swap 1 3
private def eight : List S := [1,a,b,a*b,swap45,swap45*a,swap45*b,swap45*(a*b)]
private def four : List S := [1,a,b,a*b]

private theorem eight_closed : ∀ x ∈ eight, ∀ y ∈ eight, x*y ∈ eight := by
  have h : eight.all (fun x => eight.all (fun y => decide (x*y ∈ eight))) = true := by
    decide +kernel
  simpa only [List.all_eq_true, decide_eq_true_eq] using h
private theorem eight_inverses : ∀ x ∈ eight, x⁻¹ ∈ eight := by
  have h : eight.all (fun x => decide (x⁻¹ ∈ eight)) = true := by decide +kernel
  simpa only [List.all_eq_true, decide_eq_true_eq] using h

private def certificate : Subgroup S where
  carrier := {x | x ∈ eight}
  one_mem' := by decide +kernel
  mul_mem' := fun hx hy => eight_closed _ hx _ hy
  inv_mem' := eight_inverses _

private theorem core_in_certificate : pointCore ≤ certificate := by
  rw [pointCore_eq_closure, closure_le]
  intro x hx
  rcases hx with rfl | rfl | rfl <;> change _ ∈ eight <;> decide +kernel

private theorem even_in_four {x : S} (hx : x ∈ pointCoreEven) : x ∈ four := by
  have h := core_in_certificate hx.1
  change x ∈ eight at h
  have he : Equiv.Perm.sign x = 1 := hx.2
  have hc : eight.all (fun x => decide (Equiv.Perm.sign x = 1 → x ∈ four)) = true := by
    decide +kernel
  have hh : ∀ x ∈ eight, Equiv.Perm.sign x = 1 → x ∈ four := by
    simpa only [List.all_eq_true, decide_eq_true_eq] using hc
  exact hh x h he

/-- The two actual even point cores have no common nonidentity element. -/
theorem pointCore_intersection :
    pointCoreEven ⊓ pointCoreEven.map (MulAut.conj pairRotation).toMonoidHom = ⊥ := by
  apply eq_bot_iff.mpr
  rintro x ⟨hx,y,hy,he⟩
  have cert : four.all (fun x => four.all (fun y =>
      decide (x = pairRotation*y*pairRotation⁻¹ → x=1))) = true := by decide +kernel
  have hc : ∀ x ∈ four, ∀ y ∈ four,
      x = pairRotation*y*pairRotation⁻¹ → x=1 := by
    simpa only [List.all_eq_true, decide_eq_true_eq] using cert
  exact hc x (even_in_four hx) y (even_in_four hy) he.symm

/-- The rotation is in the actual even syntheme stabilizer. -/
theorem rotation_even : pairRotation ∈ alternatingGroup (Fin 6) := by decide +kernel

theorem rotation_plane : pairRotation ∈ H2 := pairRotation_mem_H2

/-- The point moves while the syntheme plane is preserved. -/
theorem rotation_not_point : pairRotation ∉ H1 := by decide +kernel

/-- The same two literal cores are disjoint after any simultaneous flag marking. -/
theorem marked_pointCore_intersection (s : S) :
    pointCoreEven.map (MulAut.conj s).toMonoidHom ⊓
      pointCoreEven.map (MulAut.conj (s*pairRotation)).toMonoidHom = ⊥ := by
  have hmap : pointCoreEven.map (MulAut.conj (s*pairRotation)).toMonoidHom =
      (pointCoreEven.map (MulAut.conj pairRotation).toMonoidHom).map
        (MulAut.conj s).toMonoidHom := by
    rw [map_map]
    congr 1
  rw [hmap, ← map_inf _ _ _ (MulAut.conj s).injective, pointCore_intersection, Subgroup.map_bot]

end Theory.SpecificGroups.SymmetricSix.BinaryFlags.ReturningPlane
end
