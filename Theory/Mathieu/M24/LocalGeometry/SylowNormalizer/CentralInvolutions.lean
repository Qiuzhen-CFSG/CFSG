module

public import Theory.Mathieu.M24.LocalGeometry.SylowNormalizer.Order
public import Theory.Mathieu.M24.LocalGeometry.Defs
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# The fixed octad of central involutions in the marked M₂₄ subgroup

Four pointwise commutation tests on the certified 1024-row enumeration
leave only the identity row and row 106. Every central involution is
therefore row 106. Its fixed points are exactly the native octad numbered
456, as checked on all 24 points. A commuting permutation preserves this
fixed-point set, so its centralizer lies in the octad stabilizer.

The finite certificates use the existing word tables and the Lean kernel.
The enumeration is transferred through its actual embedded elements and
generators in the Witt-design automorphism group. The subgroup's Sylow
property follows separately from its checked order and the order of M₂₄.

Source context: Aschbacher–Smith, Theorem 0.1.2(5) and condition E,
printed pp.3–4, repeated on pp.481–482; GLS3, Table 5.3e.
-/

namespace Sporadic.Mathieu.M24LocalGeometry.SylowNormalizer
open Subgroup OrderEnumeration

set_option maxRecDepth 100000 in
private theorem central_row_tests : ∀ i : Fin 1024,
    point i (generatorPoint 0 1) = generatorPoint 0 (point i 1) →
    point i (generatorPoint 1 5) = generatorPoint 1 (point i 5) →
    point i (generatorPoint 0 0) = generatorPoint 0 (point i 0) →
    point i (generatorPoint 3 1) = generatorPoint 3 (point i 1) →
    i = 0 ∨ i = 106 := by
  decide +kernel

/-- The center of the actual marked subgroup has only these two possible elements. -/
public theorem central_element_cases (z : candidate) (hz : z ∈ center candidate) :
    z = 1 ∨ z = element 106 := by
  obtain ⟨i, rfl⟩ := element_surjective z
  have hcomm (a : Fin 4) (x : Fin 24) :
      point i (generatorPoint a x) = generatorPoint a (point i x) := by
    have he := mem_center_iff.mp hz (markedGenerator a)
    have hp := congrArg (fun g : candidate => g.val.val x) he
    change generatorPerm a ((element i).val.val x) =
      (element i).val.val (generatorPerm a x) at hp
    simpa only [element_apply, generatorPerm_apply] using hp.symm
  rcases central_row_tests i (hcomm 0 1) (hcomm 1 5) (hcomm 0 0) (hcomm 3 1) with
    rfl | rfl
  · exact Or.inl element_identity
  · exact Or.inr rfl

/-- Order two excludes the identity row in the center calculation. -/
public theorem central_involution_eq_element106 (z : candidate)
    (hz : z ∈ center candidate) (hz2 : orderOf z = 2) : z = element 106 := by
  rcases central_element_cases z hz with rfl | he
  · simp only [orderOf_one] at hz2
    omega
  · exact he

/-- The octad fixed pointwise by a central involution of the marked subgroup. -/
public noncomputable def centralOctad : Octad := ⟨m24BlockAt 456, by
  exact Finset.mem_image.mpr ⟨456, Finset.mem_univ _, rfl⟩⟩

set_option maxRecDepth 100000 in
private theorem row106_fixed_iff : ∀ x : Fin 24,
    point 106 x = x ↔ x ∈ m24BlockAt 456 := by
  decide +kernel

/-- All 24 fixed-point comparisons identify the fixed set with an actual Witt octad. -/
public theorem central_involution_fixed_iff (z : candidate)
    (hz : z ∈ center candidate) (hz2 : orderOf z = 2) (x : Fin 24) :
    z.val.val x = x ↔ x ∈ centralOctad.val := by
  rw [central_involution_eq_element106 z hz hz2, element_apply]
  exact row106_fixed_iff x

/-- Commutation preserves the fixed octad of every central involution. -/
public theorem central_involution_centralizer_le_octad (z : candidate)
    (hz : z ∈ center candidate) (hz2 : orderOf z = 2) :
    centralizer ({(z : M24)} : Set M24) ≤ octadStabilizer centralOctad := by
  intro g hg
  apply MulAction.mem_stabilizer_finset.mpr
  intro x
  rw [← central_involution_fixed_iff z hz hz2, ← central_involution_fixed_iff z hz hz2]
  change z.val.val (g.val x) = g.val x ↔ z.val.val x = x
  have hc := congrArg (fun u : M24 => u.val x)
    (mem_centralizer_singleton_iff.mp hg)
  change g.val (z.val.val x) = z.val.val (g.val x) at hc
  rw [← hc]
  exact g.val.injective.eq_iff

end Sporadic.Mathieu.M24LocalGeometry.SylowNormalizer
