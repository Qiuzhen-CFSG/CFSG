module

public import Theory.SpecificGroups.OrthogonalFourBinary.TerminalLines.Rotations

/-!
# Products of residuals of intersecting singular lines

A totally singular subgroup of order four projects isomorphically onto each
of the two definite planes. It is therefore the graph of one of their six
linear isomorphisms. For distinct graphs with a common nonzero vector, a
kernel-checked calculation factors every pair of plane rotations into one
stabilizing each graph. Each stabilizer in the rotation group has exponent
three, so it equals its own two-residual. Thus the two line residuals have
the literal set product equal to the full orthogonal two-residual.

The actors remain linear isometries of the existing quadratic form throughout.
Source: Aschbacher–Smith, combined manuscript (1 March 2004), the orthogonal
space on printed pp.1121–1122 and the construction before 15.3.68 on p.1154.
-/

@[expose] public section

set_option synthInstance.maxSize 10000
open Subgroup Theory.AlgebraicGroup
open scoped Pointwise
namespace OrthogonalFourBinary.TerminalLines

abbrev LineCode := Fin 3 × Fin 2

def planePermutation (i : LineCode) : Plane ≃ₗ[F] Plane :=
  planeRotation ^ (i.1 : ℕ) * (LinearEquiv.prodComm F F F) ^ (i.2 : ℕ)

def graphLine (i : LineCode) : Subgroup (Multiplicative Space) where
  carrier w := w.toAdd.2 = planePermutation i w.toAdd.1
  one_mem' := (map_zero _).symm
  mul_mem' := by
    intro u v hu hv
    change u.toAdd.2 + v.toAdd.2 = planePermutation i (u.toAdd.1 + v.toAdd.1)
    rw [map_add, ← hu, ← hv]
  inv_mem' := by
    intro w hw
    change -w.toAdd.2 = planePermutation i (-w.toAdd.1)
    rw [map_neg, hw]

private def projection (E : Subgroup (Multiplicative Space)) (b : Bool) :
    E →* Multiplicative Plane where
  toFun w := Multiplicative.ofAdd (if b then w.val.toAdd.1 else w.val.toAdd.2)
  map_one' := by cases b <;> rfl
  map_mul' := by intro u v; cases b <;> rfl

private theorem projection_bijective (E : Subgroup (Multiplicative Space))
    (hcard : Nat.card E = 4) (hs : ∀ w ∈ E, form w.toAdd = 0) (b : Bool) :
    Function.Bijective (projection E b) := by
  apply (Nat.bijective_iff_injective_and_card _).mpr
  refine ⟨?_, ?_⟩
  · apply (injective_iff_map_eq_one _).mpr
    intro w hw
    by_contra hn
    have hne : w.val.toAdd ≠ 0 := fun h => hn (Subtype.ext h)
    have hh := singular_components w.val.toAdd hne (hs w w.property)
    cases b
    · exact hh.2 hw
    · exact hh.1 hw
  · rw [hcard]
    symm
    rw [Nat.card_eq_fintype_card]
    decide +kernel

private def u : Multiplicative Plane := Multiplicative.ofAdd (1,0)
private def v : Multiplicative Plane := Multiplicative.ofAdd (0,1)

private theorem plane_equiv_exhaustive (e : Multiplicative Plane ≃* Multiplicative Plane) :
    ∃ i : LineCode, ∀ w : Multiplicative Plane, (e w).toAdd = planePermutation i w.toAdd := by
  have hc : ∀ a b : Plane, a ≠ 0 → b ≠ 0 → a ≠ b →
      ∃ i : LineCode, a = planePermutation i (1,0) ∧ b = planePermutation i (0,1) := by
    decide +kernel
  obtain ⟨i,hu,hv⟩ := hc (e u).toAdd (e v).toAdd
    (by
      change e u ≠ 1
      intro h
      exact (show u ≠ 1 by decide +kernel) (e.injective (h.trans (map_one e).symm)))
    (by
      change e v ≠ 1
      intro h
      exact (show v ≠ 1 by decide +kernel) (e.injective (h.trans (map_one e).symm)))
    (fun h => (show u ≠ v by decide +kernel) (e.injective h))
  refine ⟨i, ?_⟩
  intro w
  have hw : ∀ w : Multiplicative Plane, w = 1 ∨ w = u ∨ w = v ∨ w = u*v := by
    decide +kernel
  rcases hw w with rfl | rfl | rfl | rfl
  · simp only [map_one]
    exact (map_zero _).symm
  · exact hu
  · exact hv
  · change (e (u*v)).toAdd = planePermutation i (u.toAdd + v.toAdd)
    rw [map_mul, map_add]
    exact congrArg₂ (· + ·) hu hv

/-- Every totally singular four-subgroup is the graph of one of six plane maps. -/
theorem singular_four_eq_graph (E : Subgroup (Multiplicative Space))
    (hcard : Nat.card E = 4) (hs : ∀ w ∈ E, form w.toAdd = 0) :
    ∃ i : LineCode, E = graphLine i := by
  let e₁ := MulEquiv.ofBijective (projection E true) (projection_bijective E hcard hs true)
  let e₂ := MulEquiv.ofBijective (projection E false) (projection_bijective E hcard hs false)
  let e := e₁.symm.trans e₂
  obtain ⟨i,hi⟩ := plane_equiv_exhaustive e
  refine ⟨i, ?_⟩
  ext w
  constructor
  · intro hw
    have hh := hi (e₁ ⟨w,hw⟩)
    change (e₂ (e₁.symm (e₁ ⟨w,hw⟩))).toAdd = _ at hh
    rw [e₁.symm_apply_apply] at hh
    exact hh
  · intro hw
    let a : E := e₁.symm (Multiplicative.ofAdd w.toAdd.1)
    have ha : e₁ a = Multiplicative.ofAdd w.toAdd.1 := e₁.apply_symm_apply _
    have hb := hi (Multiplicative.ofAdd w.toAdd.1)
    have he : (a : Multiplicative Space) = w := by
      apply Prod.ext
      · exact ha
      · exact hb.trans hw.symm
    exact he ▸ a.property

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem finite_product : ∀ i j : LineCode, i ≠ j →
    (∃ w : Space, w ≠ 0 ∧ w.2 = planePermutation i w.1 ∧ w.2 = planePermutation j w.1) →
    ∀ k : RotationCode, ∃ a b : RotationCode,
      (∀ w : Space, rotation k w = rotation a (rotation b w)) ∧
      (∀ w : Space, (rotation a w).2 = planePermutation i (rotation a w).1 ↔
        w.2 = planePermutation i w.1) ∧
      (∀ w : Space, (rotation b w).2 = planePermutation j (rotation b w).1 ↔
        w.2 = planePermutation j w.1) := by decide +kernel

/-- Stabilizers in the rotation group already have odd exponent, hence are two-perfect. -/
theorem lineResidual_eq_rotations_inter (E : Subgroup (Multiplicative Space)) :
    lineResidual E = rotations ⊓ lineStabilizer E := by
  unfold lineResidual
  rw [residual_eq_rotations]
  have hr : pResidual 2 ↥(rotations ⊓ lineStabilizer E) = ⊤ := by
    apply top_unique
    intro g _
    apply mem_pResidual_of_orderOf_coprime
    have hg : g ^ 3 = 1 := by
      apply Subtype.ext
      obtain ⟨i,hi⟩ := g.property.1
      change g.val ^ 3 = 1
      rw [← hi]
      exact rotation_cube i
    exact Nat.Coprime.of_dvd_right (orderOf_dvd_of_pow_eq_one hg)
      (by decide : Nat.Coprime 2 3)
  rw [hr, ← MonoidHom.range_eq_map, range_subtype]

/-- The two line residuals for intersecting distinct singular lines multiply to O². -/
theorem residual_line_product (E F : Subgroup (Multiplicative Space))
    (hEcard : Nat.card E = 4) (hFcard : Nat.card F = 4)
    (hE : ∀ w ∈ E, form w.toAdd = 0) (hF : ∀ w ∈ F, form w.toAdd = 0)
    (hne : E ≠ F) (hcommon : ∃ w, w ≠ 1 ∧ w ∈ E ∧ w ∈ F) :
    (pResidual 2 IsometryGroup : Set IsometryGroup) =
      (lineResidual E : Set IsometryGroup) * (lineResidual F : Set IsometryGroup) := by
  obtain ⟨i,rfl⟩ := singular_four_eq_graph E hEcard hE
  obtain ⟨j,rfl⟩ := singular_four_eq_graph F hFcard hF
  have hij : i ≠ j := fun h => hne (h ▸ rfl)
  obtain ⟨w,hw,hwi,hwj⟩ := hcommon
  have hc : ∃ w : Space, w ≠ 0 ∧ w.2 = planePermutation i w.1 ∧
      w.2 = planePermutation j w.1 := ⟨w.toAdd,hw,hwi,hwj⟩
  rw [residual_eq_rotations, lineResidual_eq_rotations_inter, lineResidual_eq_rotations_inter]
  apply Set.Subset.antisymm
  · rintro g ⟨k,rfl⟩
    obtain ⟨a,b,hab,ha,hb⟩ := finite_product i j hij hc k
    refine ⟨rotationHom a, ⟨⟨a,rfl⟩,ha⟩, rotationHom b, ⟨⟨b,rfl⟩,hb⟩, ?_⟩
    exact (Subtype.ext (LinearEquiv.ext hab)).symm
  · rintro g ⟨a,ha,b,hb,rfl⟩
    exact rotations.mul_mem ha.1 hb.1

end OrthogonalFourBinary.TerminalLines
