module

public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearClassification.NonbinaryPolar.Collineation.Incidence

/-!
# Determining a projective collineation from coordinate lines

A collineation fixing the coordinate axes and acting on every coordinate line
by a field automorphism acts by that automorphism on all projective points.

The span of `eᵢ + t eⱼ` and the axes outside `{i,j}` is exactly the hyperplane
`xⱼ = t xᵢ`. We prove this identity by subtracting the appropriate multiple of
`eᵢ + t eⱼ` and expanding the remainder in the standard basis. Subspace
transport then recovers every image coordinate ratio. For a nonzero coordinate
`vᵢ`, these ratios exhibit an image representative as a scalar multiple of the
coordinatewise field transform of `v`.

This is the determination step of projective coordinatization. The field
automorphism and its coordinate-line action are inputs from the separate
arithmetic step. Source context: the geometric automorphism ingredient used
in Aschbacher--Smith F.1.12, printed pp.263--264 of `refs/quasithin.pdf`.
-/

public noncomputable section
open Projectivization Module
namespace Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearClassification.Collineation
variable {F : Type*} [Field F]

private def coordinateHyperplane (i j : Index) (t : F) : Submodule F (Vector F) where
  carrier := {v | v j = t * v i}
  zero_mem' := by simp
  add_mem' := by
    intro v w hv hw
    change v j + w j = t * (v i + w i)
    rw [hv, hw, mul_add]
  smul_mem' := by
    intro c v hv
    change c * v j = t * (c * v i)
    rw [hv]
    ring

private theorem mem_remaining_axes (i j : Index) (v : Vector F)
    (hi : v i = 0) (hj : v j = 0) :
    v ∈ ⨆ (k : Index) (_ : k ≠ i) (_ : k ≠ j), (axis (F := F) k).submodule := by
  rw [pi_eq_sum_univ' v]
  apply Submodule.sum_mem
  intro k _
  by_cases hki : k = i
  · subst k
    simp [hi]
  by_cases hkj : k = j
  · subst k
    simp [hj]
  apply Submodule.smul_mem
  have hle : (axis (F := F) k).submodule ≤
      ⨆ (l : Index) (_ : l ≠ i) (_ : l ≠ j), (axis (F := F) l).submodule :=
    le_iSup_of_le k (le_iSup_of_le hki (le_iSup_of_le hkj le_rfl))
  exact hle (Submodule.mem_span_singleton_self _)

private theorem coordinateHyperplane_eq_span (i j : Index) (hij : i ≠ j) (t : F) :
    coordinateHyperplane i j t = (pairPoint i j hij t).submodule ⊔
      ⨆ (k : Index) (_ : k ≠ i) (_ : k ≠ j), (axis (F := F) k).submodule := by
  apply le_antisymm
  · intro v hv
    let u : Vector F := Pi.single i 1 + t • Pi.single j 1
    have hui : u i = 1 := by simp [u, hij]
    have huj : u j = t := by simp [u, hij.symm]
    have hi : (v - v i • u) i = 0 := by simp [hui]
    have hj : (v - v i • u) j = 0 := by
      change v j - v i * u j = 0
      change v j = t * v i at hv
      rw [huj, hv, mul_comm t, sub_self]
    have hrem := mem_remaining_axes i j (v - v i • u) hi hj
    have hu : u ∈ (pairPoint i j hij t).submodule :=
      Submodule.mem_span_singleton_self _
    have hadd := Submodule.add_mem
      ((pairPoint i j hij t).submodule ⊔
        ⨆ (k : Index) (_ : k ≠ i) (_ : k ≠ j), (axis (F := F) k).submodule)
      (Submodule.mem_sup_left (Submodule.smul_mem _ (v i) hu))
      (Submodule.mem_sup_right hrem)
    simpa only [add_sub_cancel] using hadd
  · refine sup_le ?_ (iSup_le fun k => iSup_le fun hki => iSup_le fun hkj => ?_)
    · rw [pairPoint, submodule_mk, Submodule.span_singleton_le_iff_mem]
      change (Pi.single i 1 + t • Pi.single j 1 : Vector F) j =
        t * (Pi.single i 1 + t • Pi.single j 1 : Vector F) i
      simp [hij, hij.symm]
    · rw [axis_submodule, Submodule.span_singleton_le_iff_mem]
      change (Pi.single k 1 : Vector F) j = t * (Pi.single k 1 : Vector F) i
      simp [hki.symm, hkj.symm]

private theorem map_coordinateHyperplane (ψ : Equiv.Perm (ProjectivePoint F))
    (hψ : PreservesLines ψ) (haxes : ∀ i : Index, ψ (axis i) = axis i)
    (σ : F ≃+* F)
    (hpairs : ∀ (i j : Index) (hij : i ≠ j) (t : F),
      ψ (pairPoint i j hij t) = pairPoint i j hij (σ t))
    (i j : Index) (hij : i ≠ j) (t : F) :
    submoduleOrderIso ψ hψ (coordinateHyperplane i j t) =
      coordinateHyperplane i j (σ t) := by
  rw [coordinateHyperplane_eq_span i j hij t,
    coordinateHyperplane_eq_span i j hij (σ t)]
  simp only [OrderIso.map_sup, OrderIso.map_iSup, submoduleOrderIso_point, hpairs, haxes]

/-- A line-preserving projective permutation is determined by its action on the
coordinate axes and coordinate lines. The field automorphism and the formulas
on those lines are explicit inputs. -/
theorem eq_fieldProjective_of_coordinate_lines (ψ : Equiv.Perm (ProjectivePoint F))
    (hψ : PreservesLines ψ) (haxes : ∀ i : Index, ψ (axis i) = axis i)
    (σ : F ≃+* F)
    (hpairs : ∀ (i j : Index) (hij : i ≠ j) (t : F),
      ψ (pairPoint i j hij t) = pairPoint i j hij (σ t))
    (p : ProjectivePoint F) : ψ p = fieldProjective σ p := by
  induction p using Projectivization.ind with
  | h v hv =>
    obtain ⟨i, hi⟩ : ∃ i : Index, v i ≠ 0 := by
      by_contra! h
      exact hv (funext h)
    let q := ψ (mk F v hv)
    have hcoord (j : Index) (hij : i ≠ j) :
        q.rep j = σ (v j / v i) * q.rep i := by
      have hvH : (mk F v hv).submodule ≤ coordinateHyperplane i j (v j / v i) := by
        rw [submodule_mk, Submodule.span_singleton_le_iff_mem]
        exact (div_mul_cancel₀ (v j) hi).symm
      have hqH := (submoduleOrderIso ψ hψ).monotone hvH
      rw [submoduleOrderIso_point,
        map_coordinateHyperplane ψ hψ haxes σ hpairs i j hij] at hqH
      have hmem : q.rep ∈ coordinateHyperplane i j (σ (v j / v i)) := by
        simpa only [submodule_eq, Submodule.span_singleton_le_iff_mem] using hqH
      exact hmem
    change q = fieldProjective σ (mk F v hv)
    rw [← q.mk_rep, fieldProjective_mk]
    apply (mk_eq_mk_iff' F _ _ _ _).mpr
    refine ⟨q.rep i / σ (v i), ?_⟩
    ext j
    change (q.rep i / σ (v i)) * σ (v j) = q.rep j
    by_cases hji : j = i
    · subst j
      exact div_mul_cancel₀ _ ((map_ne_zero σ).mpr hi)
    · rw [hcoord j (Ne.symm hji), map_div₀]
      ring

end Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearClassification.Collineation
