module

public import Theory.Combinatorics.ProjectivePlaneThreeAction

/-!
# Rigidity of the coordinate frame in PG(2,3)

A collineation fixing the three coordinate points and `[1,1,1]` is the identity.
The six joins of these four points are fixed. Their opposite intersections give
`[1,1,0]`, `[1,0,1]`, and `[0,1,1]`. The three joins between these diagonal points,
intersected with the original six lines, then give the remaining six points.

We list thirteen normalized representatives and check their separation by scalars
by kernel reduction over the finite field. The projectivization cardinality
formula proves this list exhaustive. Thus the geometric construction fixes every
point, and the point action determines the collineation.

This is the elementary frame argument for the order-three plane used toward
Wong, *On finite groups whose 2-Sylow subgroups have cyclic subgroups of index 2*,
Theorem 6(b), printed p. 111, as in `ProjectivePlaneThreeAction`.
-/

namespace Configuration.PlaneThree

/-- Coordinate points, diagonal points, the all-ones point, and the six remaining points. -/
private def representativeVector : Fin 13 → Fin 3 → ZMod 3 :=
  ![![1, 0, 0], ![0, 1, 0], ![0, 0, 1], ![1, 1, 0], ![1, 0, 1], ![0, 1, 1],
    ![1, 1, 1], ![1, 1, 2], ![1, 2, 1], ![1, 2, 2], ![1, 0, 2], ![1, 2, 0], ![0, 1, 2]]

private theorem representativeVector_ne_zero (i : Fin 13) : representativeVector i ≠ 0 := by
  fin_cases i <;> decide

private def representative (i : Fin 13) : PG :=
  Projectivization.mk _ (representativeVector i) (representativeVector_ne_zero i)

private theorem representativeVector_separation : ∀ (i j : Fin 13) (a : ZMod 3),
    a • representativeVector j = representativeVector i → i = j := by
  intro i j
  fin_cases i <;> fin_cases j <;> decide +kernel

private theorem representative_injective : Function.Injective representative := by
  intro i j h
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff _ _ _ _ _).mp h
  exact representativeVector_separation i j a ha

/-- The thirteen scalar-distinct representatives exhaust PG(2,3). -/
private theorem representative_surjective : Function.Surjective representative := by
  have hc : Nat.card PG = 13 := by
    rw [Projectivization.card'']
    norm_num [Nat.card_fun, Nat.card_eq_fintype_card]
  exact ((Nat.bijective_iff_injective_and_card representative).mpr
    ⟨representative_injective, by simpa using hc.symm⟩).2

private theorem representative_incidence (i j : Fin 13) :
    representative i ∈ representative j ↔ representativeVector i ⬝ᵥ representativeVector j = 0 :=
  Projectivization.orthogonal_mk _ _

private theorem fixed_line (c : FullCollineation) (i j k : Fin 13)
    (hij : i ≠ j) (hik : representativeVector i ⬝ᵥ representativeVector k = 0)
    (hjk : representativeVector j ⬝ᵥ representativeVector k = 0)
    (hi : Collineation.pointHom PG PG c (representative i) = representative i)
    (hj : Collineation.pointHom PG PG c (representative j) = representative j) :
    Collineation.lineHom PG PG c (representative k) = representative k := by
  have hik' := (Collineation.mem_iff c (representative i) (representative k)).mpr
    ((representative_incidence i k).mpr hik)
  have hjk' := (Collineation.mem_iff c (representative j) (representative k)).mpr
    ((representative_incidence j k).mpr hjk)
  rw [hi] at hik'
  rw [hj] at hjk'
  exact (Nondegenerate.eq_or_eq hik' hjk' ((representative_incidence i k).mpr hik)
    ((representative_incidence j k).mpr hjk)).resolve_left (fun he => hij (representative_injective he))

private theorem fixed_point (c : FullCollineation) (i j k : Fin 13)
    (hjk : j ≠ k) (hij : representativeVector i ⬝ᵥ representativeVector j = 0)
    (hik : representativeVector i ⬝ᵥ representativeVector k = 0)
    (hj : Collineation.lineHom PG PG c (representative j) = representative j)
    (hk : Collineation.lineHom PG PG c (representative k) = representative k) :
    Collineation.pointHom PG PG c (representative i) = representative i := by
  have hij' := (Collineation.mem_iff c (representative i) (representative j)).mpr
    ((representative_incidence i j).mpr hij)
  have hik' := (Collineation.mem_iff c (representative i) (representative k)).mpr
    ((representative_incidence i k).mpr hik)
  rw [hj] at hij'
  rw [hk] at hik'
  exact (Nondegenerate.eq_or_eq hij' ((representative_incidence i j).mpr hij)
    hik' ((representative_incidence i k).mpr hik)).resolve_right
      (fun he => hjk (representative_injective he))

/-- A collineation of PG(2,3) fixing the standard ordered frame is the identity. -/
public theorem frame_fixed_eq_one (c : FullCollineation)
    (h : ∀ i : Fin 4, Collineation.pointHom PG PG c (frame i) = frame i) : c = 1 := by
  have h0 : Collineation.pointHom PG PG c (representative 0) = representative 0 := h 0
  have h1 : Collineation.pointHom PG PG c (representative 1) = representative 1 := h 1
  have h2 : Collineation.pointHom PG PG c (representative 2) = representative 2 := h 2
  have h6 : Collineation.pointHom PG PG c (representative 6) = representative 6 := h 3
  -- The six joins of pairs of frame points are fixed.
  have l2 := fixed_line c 0 1 2 (by decide) (by decide) (by decide) h0 h1
  have l1 := fixed_line c 0 2 1 (by decide) (by decide) (by decide) h0 h2
  have l0 := fixed_line c 1 2 0 (by decide) (by decide) (by decide) h1 h2
  have l12 := fixed_line c 0 6 12 (by decide) (by decide) (by decide) h0 h6
  have l10 := fixed_line c 1 6 10 (by decide) (by decide) (by decide) h1 h6
  have l11 := fixed_line c 2 6 11 (by decide) (by decide) (by decide) h2 h6
  -- The three opposite intersections are the diagonal points.
  have h3 := fixed_point c 3 2 11 (by decide) (by decide) (by decide) l2 l11
  have h4 := fixed_point c 4 1 10 (by decide) (by decide) (by decide) l1 l10
  have h5 := fixed_point c 5 0 12 (by decide) (by decide) (by decide) l0 l12
  -- Join the diagonal points, then intersect to obtain the last six points.
  have l9 := fixed_line c 3 4 9 (by decide) (by decide) (by decide) h3 h4
  have l8 := fixed_line c 3 5 8 (by decide) (by decide) (by decide) h3 h5
  have l7 := fixed_line c 4 5 7 (by decide) (by decide) (by decide) h4 h5
  have h7 := fixed_point c 7 11 7 (by decide) (by decide) (by decide) l11 l7
  have h8 := fixed_point c 8 10 8 (by decide) (by decide) (by decide) l10 l8
  have h9 := fixed_point c 9 12 9 (by decide) (by decide) (by decide) l12 l9
  have h10 := fixed_point c 10 1 8 (by decide) (by decide) (by decide) l1 l8
  have h11 := fixed_point c 11 2 7 (by decide) (by decide) (by decide) l2 l7
  have h12 := fixed_point c 12 0 9 (by decide) (by decide) (by decide) l0 l9
  -- Exhaustiveness now reduces the claim to pointwise rigidity.
  apply Collineation.ext_points
  intro p
  obtain ⟨i, rfl⟩ := representative_surjective p
  change Collineation.pointHom PG PG c (representative i) = representative i
  fin_cases i <;> assumption

end Configuration.PlaneThree
